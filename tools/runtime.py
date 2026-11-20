#!/usr/bin/env python3
"""Build the local Goose reference against pinned, external comparison tools."""
from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tomllib
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
CONFIG = ROOT / "conformance/dependencies.json"
PROVENANCE = ROOT / "conformance/source-provenance.json"
GOOSE_FLAGS = ["-O2", "-DGS_DEBUG=1", "--standalone"]
C_FLAGS = ["-O2", "-lm", "-pthread"]
REPLACEMENTS = [
    {"from": '0 => "accepted"', "to": '0 => "observed_success"'},
    {"from": '\\"accepted\\":', "to": '\\"success_observations\\":'},
    {"from": 'format(output, "{\\"engine\\":\\"goose-aot\\",\\"status\\":\\"checked\\",',
     "to": 'format(output, "{\\"schema\\":\\"lean-goose.definition-observations.v1\\",\\"engine\\":\\"goose-aot\\",\\"status\\":\\"checked\\",'},
    {"from": 'print("{\\"engine\\":\\"goose-aot\\",\\"status\\":\\"passed\\",',
     "to": 'print("{\\"schema\\":\\"lean-goose.benchmark-observation.v1\\",\\"engine\\":\\"goose-aot\\",\\"status\\":\\"passed\\",'},
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(args: list[str], cwd: Path = ROOT, timeout: int = 300) -> str:
    result = subprocess.run(args, cwd=cwd, text=True, capture_output=True, timeout=timeout)
    if result.returncode:
        # Raw observer stdout is intentionally not re-emitted as a local verdict.
        raise RuntimeError(f"command exited {result.returncode}: {args!r}\n{result.stderr}")
    return result.stdout.strip()


def executable(variable: str, default: str) -> Path:
    name = os.environ.get(variable, default)
    found = shutil.which(name)
    if found is None:
        raise RuntimeError(f"missing executable {name}; set {variable}")
    return Path(found).absolute()


def relative(path: str) -> Path:
    value = PurePosixPath(path)
    if value.is_absolute() or ".." in value.parts:
        raise RuntimeError("dependency path must remain inside its checkout")
    return Path(value)


def archive_sha256(checkout: Path, revision: str) -> str:
    process = subprocess.Popen(["git", "archive", "--format=tar", revision],
                               cwd=checkout, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    digest = hashlib.sha256()
    assert process.stdout is not None
    while chunk := process.stdout.read(1024 * 1024):
        digest.update(chunk)
    _, error = process.communicate(timeout=300)
    if process.returncode:
        raise RuntimeError(f"cannot hash dependency archive: {error.decode(errors='replace')}")
    return digest.hexdigest()


def verify_checkout(path: Path, pin: dict[str, Any]) -> dict[str, Any]:
    if command(["git", "rev-parse", "HEAD"], cwd=path) != pin["revision"]:
        raise RuntimeError(f"dependency revision differs from pin: {path}")
    if command(["git", "status", "--porcelain", "--untracked-files=no"], cwd=path):
        raise RuntimeError(f"dependency has tracked changes: {path}")
    archive_hash = archive_sha256(path, pin["revision"])
    if archive_hash != pin["archive_sha256"] or pin["pin"] != "sha256:" + archive_hash:
        raise RuntimeError(f"dependency archive differs from content pin: {path}")
    for item in pin.get("consumed_files", []):
        file = path / relative(item["path"])
        if file.is_symlink() or not file.is_file() or file.stat().st_size != item["bytes"] \
                or sha256(file) != item["sha256"]:
            raise RuntimeError(f"dependency file differs from content pin: {item['path']}")
    return {"repository": pin["repository"], "revision": pin["revision"],
            "archive_sha256": archive_hash, "checkout": str(path), "tracked_source_clean": True,
            "verified_consumed_files": pin.get("consumed_files", [])}


def verify_derivation(baseline: Path) -> dict[str, Any]:
    provenance = json.loads(PROVENANCE.read_text())
    if provenance.get("acceptance_authority") is not False or provenance.get("replacements") != REPLACEMENTS:
        raise RuntimeError("source provenance does not match the observation-only port contract")
    config = json.loads(CONFIG.read_text())
    if provenance["source_revision"] != config["lean_ocaml"]["revision"]:
        raise RuntimeError("source provenance revision differs from comparison pin")
    source_path = relative(provenance["source_path"])
    source = baseline / source_path
    local = ROOT / relative(provenance["local_path"])
    if source.is_symlink() or local.is_symlink():
        raise RuntimeError("checker source symlinks are outside the provenance contract")
    blob = command(["git", "rev-parse", provenance["source_revision"] + ":" + str(source_path)], cwd=baseline)
    if blob != provenance["source_git_blob"] or sha256(source) != provenance["source_sha256"]:
        raise RuntimeError("upstream checker source differs from provenance")
    transformed = source.read_text()
    for replacement in REPLACEMENTS:
        if transformed.count(replacement["from"]) != 1:
            raise RuntimeError("source presentation replacement is not unique")
        transformed = transformed.replace(replacement["from"], replacement["to"])
    if transformed.encode() != local.read_bytes() or sha256(local) != provenance["local_sha256"]:
        raise RuntimeError("local checker derivative differs from its recorded source transform")
    return {"source_revision": provenance["source_revision"], "source_git_blob": blob,
            "source_sha256": provenance["source_sha256"], "local_path": provenance["local_path"],
            "local_sha256": provenance["local_sha256"], "presentation_changes_only": True}


def prepare(build: Path) -> dict[str, Any]:
    config = json.loads(CONFIG.read_text())
    if config.get("schema") != "lean-goose.dependencies.v1" or config.get("acceptance_authority") is not False:
        raise RuntimeError("unknown dependency schema or authority model")
    if config["goose"]["goose_flags"] != GOOSE_FLAGS or config["goose"]["c_flags"] != C_FLAGS:
        raise RuntimeError("Goose compiler flags differ from the checked native lane")
    if os.environ.get("LEAN_OCAML_SOURCE"):
        baseline_path = Path(os.environ["LEAN_OCAML_SOURCE"]).expanduser().resolve()
    else:
        baseline_path = build / "external-lean-ocaml"
        command(["git", "clone", "--no-checkout", config["lean_ocaml"]["repository"], str(baseline_path)])
        command(["git", "checkout", "--detach", config["lean_ocaml"]["revision"]], cwd=baseline_path)
    if not os.environ.get("GOOSE_SOURCE"):
        raise RuntimeError("set GOOSE_SOURCE to the built pinned Goose checkout")
    goose_path = Path(os.environ["GOOSE_SOURCE"]).expanduser().resolve()
    context = {"config": config, "baseline_path": baseline_path, "goose_path": goose_path}
    context["dependency_observations"] = verify_dependencies(context)
    return context


def verify_dependencies(context: dict[str, Any]) -> dict[str, Any]:
    config = context["config"]
    return {
        "estate_dependencies": verify_estate_dependencies(config),
        "lean_ocaml": verify_checkout(context["baseline_path"], config["lean_ocaml"]),
        "goose": verify_checkout(context["goose_path"], config["goose"]),
        "local_derivation": verify_derivation(context["baseline_path"]),
    }


def verify_estate_dependencies(config: dict[str, Any], manifest: Path | None = None) -> list[dict[str, str]]:
    estate = tomllib.loads((manifest or ROOT / "ESTATE.toml").read_text())
    observed = []
    for identifier, key in (("lean-ocaml", "lean_ocaml"), ("goose", "goose")):
        entries = [entry for entry in estate.get("dep", []) if entry.get("id") == identifier]
        expected = {"id": identifier, "rev": config[key]["revision"], "pin": config[key]["pin"]}
        if len(entries) != 1 or any(entries[0].get(field) != value for field, value in expected.items()):
            raise RuntimeError(f"ESTATE dependency differs from runtime pin: {identifier}")
        observed.append(expected)
    return observed


def source_files() -> list[dict[str, Any]]:
    paths = ["ESTATE.toml", "reference/checker.goose", "tools/runtime.py", "tools/run.py",
             "conformance/dependencies.json", "conformance/source-provenance.json"]
    return [{"path": path, "sha256": sha256(ROOT / path), "bytes": (ROOT / path).stat().st_size}
            for path in sorted(paths)]


def load_support(context: dict[str, Any]) -> dict[str, Any]:
    # Execute verified source bytes rather than an unrelated/stale .pyc file.
    # Dependencies remain external and no supplied checkout is modified.
    modules = {}
    for name in ("optimization_workloads", "compare_lean", "goose_common", "test_goose"):
        path = context["baseline_path"] / "tools" / (name + ".py")
        spec = importlib.util.spec_from_file_location(name, path)
        assert spec is not None
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        exec(compile(path.read_bytes(), str(path), "exec"), module.__dict__)
        modules[name] = module
    return modules


def build_all(build: Path, context: dict[str, Any]) -> tuple[dict[str, Path], dict[str, Any], dict[str, Any]]:
    modules = load_support(context)
    baseline = modules["compare_lean"]
    baseline.BUILD = build
    config = context["config"]
    ocamlc = executable("OCAMLC", "ocamlc")
    lean = executable("LEAN", "lean")
    cc = executable("GOOSE_CC", "gcc")
    if command([str(ocamlc), "-version"]) != config["ocaml"]["version"]:
        raise RuntimeError("OCaml version differs from pin")
    lean_version = command([str(lean), "--version"])
    if f"version {config['lean']['version']}," not in lean_version or config["lean"]["revision"] not in lean_version:
        raise RuntimeError("Lean version or revision differs from pin")
    cc_version = command([str(cc), "--version"])
    if "gcc" not in cc_version.lower() and "free software foundation" not in cc_version.lower():
        raise RuntimeError("this native comparison requires GCC")
    goose = Path(os.environ.get("GOOSE", str(context["goose_path"] / "build/goose"))).resolve()
    if not goose.is_file() or not os.access(goose, os.X_OK):
        raise RuntimeError(f"missing Goose compiler: {goose}")
    print("Building local Goose reference and pinned external comparison drivers.", flush=True)
    ocaml_binary = baseline.build_ocaml(ocamlc)
    lean_binary = baseline.build_lean(lean)
    ocaml_folder = build / "bytecode"
    shutil.copyfile(context["baseline_path"] / "conformance/migration_check.ml", ocaml_folder / "migration_check.ml")
    ocaml_checker = ocaml_folder / "migration_check"
    command([str(ocamlc), "-o", str(ocaml_checker), "conversion.cmo", "migration_check.ml"], cwd=ocaml_folder)
    folder = build / "goose"
    folder.mkdir()
    generated = folder / "checker.c"
    goose_binary = folder / "checker"
    emit = [str(goose), *GOOSE_FLAGS, "-o", str(generated), str(ROOT / "reference/checker.goose")]
    command(emit)
    if "#define GS_DEBUG 1" not in generated.read_text():
        raise RuntimeError("emitted checker does not retain requested runtime checks")
    compile_command = [str(cc), C_FLAGS[0], str(generated), "-o", str(goose_binary), *C_FLAGS[1:]]
    command(compile_command)
    binaries = {"lean-kernel": lean_binary, "ocaml-bytecode": ocaml_binary,
                "ocaml-check": ocaml_checker, "goose-aot": goose_binary}
    metadata = {
        "ocaml_version": config["ocaml"]["version"], "ocaml_backend": "bytecode", "lean_version": lean_version,
        "goose_source_revision": config["goose"]["revision"], "goose_source_archive_sha256": config["goose"]["archive_sha256"],
        "goose_compiler": str(goose), "goose_compiler_sha256": sha256(goose),
        "generated_c_sha256": sha256(generated), "generated_c_bytes": generated.stat().st_size,
        "emit_command": emit, "compile_command": compile_command, "gcc_version": cc_version,
        "executables": [{"path": str(path), "sha256": sha256(path)} for path in (ocamlc, lean, lean.parent / "leanc", cc)],
        "binaries": [{"engine": engine, "sha256": sha256(binary)} for engine, binary in binaries.items()],
    }
    return binaries, metadata, modules
