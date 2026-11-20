#!/usr/bin/env python3
"""Execute the required Lean/Quint scopes and source-bound native comparisons."""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tomllib

import acceptance
import check_expression_dag as dag
import check_stored_bindings as stored
import check_substitution as substitution
import runtime
import transaction_profile as profile

ROOT = runtime.ROOT
LEAN_TOOLCHAIN = "leanprover/lean4:v4.34.1"
LEAN_COMMIT = "5045d0056413266e57c625dcd7c365b10e377c52"
LEAN_FLAGS = ["--threads=1"]
QUINT_TOOLCHAIN = "@informalsystems/quint@0.33.1"
NODE_VERSION = "v24.22.3"
SEED = "20261120"
LEAN_SOURCES = {"formal/lean/DefinitionTransactions.lean", "formal/lean/Audit.lean", "formal/lean/Replay.lean"} | stored.LEAN_SOURCES | dag.LEAN_SOURCES | substitution.LEAN_SOURCES
QUINT_SOURCES = {"formal/quint/DefinitionTransactions.qnt"} | stored.QUINT_SOURCES | dag.QUINT_SOURCES | substitution.QUINT_SOURCES
IMPLEMENTATIONS = {"reference/checker.goose", "tools/run.py", "tools/runtime.py", "tools/acceptance.py",
                   "tools/check_formal.py", "tools/transaction_profile.py", "formal/quint/replay.py"} | stored.IMPLEMENTATIONS | dag.IMPLEMENTATIONS | substitution.IMPLEMENTATIONS
LEAN_OBLIGATIONS = {"GooseTransactions." + name for name in (
    "initial_invariant", "step_preserves_invariant", "run_preserves_invariant",
    "run_environment_exact", "run_environment_unique", "run_success_count_exact",
    "halted_step_identity", "halted_run_identity", "halted_no_receipt",
    "duplicate_precedes_checks", "duplicate_preserves_environment", "mismatch_preserves_environment",
    "missing_alias_preserves_environment", "fresh_good_appends", "fresh_scope_halts",
    "mismatch_then_retry_succeeds", "step_preserves_authority", "run_preserves_authority",
    "run_has_no_authority", "completed_receipt_has_no_authority", "run_environment_extends",
)}
QUINT_TESTS = {
    "initialStateTest", "successfulDefinitionTest", "failedInsertionRetryTest",
    "duplicatePreservesEnvironmentTest", "duplicatePreemptsScopeTest", "unknownAliasRecoveryTest",
    "validAliasTest", "unknownAliasPreservesExistingTest", "scopeFailureSuppressesReceiptTest",
    "haltAbsorbingTest", "orderedSuccessCountTest", "authorityPreservedTest",
}


def save(path: Path, value: object) -> None:
    acceptance.write_json(path, value)


def owned(root: Path, name: str) -> Path:
    if not isinstance(name, str) or not name or "\\" in name or Path(name).is_absolute() \
            or any(part in ("", ".", "..") for part in name.split("/")):
        raise ValueError("formal input must be an owned repository-relative file")
    path = root / name
    if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"missing or escaping formal input: {name}")
    return path


def configuration(root: Path) -> tuple[dict, list[str]]:
    manifest = tomllib.loads((root / "ESTATE.toml").read_text())
    if manifest.get("version") != 3 or manifest.get("template") != "estate-repository-v3" \
            or manifest.get("authority", {}).get("acceptance_authority") is not False:
        raise ValueError("formal gate requires the v3 non-admitting reference manifest")
    spec = manifest["formalization"]
    if set(spec) != {"scope", "gate", "implementation_paths", "lean", "quint"}:
        raise ValueError("unsupported formalization configuration or status flag")
    if spec["gate"] != "tools/check_formal.py" or set(spec["implementation_paths"]) != IMPLEMENTATIONS:
        raise ValueError("manifest implementation scope differs from the executed formal profile")
    for lane, sources, pin, obligations in (
        ("lean", LEAN_SOURCES, LEAN_TOOLCHAIN, LEAN_OBLIGATIONS | stored.LEAN_OBLIGATIONS | dag.LEAN_OBLIGATIONS | substitution.LEAN_OBLIGATIONS),
        ("quint", QUINT_SOURCES, QUINT_TOOLCHAIN, QUINT_TESTS | {"safety"} | stored.QUINT_OBLIGATIONS | dag.QUINT_OBLIGATIONS | substitution.QUINT_OBLIGATIONS),
    ):
        row = spec[lane]
        if set(row) != {"toolchain", "sources", "obligations"} \
                or row["toolchain"] != pin or set(row["sources"]) != sources \
                or set(row["obligations"]) != obligations \
                or len(row["obligations"]) != len(obligations):
            raise ValueError(f"{lane}: declaration differs from executed sources, pins or obligations")
    if (root / "formal/lean/lean-toolchain").read_text().strip() != LEAN_TOOLCHAIN:
        raise ValueError("Lean toolchain file differs from its declared pin")
    package = json.loads((root / "formal/quint/package.json").read_text())
    lock = json.loads((root / "formal/quint/package-lock.json").read_text())
    if package["dependencies"].get("@informalsystems/quint") != "0.33.1" \
            or lock["packages"]["node_modules/@informalsystems/quint"]["version"] != "0.33.1":
        raise ValueError("Quint package or lock differs from its declared pin")
    paths = sorted(LEAN_SOURCES | QUINT_SOURCES | IMPLEMENTATIONS | dag.DOCUMENTS | substitution.DOCUMENTS | {
        "ESTATE.toml", spec["scope"], "formal/lean/lean-toolchain", "formal/quint/package.json",
        "formal/quint/package-lock.json", "conformance/dependencies.json", "conformance/source-provenance.json",
        "schemas/binding-trace-v1.md",
    })
    for path in paths:
        owned(root, path)
    return spec, paths


def covered_inputs(root: Path, files: list[dict]) -> tuple[dict, list[str]]:
    spec, paths = configuration(root)
    covered = {row["path"] for row in files}
    if missing := set(paths) - covered:
        raise ValueError(f"declared inputs are excluded from the source digest: {sorted(missing)}")
    return spec, paths


def run(command: list[str], cwd: Path, output: Path, receipt: dict, name: str,
        *, env: dict | None = None, stdin: str | None = None, expected_exit: int = 0,
        compress_log: bool = False) -> str:
    row = {"name": name, "command": command, "cwd": str(cwd), "started_at_utc": acceptance.now()}
    if stdin is not None:
        row["stdin_sha256"] = hashlib.sha256(stdin.encode()).hexdigest()
    if env is not None:
        row["environment_overrides"] = {key: env[key] for key in ("LEAN_PATH", "QUINT") if key in env}
    receipt["commands"].append(row)
    save(output / "results.json", receipt)
    try:
        result = subprocess.run(command, cwd=cwd, env=env, input=stdin, capture_output=True,
                                text=True, timeout=300)
        text = result.stdout + result.stderr
        row["exit_code"] = result.returncode
    except (OSError, subprocess.TimeoutExpired) as error:
        text = f"{type(error).__name__}: {error}\n"
        row.update(exit_code=None, execution_error=type(error).__name__)
    log = output / (f"{name}.log.gz" if compress_log else f"{name}.log")
    encoded = text.encode()
    if compress_log:
        log.write_bytes(gzip.compress(encoded, mtime=0))
        row.update(log_encoding="gzip", uncompressed_bytes=len(encoded),
                   uncompressed_sha256=hashlib.sha256(encoded).hexdigest())
    else:
        log.write_bytes(encoded)
    row.update(finished_at_utc=acceptance.now(), log=log.name, log_sha256=runtime.sha256(log))
    save(output / "results.json", receipt)
    if row["exit_code"] != expected_exit:
        raise RuntimeError(f"{name}: expected exit {expected_exit}, got {row['exit_code']}; see {log.name}")
    print(f"{name}: exit {row['exit_code']}", flush=True)
    return result.stdout


def fingerprint(executables: dict[str, Path]) -> list[dict]:
    return [{"tool": name, "path": str(path), "sha256": runtime.sha256(path)}
            for name, path in sorted(executables.items())]


def require_quint_node(selected: Path) -> None:
    # The installed Quint CLI uses /usr/bin/env node. Its replay adapter inherits
    # the same PATH, so an override may not attest a different executable.
    actual = shutil.which("node")
    if actual is None or Path(actual).resolve() != selected.resolve():
        raise ValueError("selected NODE differs from the node used by Quint on PATH")


def counterexample(exit_code: int, text: str, path: Path) -> None:
    if exit_code != 1 or "[violation] Found an issue" not in text or "error: Invariant violated" not in text:
        raise ValueError("unsafe insertion did not produce the designated invariant failure")
    states = json.loads(path.read_text()).get("states", [])
    if len(states) != 2:
        raise ValueError("unsafe insertion did not produce its two-state witness")
    before, after = states[0]["s"], states[1]["s"]
    if before["environment"] != [] or after["environment"] != [{"#bigint": "0"}] \
            or before["outcomes"] != [] \
            or after["outcomes"] != [{"name": {"#bigint": "0"}, "code": {"#bigint": "6"}}] \
            or after["halted"] is not False or after["acceptance_authority"] is not False:
        raise ValueError("unsafe insertion witness differs from the refused-definition mutation")


def execute(output: Path, receipt: dict) -> None:
    lean = runtime.executable("LEAN", "lean")
    quint = runtime.executable("QUINT", str(ROOT / "formal/quint/node_modules/.bin/quint"))
    node = runtime.executable("NODE", "node")
    require_quint_node(node)
    gcc = runtime.executable("GOOSE_CC", "gcc")
    lean_version = run([str(lean), "--version"], ROOT, output, receipt, "lean-version").strip()
    if "version 4.34.1," not in lean_version or LEAN_COMMIT not in lean_version:
        raise ValueError("Lean executable differs from its pinned version/revision")
    if run([str(quint), "--version"], ROOT, output, receipt, "quint-version").strip() != "0.33.1":
        raise ValueError("Quint executable differs from its pinned version")
    if run([str(node), "--version"], ROOT, output, receipt, "node-version").strip() != NODE_VERSION:
        raise ValueError("Node executable differs from its pinned version")
    compiler_version = run([str(gcc), "--version"], ROOT, output, receipt, "gcc-version")
    if "gcc" not in compiler_version.lower() and "free software foundation" not in compiler_version.lower():
        raise ValueError("the pinned native comparison profile requires GCC")
    inventory = profile.cases()
    if len(inventory) != profile.CASE_COUNT or len(set(inventory)) != profile.CASE_COUNT:
        raise ValueError("finite action inventory differs from its declared bound")
    inputs = "\n".join(profile.encode(actions) for actions in inventory) + "\n"
    (output / "transaction-inputs.txt").write_text(inputs)
    with tempfile.TemporaryDirectory(prefix="lean-goose-formal-") as folder:
        build = Path(folder)
        context = runtime.prepare(build)
        receipt["dependencies_before"] = context["dependency_observations"]
        goose = Path(os.environ.get("GOOSE", str(context["goose_path"] / "build/goose"))).absolute()
        executables = {"lean": lean, "quint_cli": quint, "node": node, "gcc": gcc, "goose": goose}
        receipt["toolchains"] = {"lean": lean_version, "quint": "0.33.1", "node": NODE_VERSION,
                                 "lean_flags": LEAN_FLAGS,
                                 "quint_backend": "typescript", "executables": fingerprint(executables)}
        lean_build = build / "lean"
        lean_build.mkdir()
        for source in LEAN_SOURCES:
            shutil.copyfile(ROOT / source, lean_build / Path(source).name)
        env = dict(os.environ, LEAN_PATH=str(lean_build), QUINT=str(quint))
        model = lean_build / "DefinitionTransactions.olean"
        run([str(lean), *LEAN_FLAGS, "-o", str(model), "DefinitionTransactions.lean"], lean_build, output, receipt,
            "lean-build", env=env)
        audit = run([str(lean), *LEAN_FLAGS, "Audit.lean"], lean_build, output, receipt, "lean-axiom-audit", env=env)
        if "Goose transaction axiom audit passed: 21 required theorems without axioms;" not in audit:
            raise ValueError("Lean audit did not confirm its entire required theorem inventory")
        receipt["lean"] = {"status": "passed", "obligations": sorted(LEAN_OBLIGATIONS),
                           "required_theorem_axioms": [], "namespace_support_axiom_allowlist": ["propext"],
                           "compiled_model_sha256": runtime.sha256(model)}
        lean_results = profile.decode_models(run([str(lean), *LEAN_FLAGS, "--run", "Replay.lean"], lean_build,
            output, receipt, "lean-replay", env=env, stdin=inputs), inventory)
        quint_root = ROOT / "formal/quint"
        run([str(quint), "typecheck", "DefinitionTransactions.qnt"], quint_root, output, receipt, "quint-typecheck")
        tests = run([str(quint), "test", "DefinitionTransactions.qnt", "--backend=typescript",
                     "--max-samples=1", f"--seed={SEED}"], quint_root, output, receipt, "quint-tests")
        if "12 passing" not in tests or any(f"ok {name} passed 1 test(s)" not in tests for name in QUINT_TESTS):
            raise ValueError("Quint did not execute the complete deterministic test inventory")
        simulation = run([str(quint), "run", "DefinitionTransactions.qnt", "--backend=typescript",
            "--invariant=safety", "--max-samples=1000", "--max-steps=40", f"--seed={SEED}", "--verbosity=1"],
            quint_root, output, receipt, "quint-bounded-run")
        if "[ok] No violation found" not in simulation:
            raise ValueError("Quint did not complete its bounded invariant check")
        trace = output / "quint-negative.itf.json"
        trace.unlink(missing_ok=True)
        negative = run([str(quint), "run", "DefinitionTransactions.qnt", "--backend=typescript",
            "--step=unsafeStep", "--invariant=safety", "--max-samples=1", "--max-steps=1",
            f"--seed={SEED}", "--verbosity=2", "--out-itf", str(trace)], quint_root,
            output, receipt, "quint-negative-control", expected_exit=1)
        # Quint writes the violation summary on stderr; verify the complete captured log.
        counterexample(1, (output / "quint-negative-control.log").read_text(), trace)
        quint_results = profile.decode_models(run([sys.executable, str(quint_root / "replay.py")],
            ROOT, output, receipt, "quint-replay", env=env, stdin=inputs), inventory)
        if lean_results != quint_results:
            raise ValueError("Lean and Quint transaction predictions disagree")
        receipt["quint"] = {"status": "passed", "tests": sorted(QUINT_TESTS), "backend": "typescript",
            "invariant": "safety", "seed": SEED, "max_samples": 1000, "max_steps": 40,
            "unbounded_proof": False, "negative_control": {"witnessed": True, "expected_exit_code": 1,
                "trace": trace.name, "sha256": runtime.sha256(trace)}}
        generated, binary = build / "checker.c", build / "checker"
        run([str(goose), *runtime.GOOSE_FLAGS, "-o", str(generated), str(ROOT / "reference/checker.goose")],
            ROOT, output, receipt, "goose-emit")
        if "#define GS_DEBUG 1" not in generated.read_text():
            raise ValueError("generated Goose runtime checks are disabled")
        run([str(gcc), "-O2", str(generated), "-o", str(binary), "-lm", "-pthread"],
            ROOT, output, receipt, "goose-build")
        receipt["native_build"] = {"generated_c_sha256": runtime.sha256(generated),
                                   "binary_sha256": runtime.sha256(binary)}
        completed, halted = 0, 0
        fixture = build / "transaction.tsv"
        comparison = output / "native-comparison.jsonl"
        with comparison.open("w") as log:
            for index, (actions, prediction) in enumerate(zip(inventory, lean_results)):
                fixture.write_text(profile.fixture(actions))
                result = subprocess.run([str(binary), "--check", str(fixture)], cwd=ROOT,
                                        capture_output=True, text=True, timeout=15)
                observed = profile.check_native(prediction, result.returncode, result.stdout, result.stderr)
                log.write(json.dumps({"case": index, "input": profile.encode(actions),
                    "fixture_sha256": runtime.sha256(fixture), "model": prediction,
                    "native_exit_code": result.returncode, "native": observed}, separators=(",", ":")) + "\n")
                halted += prediction["halted"]
                completed += not prediction["halted"]
        receipt["finite_correspondence"] = {"status": "passed", "cases": len(inventory),
            "action_count": len(profile.ACTIONS), "names": [0, 1], "trace_lengths": [1, 2, 3],
            "completed_receipts": completed, "designated_scope_failures": halted,
            "lean_quint_full_model_agreement": True,
            "native_projection": "ordered observations, success count, authority, or designated fatal exit with no receipt",
            "universal_implementation_refinement": False,
            "inputs": "transaction-inputs.txt", "inputs_sha256": runtime.sha256(output / "transaction-inputs.txt"),
            "log": comparison.name, "log_sha256": runtime.sha256(comparison),
            "native_command_template": [str(binary), "--check", str(fixture)]}
        stored.execute(output=output, receipt=receipt, build=build, lean_build=lean_build,
                       lean=lean, lean_flags=LEAN_FLAGS, quint=quint, binary=binary, env=env, seed=SEED, run=run)
        dag.execute(output=output, receipt=receipt, build=build, lean_build=lean_build,
                    lean=lean, lean_flags=LEAN_FLAGS, quint=quint, binary=binary, env=env, seed=SEED, run=run)
        substitution.execute(output=output, receipt=receipt, build=build, lean_build=lean_build,
                             lean=lean, lean_flags=LEAN_FLAGS, quint=quint, goose=goose, gcc=gcc,
                             binary=binary, env=env, seed=SEED, run=run)
        receipt["dependencies_after"] = runtime.verify_dependencies(context)
        if receipt["dependencies_before"] != receipt["dependencies_after"]:
            raise ValueError("external dependency source changed during formal verification")
        receipt["tool_executables_unchanged"] = fingerprint(executables) == receipt["toolchains"]["executables"]
        if not receipt["tool_executables_unchanged"]:
            raise ValueError("formal tool executable identity changed during verification")
        print(f"Native finite correspondence: {len(inventory)} traces passed.", flush=True)


def verify(output: Path) -> int:
    output = output.resolve()
    if output.is_relative_to(ROOT) and not output.is_relative_to(acceptance.EVIDENCE):
        raise ValueError("formal output must be under conformance/evidence or outside the repository")
    output.mkdir(parents=True, exist_ok=True)
    receipt = {"schema": "lean-goose.formal-evidence.v4", "status": "running",
        "started_at_utc": acceptance.now(), "evidence_only": True, "acceptance_authority": False,
        "hosted_results_included": False, "implementation_correspondence": "finite_profile_only",
        "scope": "ordered transactions, complete stored bindings, immutable expression DAGs, binder scope, lifting and capture-avoiding substitution; no full kernel refinement",
        "commands": [], "excluded_build_directories": sorted(acceptance.SKIP_DIRS),
        "excluded_build_suffixes": sorted(acceptance.SKIP_SUFFIXES),
        "excluded_evidence_directory": "conformance/evidence/"}
    save(output / "results.json", receipt)
    try:
        files, digest = acceptance.source_snapshot()
        spec, inputs = covered_inputs(ROOT, files)
        receipt.update(source_tree_sha256=digest, policy_sha256=runtime.sha256(ROOT / "ESTATE.toml"),
                       source_manifest="source-manifest.json", formalization=spec, declared_inputs=inputs,
                       base_revision=acceptance.git_revision())
        save(output / "source-manifest.json", files)
        save(output / "results.json", receipt)
        execute(output, receipt)
        after_files, after_digest = acceptance.source_snapshot()
        after_spec, after_inputs = covered_inputs(ROOT, after_files)
        receipt["source_unchanged"] = files == after_files and digest == after_digest \
            and spec == after_spec and inputs == after_inputs
        if not receipt["source_unchanged"]:
            raise ValueError("source or formal declaration changed during verification")
        receipt["status"] = "passed"
    except (Exception, KeyboardInterrupt) as error:
        receipt.update(status="failed", failure=f"{type(error).__name__}: {error}")
        print(receipt["failure"], file=sys.stderr, flush=True)
    receipt["finished_at_utc"] = acceptance.now()
    save(output / "results.json", receipt)
    print(f"Formal verification {receipt['status']}: {output / 'results.json'}", flush=True)
    return 0 if receipt["status"] == "passed" else 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=acceptance.EVIDENCE / "formal")
    raise SystemExit(verify(parser.parse_args().output))
