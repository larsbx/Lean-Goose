#!/usr/bin/env python3
"""Run repository verification and record exact-source, observation-only evidence."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "conformance/evidence"
RECEIPT = EVIDENCE / "verification.json"
SKIP_DIRS = {".git", "_build", "__pycache__", "build", "dist", "coverage", ".cache", ".venv", "node_modules", ".lake"}
SKIP_SUFFIXES = {".cmi", ".cmo", ".cmx", ".o", ".pyc", ".olean", ".ilean"}


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def write_json(path: Path, value: object) -> None:
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def source_snapshot() -> tuple[list[dict[str, object]], str]:
    files = []

    def fail_walk(error: OSError) -> None:
        raise error

    for parent, directories, names in os.walk(ROOT, onerror=fail_walk):
        directories[:] = sorted(d for d in directories if d not in SKIP_DIRS
                                and Path(parent) / d != EVIDENCE)
        for directory in directories:
            if (Path(parent) / directory).is_symlink():
                raise ValueError(f"source directory symlink is outside the receipt contract: {Path(parent) / directory}")
        for name in sorted(names):
            path = Path(parent) / name
            if name == ".git" or path.suffix in SKIP_SUFFIXES:
                continue
            if path.is_symlink():
                raise ValueError(f"source symlink is outside the receipt contract: {path}")
            content = path.read_bytes()
            files.append({"path": path.relative_to(ROOT).as_posix(), "bytes": len(content),
                          "sha256": hashlib.sha256(content).hexdigest()})
    files.sort(key=lambda item: item["path"])
    encoded = json.dumps(files, sort_keys=True, separators=(",", ":")).encode()
    return files, hashlib.sha256(encoded).hexdigest()


def git_revision() -> str | None:
    top = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=ROOT,
                         capture_output=True, text=True, timeout=15)
    if top.returncode or Path(top.stdout.strip()).resolve() != ROOT:
        return None
    result = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                            capture_output=True, text=True, timeout=15)
    return result.stdout.strip() if result.returncode == 0 else None


def run(name: str, command: list[str], timeout: int = 600) -> dict[str, object]:
    logfile = EVIDENCE / f"{name}.log"
    record: dict[str, object] = {"name": name, "command": command, "timeout_seconds": timeout, "started_at_utc": now()}
    print(f"Verifying {name}.", flush=True)
    try:
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        output = result.stdout + result.stderr
        record.update(status="passed" if result.returncode == 0 else "failed", exit_code=result.returncode)
    except (OSError, subprocess.TimeoutExpired) as error:
        output = f"{type(error).__name__}: {error}\n"
        record.update(status="failed", exit_code=None, execution_error=type(error).__name__)
    logfile.write_text(output)
    print(output, end="" if output.endswith("\n") else "\n", flush=True)
    record.update(finished_at_utc=now(), log=logfile.relative_to(ROOT).as_posix(),
                  log_sha256=hashlib.sha256(logfile.read_bytes()).hexdigest())
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit", type=Path,
                        default=Path(os.environ["ESTATE_AUDITOR"]) if os.environ.get("ESTATE_AUDITOR") else None,
                        help="already obtained pinned external estate auditor")
    args = parser.parse_args()
    EVIDENCE.mkdir(parents=True, exist_ok=True)
    receipt: dict[str, object] = {
        "schema": "lean-goose.local-verification.v1", "status": "running", "started_at_utc": now(),
        "acceptance_authority": False, "authority": "unsigned_local_test_observations_only",
        "hosted_results_included": False, "source_manifest": "conformance/evidence/source-manifest.json",
        "evidence_directory_excluded_from_source_digest": "conformance/evidence/",
        "source_digest_encoding": "SHA-256 of sorted path/bytes/sha256 objects; compact JSON with sorted keys",
        "excluded_build_directories": sorted(SKIP_DIRS), "excluded_build_suffixes": sorted(SKIP_SUFFIXES),
        "checks": [],
    }
    # Replace stale success before any prerequisite, source or subprocess check.
    write_json(RECEIPT, receipt)
    try:
        receipt["base_revision"] = git_revision()
        files, digest = source_snapshot()
        receipt["source_tree_sha256"] = digest
        write_json(EVIDENCE / "source-manifest.json", files)
        write_json(RECEIPT, receipt)
        commands = [
            ("estate-audit", ["sh", "tools/estate-audit.sh"]
             + ([str(args.audit.resolve())] if args.audit else [])),
            ("formal-tests", [sys.executable, "-m", "unittest", "discover", "-s", "tests", "-v"]),
            ("formal", [sys.executable, "tools/check_formal.py"]),
            ("conformance", [sys.executable, "tools/run.py", "check", "--definitions", "128",
                             "--output", "conformance/evidence/check"]),
            ("benchmark-smoke", [sys.executable, "tools/run.py", "bench", "--samples", "1",
                                 "--definitions", "8", "--workers", "1", "--min-sample-seconds", "0.05",
                                 "--output", "conformance/evidence/smoke"]),
        ]
        for name, command in commands:
            # Four required formal scopes include replay of every observed
            # native arena. Keep individual model/native command limits intact;
            # allow the expanded sequential orchestration thirty minutes.
            record = run(name, command, timeout=1800 if name == "formal" else 600)
            receipt["checks"].append(record)
            write_json(RECEIPT, receipt)
            if record["status"] != "passed":
                raise RuntimeError(f"{name} failed; see {record['log']}")
        after_files, after_digest = source_snapshot()
        unchanged = files == after_files and digest == after_digest
        receipt["source_unchanged_during_verification"] = unchanged
        if not unchanged:
            raise RuntimeError("source changed during verification")
        receipt["status"] = "passed"
    except Exception as error:
        receipt.update(status="failed", failure=f"{type(error).__name__}: {error}")
        print(receipt["failure"], file=sys.stderr, flush=True)
    receipt["finished_at_utc"] = now()
    write_json(RECEIPT, receipt)
    print(f"Repository verification {receipt['status']}; evidence: {RECEIPT.relative_to(ROOT)}", flush=True)
    return 0 if receipt["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
