"""Derive a diagnostic executable from the exact owned checker and one driver.

The only checker change is the unique main identifier. All transformation,
parser, import, metadata, resource, and trace functions are preserved byte for
byte. This module generates source; root orchestration executes and attests the
actual pinned compiler and resulting native executable.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

CHECKER = "reference/checker.goose"
DRIVER = "reference/substitution-driver.goose"
CHECKER_SHA256 = "0de9dfe21a2e95fd0468fd9365ff8e73a18a22e91f457dd4e16209bf740f0e0a"
MAIN = b"\nfn main() {"
RENAMED_MAIN = b"\nfn original_main() {"
SEPARATOR = b"\n// BEGIN OWNED SUBSTITUTION DIAGNOSTIC DRIVER\n"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def owned(root: Path, name: str) -> bytes:
    path = root / name
    if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError("harness source must remain an owned repository file")
    return path.read_bytes()


def reconstruct(checker: bytes, driver: bytes) -> bytes:
    if digest(checker) != CHECKER_SHA256:
        raise ValueError("harness checker differs from the reviewed source pin")
    if checker.count(MAIN) != 1 or RENAMED_MAIN in checker or SEPARATOR in checker:
        raise ValueError("ambiguous original checker entrypoint")
    if driver.count(MAIN) != 1 or RENAMED_MAIN in driver or SEPARATOR in driver:
        raise ValueError("ambiguous substitution driver entrypoint")
    if not checker.endswith(b"\n") or not driver.endswith(b"\n"):
        raise ValueError("harness sources must preserve final LF")
    renamed = checker.replace(MAIN, RENAMED_MAIN, 1)
    if renamed.replace(RENAMED_MAIN, MAIN, 1) != checker:
        raise ValueError("checker rename failed exact round trip")
    return renamed + SEPARATOR + driver


def verify_generated(checker: bytes, driver: bytes, generated: bytes) -> None:
    expected = reconstruct(checker, driver)
    if generated != expected:
        raise ValueError("generated harness differs from its exact reviewed derivation")
    prefix, appended = generated.split(SEPARATOR)
    if prefix.replace(RENAMED_MAIN, MAIN, 1) != checker or appended != driver:
        raise ValueError("generated harness changed checker or driver bytes")


def generate(root: Path, output: Path) -> dict:
    root = root.resolve()
    output = output.absolute()
    # Build artifacts must not replace any owned or externally supplied source.
    if output.resolve().is_relative_to(root) or output.exists() or output.is_symlink():
        raise ValueError("generated harness must be a new nonsymlink temporary file outside the repository")
    checker, driver = owned(root, CHECKER), owned(root, DRIVER)
    provenance = json.loads(owned(root, "conformance/source-provenance.json"))
    if provenance.get("local_path") != CHECKER or provenance.get("local_sha256") != CHECKER_SHA256:
        raise ValueError("harness checker pin differs from the owned provenance contract")
    generated = reconstruct(checker, driver)
    # Exclusive creation also refuses a file or symlink created after the check.
    with output.open("xb") as destination:
        destination.write(generated)
    verify_generated(checker, driver, output.read_bytes())
    return {"schema": "lean-goose.substitution-harness.v1", "checker": CHECKER,
            "checker_sha256": digest(checker), "driver": DRIVER, "driver_sha256": digest(driver),
            "generated_source_sha256": digest(generated), "generated_source_bytes": len(generated),
            "checker_bytes_preserved_except_main_identifier": True,
            "original_main_rename": "main -> original_main", "acceptance_authority": False}
