#!/usr/bin/env python3
"""Observe the local bounded Goose reference against pinned external comparators."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import math
import os
from pathlib import Path
import platform
import random
import statistics
import sys
import tempfile
import time
from typing import Any

import runtime

DEFINITION_SCHEMA = "lean-goose.definition-observations.v1"
BENCHMARK_SCHEMA = "lean-goose.benchmark-observation.v1"
WORKLOADS = ("wide", "chain", "identities", "distinct_trees", "unshared_trees",
             "dependent_terms", "alias_diamonds")
BOUNDARIES = ["etaBoundary", "proofIrrelevanceBoundary"]
REFERENCE_OUTCOMES = {"observed_success", "Unknown_constant", "Duplicate_definition",
                      "Expected_sort", "Expected_function", "Type_mismatch"}
LEAN_OUTCOMES = {"observed_success", "unknownConstant", "alreadyDeclared", "typeExpected",
                 "funExpected", "appTypeMismatch", "letTypeMismatch", "declTypeMismatch"}


def now() -> str:
    return datetime.now(timezone.utc).isoformat()


def save(path: Path, value: dict[str, Any]) -> None:
    temporary = path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n")
    temporary.replace(path)


def json_object(text: str) -> dict[str, Any]:
    def unique(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate observation field")
            result[key] = value
        return result

    def invalid_constant(_: str) -> None:
        raise ValueError("nonfinite observation value")

    value = json.loads(text, object_pairs_hook=unique, parse_constant=invalid_constant)
    if not isinstance(value, dict):
        raise ValueError("observer output must be one JSON object")
    return value


def normalize_expected(rows: list[dict[str, str]]) -> list[dict[str, str]]:
    return [{"name": row["name"],
             "outcome": "observed_success" if row["outcome"] == "accepted" else row["outcome"]}
            for row in rows]


def definition_observation(engine: str, raw: dict[str, Any],
                           expected: list[dict[str, str]]) -> dict[str, Any]:
    local = engine == "goose-aot"
    count_key = "success_observations" if local else "accepted"
    fields = {"engine", "status", "outcomes", count_key, "acceptance_authority"}
    if local:
        fields.add("schema")
    if engine == "lean-kernel":
        fields.update(("trust_level", "checked_insertion"))
    if set(raw) != fields or raw.get("engine") != engine or raw.get("status") != "checked" \
            or raw.get("acceptance_authority") is not False:
        raise RuntimeError(f"{engine}: unknown or non-observational definition output")
    if local and raw["schema"] != DEFINITION_SCHEMA:
        raise RuntimeError("local Goose definition schema differs from contract")
    if engine == "lean-kernel" and (type(raw["trust_level"]) is not int or raw["trust_level"] != 0
                                    or raw["checked_insertion"] is not True):
        raise RuntimeError("Lean did not report checked insertion at trust level zero")
    if not isinstance(raw["outcomes"], list):
        raise RuntimeError(f"{engine}: malformed ordered observation inventory")
    outcomes = []
    allowed = LEAN_OUTCOMES if engine == "lean-kernel" else REFERENCE_OUTCOMES
    for row in raw["outcomes"]:
        if not isinstance(row, dict) or set(row) != {"name", "outcome"} \
                or not isinstance(row["name"], str) or not isinstance(row["outcome"], str):
            raise RuntimeError(f"{engine}: malformed definition observation")
        outcome = row["outcome"]
        if not local and outcome == "accepted":
            outcome = "observed_success"
        if outcome not in allowed:
            raise RuntimeError(f"{engine}: unregistered semantic observation category")
        outcomes.append({"name": row["name"], "outcome": outcome})
    successes = sum(row["outcome"] == "observed_success" for row in outcomes)
    if type(raw[count_key]) is not int or raw[count_key] != successes or outcomes != expected:
        # Do not re-emit arbitrary or legacy observer stdout in a local receipt.
        raise RuntimeError(f"{engine}: ordered observations differ from registered expectations")
    result = {"schema": DEFINITION_SCHEMA, "engine": engine, "status": "checked",
              "outcomes": outcomes, "success_observations": successes,
              "acceptance_authority": False}
    if engine == "lean-kernel":
        result.update(trust_level=0, checked_insertion=True)
    return result


def check_result(engine: str, binary: Path, path: Path,
                 expected: list[dict[str, str]]) -> dict[str, Any]:
    text = runtime.command([str(binary), "--check", str(path)])
    return definition_observation(engine, json_object(text), normalize_expected(expected))


def fixture(modules: dict[str, Any], workload: str, definitions: int) -> Any:
    baseline, generated = modules["compare_lean"], modules["optimization_workloads"]
    return (generated.fixture(workload, definitions, baseline.Dag)
            if workload in generated.WORKLOADS else baseline.fixture(workload, definitions))


def check_all(binaries: dict[str, Path], modules: dict[str, Any],
              output: Path, definitions: int) -> dict[str, Any]:
    output.mkdir(parents=True, exist_ok=True)
    helpers = modules["test_goose"]
    if tuple(helpers.WORKLOADS) != WORKLOADS:
        raise RuntimeError("external workload inventory differs from local contract")
    cases = helpers.controls()
    differences = []
    for _, _, reference, lean in cases:
        if len(reference) != len(lean):
            raise RuntimeError("external expectations have unequal inventories")
        for left, right in zip(normalize_expected(reference), normalize_expected(lean)):
            if left["name"] != right["name"]:
                raise RuntimeError("external expectation order differs across engines")
            if (left["outcome"] == "observed_success") != (right["outcome"] == "observed_success"):
                if left["outcome"] != "Type_mismatch" or right["outcome"] != "observed_success":
                    raise RuntimeError("unexpected conversion boundary direction")
                differences.append(left["name"])
    if differences != BOUNDARIES or sum(len(graph.definitions) for _, graph, _, _ in cases) != 68:
        raise RuntimeError("external controls differ from the registered finite inventory")
    for workload in WORKLOADS:
        graph = fixture(modules, workload, definitions)
        expected = [{"name": name, "outcome": "observed_success"} for name, _, _ in graph.definitions]
        cases.append((workload, graph, expected, expected))
    observations = []
    for name, graph, reference, lean in cases:
        path = output / f"{name}.tsv"
        path.write_text(graph.render())
        results = [check_result(engine, binaries[key], path, expected)
                   for engine, key, expected in [("lean-kernel", "lean-kernel", lean),
                                                 ("ocaml-bytecode", "ocaml-check", reference),
                                                 ("goose-aot", "goose-aot", reference)]]
        observations.append({"case": name, "fixture": path.name, "sha256": runtime.sha256(path),
                             "definitions": len(graph.definitions), "engines": results})
        print(f"Observed {name}: {len(graph.definitions)} ordered outcomes match expectations.", flush=True)
    invalid = helpers.structural_controls(binaries["goose-aot"], output)
    if len(invalid) != 6:
        raise RuntimeError("external structural-control inventory differs from local contract")
    result = {"schema": "lean-goose.conformance-observations.v1", "status": "passed",
              "evidence_only": True, "acceptance_authority": False, "fixtures": len(cases),
              "ordered_outcomes_per_engine": sum(len(graph.definitions) for _, graph, _, _ in cases),
              "registered_disagreements": BOUNDARIES,
              "structural_and_resource_controls": invalid, "observations": observations}
    save(output / "results.json", result)
    return result


def measure(engine: str, binary: Path, workers: int, path: Path,
            iterations: int, definitions: int) -> dict[str, Any]:
    args = [str(binary), str(path)]
    if engine != "lean-kernel":
        args.append(str(workers))
    args.append(str(iterations))
    start = time.perf_counter_ns()
    raw = json_object(runtime.command(args, timeout=600))
    process_ns = time.perf_counter_ns() - start
    fields = {"engine", "status", "workers", "iterations", "definitions", "elapsed_ns",
              "per_batch_ns", "validated_batches", "refusal_controls"}
    if engine == "goose-aot":
        fields.update(("schema", "acceptance_authority"))
    elif engine == "lean-kernel":
        fields.remove("workers")
        fields.update(("trust_level", "checked_insertion"))
    elif engine == "ocaml-bytecode":
        fields.update(("waves", "cpu_s"))
    else:
        raise RuntimeError("unregistered measurement engine")
    if set(raw) != fields or raw.get("engine") != engine or raw.get("status") != "passed":
        raise RuntimeError(f"{engine}: unknown or incomplete benchmark observation")
    # The pinned Lean driver is serial and does not emit a worker-count field.
    # Its one-worker configuration is fixed here, before normalized validation.
    if engine == "lean-kernel":
        raw["workers"] = 1
    for key, expected in (("workers", workers), ("iterations", iterations), ("definitions", definitions),
                          ("validated_batches", iterations), ("refusal_controls", 1)):
        if type(raw[key]) is not int or raw[key] != expected:
            raise RuntimeError(f"{engine}: benchmark inventory mismatch: {key}")
    if type(raw["elapsed_ns"]) is not int or raw["elapsed_ns"] <= 0 \
            or type(raw["per_batch_ns"]) not in (int, float) or not math.isfinite(raw["per_batch_ns"]) \
            or abs(raw["per_batch_ns"] - raw["elapsed_ns"] / iterations) > 1.01:
        raise RuntimeError(f"{engine}: invalid timing observation")
    if engine == "goose-aot" and (raw["schema"] != BENCHMARK_SCHEMA
                                  or raw["acceptance_authority"] is not False):
        raise RuntimeError("local Goose benchmark schema or authority mismatch")
    if engine == "lean-kernel" and (type(raw["trust_level"]) is not int or raw["trust_level"] != 0
                                    or raw["checked_insertion"] is not True):
        raise RuntimeError("Lean benchmark did not report checked insertion at trust level zero")
    if engine == "ocaml-bytecode" and (type(raw["waves"]) is not int or raw["waves"] < 1
                                       or type(raw["cpu_s"]) not in (int, float)
                                       or not math.isfinite(raw["cpu_s"]) or raw["cpu_s"] < 0):
        raise RuntimeError("invalid OCaml batch observations")
    return {**raw, "schema": BENCHMARK_SCHEMA, "acceptance_authority": False,
            "process_elapsed_ns": process_ns, "command": args}


def benchmark(args: argparse.Namespace, receipt: dict[str, Any], binaries: dict[str, Path],
              modules: dict[str, Any], output: Path) -> None:
    conformance = check_all(binaries, modules, output / "fixtures", args.definitions)
    receipt["conformance"] = {key: value for key, value in conformance.items() if key != "observations"}
    receipt["conformance"].update(path="fixtures/results.json",
                                  sha256=runtime.sha256(output / "fixtures/results.json"))
    configurations = [("lean-kernel", binaries["lean-kernel"], 1),
                      ("goose-aot", binaries["goose-aot"], 1),
                      *[("ocaml-bytecode", binaries["ocaml-bytecode"], workers) for workers in args.workers]]
    receipt.update(fixtures=[], calibrations=[], observations=[])
    for workload in WORKLOADS:
        path = output / "fixtures" / f"{workload}.tsv"
        graph = fixture(modules, workload, args.definitions)
        if path.read_text() != graph.render():
            raise RuntimeError("semantic-control fixture differs from timing fixture")
        receipt["fixtures"].append({"workload": workload, "path": f"fixtures/{path.name}",
                                    "sha256": runtime.sha256(path),
                                    **modules["optimization_workloads"].inventory(graph)})
        iterations = {}
        for engine, binary, workers in configurations:
            observation = measure(engine, binary, workers, path, 1, args.definitions)
            count = max(1, min(100_000, math.ceil(args.min_sample_seconds * 1e9 / observation["elapsed_ns"])))
            iterations[(engine, workers)] = count
            receipt["calibrations"].append({"workload": workload, **observation, "selected_iterations": count})
        for sample in range(args.samples):
            ordered = configurations.copy()
            random.Random(20261119 + sample).shuffle(ordered)
            for engine, binary, workers in ordered:
                observation = measure(engine, binary, workers, path, iterations[(engine, workers)], args.definitions)
                receipt["observations"].append({"workload": workload, "sample": sample + 1, **observation})
                print(f"{workload}: {engine}, workers={workers}, sample={sample + 1}: "
                      f"{observation['elapsed_ns'] / observation['iterations'] / 1e6:.6f} ms/batch", flush=True)
                save(output / "results.json", receipt)
    summaries = []
    for workload in WORKLOADS:
        for engine, _, workers in configurations:
            values = [row["elapsed_ns"] / row["iterations"] / 1e6 for row in receipt["observations"]
                      if (row["workload"], row["engine"], row["workers"]) == (workload, engine, workers)]
            summaries.append({"workload": workload, "engine": engine, "workers": workers,
                              "median_ms": statistics.median(values), "mean_ms": statistics.mean(values),
                              "min_ms": min(values), "max_ms": max(values),
                              "stdev_ms": statistics.stdev(values) if len(values) > 1 else 0.0})
    receipt["summaries"] = summaries


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_subparsers(dest="mode", required=True)
    for mode in ("pins", "check", "bench"):
        sub = modes.add_parser(mode)
        sub.add_argument("--output", type=Path, default=runtime.ROOT / "conformance/evidence" / mode)
        if mode != "pins":
            sub.add_argument("--definitions", type=int, default=128)
        if mode == "bench":
            sub.add_argument("--samples", type=int, default=7)
            sub.add_argument("--min-sample-seconds", type=float, default=0.15)
            sub.add_argument("--workers", nargs="+", type=int, default=[1, 2, 4, 8])
    args = parser.parse_args()
    if args.mode != "pins" and not 1 <= args.definitions <= 512:
        parser.error("definitions must be in 1..512")
    if args.mode == "bench":
        if not 1 <= args.samples <= 30 or not math.isfinite(args.min_sample_seconds) \
                or not 0.05 <= args.min_sample_seconds <= 5:
            parser.error("samples must be in 1..30 and min-sample-seconds in 0.05..5")
        if any(n < 1 or n > 64 for n in args.workers) or len(set(args.workers)) != len(args.workers):
            parser.error("workers must be distinct counts in 1..64")
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    schemas = {"pins": "lean-goose.dependency-observations.v1",
               "check": "lean-goose.conformance-observations.v1",
               "bench": "lean-goose.benchmark-evidence.v1"}
    receipt: dict[str, Any] = {
        "schema": schemas[args.mode], "status": "running", "mode": args.mode,
        "started_at_utc": now(), "acceptance_authority": False, "evidence_only": True,
        "authority": "unsigned_local_observations_only",
    }
    # Invalidate any previous successful receipt before probing sources or Git.
    save(output / "results.json", receipt)
    try:
        receipt["sources_before"] = runtime.source_files()
        receipt["source_revision"] = runtime.command(["git", "rev-parse", "HEAD"])
        execute(args, receipt, output)
        receipt.update(status="passed", finished_at_utc=now())
        save(output / "results.json", receipt)
        print(f"{args.mode}: passed finite observation checks; evidence only. Receipt: {output / 'results.json'}")
        return 0
    except (Exception, KeyboardInterrupt) as error:
        receipt.update(status="failed", failure=str(error), finished_at_utc=now())
        try:
            receipt["sources_after"] = runtime.source_files()
            receipt["source_unchanged"] = receipt.get("sources_before") == receipt["sources_after"]
        except Exception:
            receipt["source_unchanged"] = False
        save(output / "results.json", receipt)
        print(f"{args.mode}: failed: {error}", file=sys.stderr)
        return 1


def execute(args: argparse.Namespace, receipt: dict[str, Any], output: Path) -> None:
    if args.mode == "bench":
        receipt.update(samples_per_configuration=args.samples, definitions_per_batch=args.definitions,
                       ocaml_workers=args.workers, goose_workers=1,
                       minimum_target_sample_seconds=args.min_sample_seconds,
                       machine={"logical_cpus": os.cpu_count(), "platform": platform.platform(),
                                "affinity_cpus": sorted(os.sched_getaffinity(0))
                                if hasattr(os, "sched_getaffinity") else None},
                       execution_order="one measurement process at a time; deterministic shuffled configurations per round",
                       timing="monotonic complete checked-batch intervals; fresh environment and caches per batch; parsing, source compilation, warmup and result validation untimed; process elapsed time also recorded",
                       scope="synthetic transparent monomorphic definitions with numeric sorts and beta/zeta reduction; different bounded implementations, not a language-only causal comparison")
    save(output / "results.json", receipt)
    with tempfile.TemporaryDirectory(prefix="lean-goose-") as folder:
        build = Path(folder)
        context = runtime.prepare(build)
        receipt["dependencies_before"] = context["dependency_observations"]
        if args.mode != "pins":
            binaries, toolchains, modules = runtime.build_all(build, context)
            receipt["toolchains"] = toolchains
            if args.mode == "check":
                receipt.update(check_all(binaries, modules, output / "fixtures", args.definitions))
                # A local check is complete only after the source/drift checks below.
                receipt["status"] = "running"
                receipt["fixture_directory"] = "fixtures"
            else:
                receipt["machine"]["cpu_model"] = modules["compare_lean"].cpu_description()
                benchmark(args, receipt, binaries, modules, output)
        receipt["dependencies_after"] = runtime.verify_dependencies(context)
        receipt["dependencies_unchanged"] = receipt["dependencies_before"] == receipt["dependencies_after"]
        if not receipt["dependencies_unchanged"]:
            raise RuntimeError("dependency source identity changed during observation")
    receipt["sources_after"] = runtime.source_files()
    receipt["source_unchanged"] = receipt["sources_before"] == receipt["sources_after"]
    if not receipt["source_unchanged"]:
        raise RuntimeError("local source changed during observation")


if __name__ == "__main__":
    sys.exit(main())
