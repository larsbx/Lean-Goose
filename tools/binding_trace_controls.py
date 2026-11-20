"""Required native controls for the opt-in stored-binding diagnostic contract.

Fixtures are generated under the caller's temporary build directory. Evidence
retains actual process output, inline when small and losslessly gzipped when
large; fixture identities and generation code make large inputs reproducible
without checking multi-megabyte resource specimens into the repository.
"""
from __future__ import annotations

from datetime import datetime, timezone
import gzip
import hashlib
import json
import math
from pathlib import Path
import re
import subprocess
import time


CONTROL_COUNT = 26
TRACE_BYTES = 4 * 1024 * 1024
TRACE_NODES = 4096
TRACE_DEFINITIONS = 64
INLINE_BYTES = 32 * 1024
TIMEOUT_SECONDS = 30
HEADER = "lean-ocaml-benchmark-dag-v1\n"
BASE_NODES = [("s", 0), ("s", 1), ("s", 2), ("v", 0),
              ("c", "formal0"), ("c", "formal1")]
FATAL_OUTCOMES = {"Invalid_scope", "Height_limit", "Limit_exceeded"}
SEMANTIC_OUTCOMES = {"observed_success", "Unknown_constant", "Duplicate_definition",
                     "Expected_sort", "Expected_function", "Type_mismatch"}


def _require(condition: bool, message: str) -> None:
    # Gate validation must remain enabled when the Python interpreter uses -O.
    if not condition:
        raise ValueError(message)


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def _fixture_bytes(nodes: list[tuple], definitions: list[tuple]) -> bytes:
    rows = [HEADER.rstrip("\n")]
    rows.extend("\t".join(map(str, ("n", i, *fields))) for i, fields in enumerate(nodes))
    rows.extend("\t".join(map(str, ("d", *fields))) for fields in definitions)
    return ("\n".join(rows) + "\n").encode("ascii")


def _node_payload(fields: tuple) -> dict:
    tag, *values = fields
    result = {"tag": tag, "a": 0, "b": 0, "c": 0, "name": ""}
    if tag == "c":
        result["name"] = values[0]
    else:
        result.update(zip(("a", "b", "c"), values))
    return result


def _unique_object(pairs: list[tuple]) -> dict:
    result = {}
    for key, value in pairs:
        _require(key not in result, "native JSON contains a duplicate object key")
        result[key] = value
    return result


def _invalid_constant(value: str) -> None:
    raise ValueError(f"native JSON contains a non-JSON numeric constant: {value}")


def _one_json(data: bytes) -> dict:
    _require(data.endswith(b"\n") and data.count(b"\n") == 1,
             "native result must be exactly one JSON line ending with LF")
    result = json.loads(data.decode("utf-8"), object_pairs_hook=_unique_object,
                        parse_constant=_invalid_constant)
    _require(type(result) is dict, "native result must be a JSON object")
    return result


def _name(value: object) -> bool:
    return type(value) is str and re.fullmatch(r"[A-Za-z0-9_]+", value) is not None


def _same_payload(nodes: list[dict], left: int, right: int) -> bool:
    """Compare these controls' already-normal type DAGs without expanding sharing."""
    pending = [(left, right)]
    seen = set()
    while pending:
        pair = pending.pop()
        if pair in seen:
            continue
        seen.add(pair)
        a, b = (nodes[index] for index in pair)
        if a["tag"] != b["tag"]:
            return False
        tag = a["tag"]
        if tag in ("s", "v"):
            if a["a"] != b["a"]:
                return False
        elif tag == "c":
            if a["name"] != b["name"]:
                return False
        else:
            fields = ("a", "b", "c") if tag == "t" else ("a", "b")
            pending.extend((a[field], b[field]) for field in fields)
    return True


def _validate_trace(data: dict, raw: list[tuple], definitions: list[tuple],
                    outcomes: list[str], fatal: str | None) -> None:
    _require(set(data) == {"schema", "engine", "status", "steps", "success_observations",
                           "acceptance_authority"}, "trace envelope fields differ from v1")
    _require(data["schema"] == "lean-goose.binding-trace.v1" and data["engine"] == "goose-aot",
             "trace schema or engine differs from the native contract")
    _require(data["status"] == ("halted" if fatal else "traced"), "trace completion status differs")
    _require(data["acceptance_authority"] is False, "trace acquired acceptance authority")
    _require(type(data["success_observations"]) is int, "trace count must be an integer")
    steps = data["steps"]
    _require(type(steps) is list and len(steps) == len(outcomes), "trace processed the wrong prefix")
    _require(len(outcomes) <= len(definitions), "control expectation exceeds its definition inventory")
    if fatal:
        _require(fatal in FATAL_OUTCOMES and outcomes[-1] == fatal,
                 "control has an invalid fatal expectation")
    else:
        _require(len(outcomes) == len(definitions), "completed trace omitted a definition")
    previous_bindings: list[dict] = []
    previous_nodes = [_node_payload(fields) for fields in raw]
    successes = 0
    for index, step in enumerate(steps):
        _require(type(step) is dict and set(step) == {"name", "outcome", "bindings", "nodes"},
                 "trace step fields differ from v1")
        _require(step["name"] == definitions[index][0] and _name(step["name"]),
                 "trace changed a processed definition's name")
        _require(step["outcome"] == outcomes[index]
                 and step["outcome"] in SEMANTIC_OUTCOMES | FATAL_OUTCOMES,
                 "trace outcome differs from the registered control expectation")
        nodes, bindings = step["nodes"], step["bindings"]
        _require(type(nodes) is list and len(previous_nodes) <= len(nodes) <= TRACE_NODES,
                 "trace node arena has an invalid size")
        _require(nodes[:len(previous_nodes)] == previous_nodes,
                 "trace altered an imported or earlier immutable node payload")
        for node_id, node in enumerate(nodes):
            _require(type(node) is dict and set(node) == {"tag", "a", "b", "c", "name"},
                     "trace node payload has missing fields or leaked mutable metadata")
            _require(node["tag"] in ("s", "v", "c", "a", "l", "p", "t"),
                     "trace node has an unknown tag")
            _require(all(type(node[field]) is int and node[field] >= 0 for field in ("a", "b", "c")),
                     "trace node payloads must be nonnegative integers")
            _require(_name(node["name"]) if node["tag"] == "c" else node["name"] == "",
                     "trace node name differs from its tag's payload")
            if node["tag"] in ("a", "l", "p", "t"):
                fields = ("a", "b", "c") if node["tag"] == "t" else ("a", "b")
                _require(all(node[field] < node_id for field in fields),
                         "trace contains a forward, cyclic, or out-of-range child ID")
        _require(type(bindings) is list and bindings[:len(previous_bindings)] == previous_bindings,
                 "trace changed an earlier stored binding record")
        for binding in bindings:
            _require(type(binding) is dict and set(binding) == {"name", "type", "value", "inferred"},
                     "trace binding fields differ from v1")
            _require(_name(binding["name"]), "trace binding name is invalid")
            _require(all(type(binding[field]) is int and 0 <= binding[field] < len(nodes)
                         for field in ("type", "value", "inferred")),
                     "trace binding references an invalid node ID")
        _require(len({binding["name"] for binding in bindings}) == len(bindings),
                 "trace contains duplicate stored binding names")
        if step["outcome"] == "observed_success":
            successes += 1
            _require(len(bindings) == len(previous_bindings) + 1,
                     "successful insertion did not append exactly one binding")
            added = bindings[-1]
            name, ty, value = definitions[index]
            _require((added["name"], added["type"], added["value"]) == (name, ty, value),
                     "successful binding changed its original type or value IDs")
            _require(_same_payload(nodes, added["type"], added["inferred"]),
                     "stored inferred type differs from the control's declared normal type")
        else:
            _require(bindings == previous_bindings, "refused or fatal definition mutated stored bindings")
        previous_nodes, previous_bindings = nodes, bindings
    _require(data["success_observations"] == successes == len(previous_bindings),
             "trace success count differs from actual stored bindings")


class _Controls:
    def __init__(self, binary: Path, build: Path, output: Path):
        self.binary = binary.resolve()
        self.build = (build / "stored-native-controls").resolve()
        self.output = output.resolve()
        self.build.mkdir(parents=True, exist_ok=True)
        self.output.mkdir(parents=True, exist_ok=True)
        self.path = self.output / "stored-native-controls.json"
        self.started = time.monotonic()
        self.receipt = {
            "schema": "lean-goose.stored-native-controls.v1", "status": "running",
            "started_at_utc": _now(), "acceptance_authority": False,
            "binary": {"path": str(self.binary)},
            "generator_sha256": _sha256(Path(__file__).read_bytes()),
            "registered_control_count": CONTROL_COUNT, "timeout_seconds_per_command": TIMEOUT_SECONDS,
            "limits": {"input_bytes": TRACE_BYTES, "output_bytes_including_lf": TRACE_BYTES,
                       "input_and_derived_nodes": TRACE_NODES, "definitions": TRACE_DEFINITIONS},
            "fixture_storage": "temporary build directory; deterministic generator and hashes retained",
            "controls": [],
        }
        self.save()
        try:
            self.receipt["binary"]["sha256"] = _sha256(self.binary.read_bytes())
        except OSError as error:
            self.receipt.update(status="failed", finished_at_utc=_now(),
                                error={"type": type(error).__name__, "message": str(error)})
            self.save()
            raise
        self.save()

    def save(self) -> None:
        self.path.write_text(json.dumps(self.receipt, indent=2, ensure_ascii=True) + "\n")

    def stream(self, data: bytes, stem: str) -> dict:
        result = {"bytes": len(data), "sha256": _sha256(data), "retention": "complete"}
        if len(data) <= INLINE_BYTES:
            try:
                result.update(encoding="utf-8", text=data.decode("utf-8"))
                return result
            except UnicodeDecodeError:
                pass
        directory = self.output / "stored-native-control-streams"
        directory.mkdir(exist_ok=True)
        compressed = gzip.compress(data, mtime=0)
        path = directory / f"{stem}.gz"
        path.write_bytes(compressed)
        result.update(encoding="gzip", path=path.relative_to(self.output).as_posix(),
                      compressed_bytes=len(compressed), compressed_sha256=_sha256(compressed))
        return result

    def begin(self, name: str, data: bytes, expected: dict) -> tuple[Path, dict]:
        _require(not any(row["name"] == name for row in self.receipt["controls"]),
                 "duplicate native control name")
        path = self.build / f"{name}.dag"
        path.write_bytes(data)
        row = {"name": name, "status": "running", "expected": expected,
               "fixture": {"path": str(path), "bytes": len(data), "sha256": _sha256(data)},
               "commands": []}
        self.receipt["controls"].append(row)
        self.save()
        return path, row

    def run(self, row: dict, path: Path, mode: str) -> subprocess.CompletedProcess:
        command = ([str(self.binary), str(path), "1", "2"] if mode == "benchmark"
                   else [str(self.binary), mode, str(path)])
        entry = {"mode": mode, "command": command, "cwd": str(self.build), "started_at_utc": _now()}
        row["commands"].append(entry)
        self.save()
        started = time.monotonic()
        stem = f"{row['name']}-{mode.lstrip('-')}"
        try:
            result = subprocess.run(command, cwd=self.build, capture_output=True, timeout=TIMEOUT_SECONDS)
        except (OSError, subprocess.TimeoutExpired) as error:
            entry.update(exit_code=None, execution_error=type(error).__name__, error=str(error),
                         capture_complete=False,
                         stdout=self.stream(getattr(error, "stdout", None) or b"", stem + "-stdout"),
                         stderr=self.stream(getattr(error, "stderr", None) or b"", stem + "-stderr"))
            raise RuntimeError(f"{row['name']} {mode}: native command did not complete") from error
        else:
            entry.update(exit_code=result.returncode, capture_complete=True,
                         stdout=self.stream(result.stdout, stem + "-stdout"),
                         stderr=self.stream(result.stderr, stem + "-stderr"))
            return result
        finally:
            entry.update(finished_at_utc=_now(), elapsed_seconds=time.monotonic() - started)
            self.save()

    def complete(self, row: dict) -> None:
        row["status"] = "passed"
        self.save()

    def check(self, row: dict, path: Path, definitions: list[tuple], outcomes: list[str],
              fatal: str | None = None) -> None:
        result = self.run(row, path, "--check")
        if fatal:
            _require(result.returncode == 2 and result.stdout == b""
                     and result.stderr == f"goose bounded checker: {fatal}\n".encode(),
                     "ordinary check mode changed its fatal exit or emitted a completed receipt")
            return
        _require(result.returncode == 0 and result.stderr == b"", "ordinary check mode failed")
        data = _one_json(result.stdout)
        _require(type(data.get("success_observations")) is int
                 and data.get("acceptance_authority") is False,
                 "ordinary check mode count or authority has the wrong JSON type")
        expected = {"schema": "lean-goose.definition-observations.v1", "engine": "goose-aot",
                    "status": "checked", "outcomes": [
                        {"name": definition[0], "outcome": outcome}
                        for definition, outcome in zip(definitions, outcomes)],
                    "success_observations": outcomes.count("observed_success"), "acceptance_authority": False}
        _require(data == expected and len(definitions) == len(outcomes),
                 "ordinary check mode differs from its registered observation contract")

    def trace(self, name: str, nodes: list[tuple], definitions: list[tuple], outcomes: list[str],
              *, fatal: str | None = None, node_count: int | None = None,
              stdout_bytes: int | None = None, all_tags: bool = False) -> None:
        expected = {"trace_exit": 2 if fatal else 0, "trace_status": "halted" if fatal else "traced",
                    "outcomes": outcomes, "check_exit": 2 if fatal else 0}
        if node_count is not None:
            expected["final_node_count"] = node_count
        if stdout_bytes is not None:
            expected["trace_stdout_bytes"] = stdout_bytes
        path, row = self.begin(name, _fixture_bytes(nodes, definitions), expected)
        result = self.run(row, path, "--trace")
        _require(result.returncode == expected["trace_exit"], f"{name}: wrong trace exit code")
        _require(result.stderr == (f"goose bounded checker: {fatal}\n".encode() if fatal else b""),
                 f"{name}: unexpected trace diagnostic")
        _require(len(result.stdout) <= TRACE_BYTES, f"{name}: serialized trace exceeds its bound")
        data = _one_json(result.stdout)
        _validate_trace(data, nodes, definitions, outcomes, fatal)
        if node_count is not None:
            _require(len(data["steps"][-1]["nodes"]) == node_count, f"{name}: wrong arena boundary")
        if stdout_bytes is not None:
            _require(len(result.stdout) == stdout_bytes, f"{name}: wrong serialized byte boundary")
        if all_tags:
            _require({node["tag"] for node in data["steps"][0]["nodes"]} == set("svcalpt"),
                     "node export control did not cover every tag")
        row["observed"] = {"steps": len(data["steps"]), "final_nodes": len(data["steps"][-1]["nodes"]),
                           "success_observations": data["success_observations"],
                           "raw_binding_and_node_prefixes_preserved": True}
        self.check(row, path, definitions, outcomes, fatal)
        self.complete(row)

    def no_json(self, name: str, data: bytes, exit_code: int, stderr: str,
                *, check_exit: int | None = None, check_stderr: str | None = None,
                definitions: list[tuple] | None = None, outcomes: list[str] | None = None) -> None:
        expected = {"trace_exit": exit_code, "trace_stdout_bytes": 0, "trace_stderr": stderr,
                    "check_exit": check_exit if check_exit is not None else 0}
        path, row = self.begin(name, data, expected)
        trace = self.run(row, path, "--trace")
        _require(trace.returncode == exit_code and trace.stdout == b"" and trace.stderr == stderr.encode(),
                 f"{name}: expected an exact diagnostic failure without JSON")
        if check_exit is not None:
            check = self.run(row, path, "--check")
            _require(check.returncode == check_exit and check.stdout == b""
                     and check.stderr == (check_stderr or "").encode(),
                     f"{name}: ordinary check mode changed its failure contract")
        else:
            _require(definitions is not None and outcomes is not None,
                     f"{name}: missing ordinary-check expectations")
            self.check(row, path, definitions, outcomes)
        self.complete(row)


def _byte_boundary_nodes(extra: int) -> tuple[list[tuple], list[tuple]]:
    # This simple sort specimen stores two copies of the definition name and one
    # unused constant name in its trace. Size the latter so the complete JSON/LF
    # is exactly the declared output cap (or one byte over), while input fits.
    definition_name = "D" * (1024 * 1024)
    nodes = [("s", 0), ("s", 1), ("c", "C")]
    expected = {
        "schema": "lean-goose.binding-trace.v1", "engine": "goose-aot", "steps": [{
            "name": definition_name, "outcome": "observed_success", "bindings": [{
                "name": definition_name, "type": 1, "value": 0, "inferred": 4}],
            "nodes": [_node_payload(fields) for fields in nodes + [("s", 2), ("s", 1)]]}],
        "status": "traced", "success_observations": 1, "acceptance_authority": False,
    }
    base_size = len(json.dumps(expected, separators=(",", ":")).encode("ascii")) + 1
    nodes[2] = ("c", "C" * (1 + TRACE_BYTES + extra - base_size))
    return nodes, [(definition_name, 1, 0)]


def _exercise(c: _Controls) -> None:
    c.trace("good_alias", BASE_NODES, [("formal0", 1, 0), ("formal1", 1, 4)], ["observed_success"] * 2)
    c.trace("duplicate_preempts_scope", BASE_NODES, [("formal0", 1, 0), ("formal0", 1, 3)],
            ["observed_success", "Duplicate_definition"])
    c.trace("mismatch_then_retry", BASE_NODES, [("formal0", 1, 1), ("formal0", 1, 0)],
            ["Type_mismatch", "observed_success"])
    c.trace("unknown_then_good_then_alias", BASE_NODES,
            [("formal0", 1, 5), ("formal1", 1, 0), ("formal0", 1, 5)],
            ["Unknown_constant", "observed_success", "observed_success"])
    c.trace("wrong_level_alias", BASE_NODES, [("formal0", 2, 1), ("formal1", 1, 4)],
            ["observed_success", "Type_mismatch"])
    c.trace("typed_alias", BASE_NODES, [("formal0", 2, 1), ("formal1", 2, 4)], ["observed_success"] * 2)
    tags = BASE_NODES + [("a", 0, 0), ("l", 0, 3), ("p", 0, 0), ("t", 1, 0, 3)]
    c.trace("all_tags", tags, [("formal0", 1, 0)], ["observed_success"], all_tags=True)
    c.trace("expected_sort", tags, [("formal0", 7, 0)], ["Expected_sort"])
    c.trace("expected_function", tags, [("formal0", 1, 6)], ["Expected_function"])
    c.trace("scope_halts", BASE_NODES, [("formal0", 1, 0), ("formal1", 1, 3), ("later", 1, 0)],
            ["observed_success", "Invalid_scope"], fatal="Invalid_scope")

    # Input subterms satisfy the height bound; substitution combines their depths
    # during the first definition and triggers a real processed height failure.
    height = [("s", 0), ("s", 1)]
    value = 0
    for _ in range(70):
        height.append(("p", 0, value))
        value = len(height) - 1
    height.append(("v", 70))
    body = len(height) - 1
    for _ in range(70):
        height.append(("p", 0, body))
        body = len(height) - 1
    height.append(("t", 1, value, body))
    c.trace("derived_height_halts", height, [("height_case", 1, len(height) - 1), ("later", 1, 0)],
            ["Height_limit"], fatal="Height_limit")

    # Equality of two distinct shared Pi DAGs exhausts checker fuel without
    # approaching the diagnostic node/output bounds. The first binding succeeds.
    fuel = [("s", 0), ("s", 1)]
    left, value = 1, 0
    for _ in range(25):
        fuel.append(("l", left, value))
        value = len(fuel) - 1
        fuel.append(("p", left, left))
        left = len(fuel) - 1
    right = 1
    for _ in range(25):
        fuel.append(("p", right, right))
        right = len(fuel) - 1
    fuel.append(("c", "fuel_base"))
    c.trace("fuel_halts", fuel,
            [("fuel_base", left, value), ("fuel_case", right, len(fuel) - 1), ("later", 1, 0)],
            ["observed_success", "Limit_exceeded"], fatal="Limit_exceeded")

    imported = [("s", 0), ("s", 1)]
    previous = 0
    for _ in range(128):
        imported.append(("p", 0, previous))
        previous = len(imported) - 1
    height_error = "goose bounded checker: Height_limit\n"
    c.no_json("import_height_failure", _fixture_bytes(imported, [("unused", 1, 0)]), 2, height_error,
              check_exit=2, check_stderr=height_error)
    missing_lf = "goose benchmark parser: missing final LF\n"
    c.no_json("parser_failure", (HEADER + "n\t0\ts\t0\nd\tbad_name\t0\t0").encode(), 3, missing_lf,
              check_exit=3, check_stderr=missing_lf)
    bad_name = "goose benchmark parser: invalid constant name\n"
    c.no_json("invalid_name_parser_failure",
              _fixture_bytes([("s", 0), ("s", 1), ("c", 'quote"')], [("valid", 1, 0)]),
              3, bad_name, check_exit=3, check_stderr=bad_name)

    good = [("formal0", 1, 0)]
    c.no_json("input_nodes_limit", _fixture_bytes([("s", 0), ("s", 1)] + [("s", 0)] * 4095, good),
              2, "goose binding trace: input nodes exceed trace bound\n",
              definitions=good, outcomes=["observed_success"])
    repeated = [("same", 1, 0)] * 65
    c.no_json("definition_limit", _fixture_bytes([("s", 0), ("s", 1)], repeated),
              2, "goose binding trace: definitions exceed trace bound\n", definitions=repeated,
              outcomes=["observed_success"] + ["Duplicate_definition"] * 64)
    c.no_json("derived_nodes_limit", _fixture_bytes([("s", 0), ("s", 1)] + [("s", 0)] * 4094, good),
              2, "goose binding trace: derived nodes exceed trace bound\n",
              definitions=good, outcomes=["observed_success"])
    c.no_json("input_byte_limit", b"x" * (TRACE_BYTES + 1),
              2, "goose binding trace: input bytes exceed trace bound\n",
              check_exit=3, check_stderr=missing_lf)
    repeated = [("formal0", 1, 0)] * 64
    c.no_json("output_limit", _fixture_bytes([("s", 0), ("s", 1)] + [("s", 0)] * 4000, repeated),
              2, "goose binding trace: serialized output exceeds trace bound\n", definitions=repeated,
              outcomes=["observed_success"] + ["Duplicate_definition"] * 63)

    c.trace("node_boundary", [("s", 0), ("s", 1)] + [("s", 0)] * 4092, good,
            ["observed_success"], node_count=4096)
    c.trace("definition_boundary", [("s", 0), ("s", 1)], [("same", 1, 0)] * 64,
            ["observed_success"] + ["Duplicate_definition"] * 63)
    c.no_json("input_byte_boundary", b"x" * TRACE_BYTES, 3, missing_lf,
              check_exit=3, check_stderr=missing_lf)
    nodes, definitions = _byte_boundary_nodes(0)
    c.trace("output_byte_boundary", nodes, definitions, ["observed_success"], stdout_bytes=TRACE_BYTES)
    nodes, definitions = _byte_boundary_nodes(1)
    c.no_json("output_byte_over_boundary", _fixture_bytes(nodes, definitions),
              2, "goose binding trace: serialized output exceeds trace bound\n",
              definitions=definitions, outcomes=["observed_success"])

    path, row = c.begin("benchmark_mode", _fixture_bytes(BASE_NODES, [("formal0", 1, 0), ("formal1", 1, 4)]),
                        {"exit_code": 0, "schema": "lean-goose.benchmark-observation.v1", "iterations": 2})
    result = c.run(row, path, "benchmark")
    _require(result.returncode == 0 and result.stderr == b"", "benchmark mode failed")
    data = _one_json(result.stdout)
    _require(set(data) == {"schema", "engine", "status", "workers", "iterations", "definitions",
                           "elapsed_ns", "per_batch_ns", "validated_batches", "refusal_controls",
                           "acceptance_authority"}, "benchmark output fields changed")
    expected = {"schema": "lean-goose.benchmark-observation.v1", "engine": "goose-aot", "status": "passed",
                "workers": 1, "iterations": 2, "definitions": 2, "validated_batches": 2, "refusal_controls": 1}
    _require(all(data[key] == value and type(data[key]) is type(value) for key, value in expected.items())
             and data["acceptance_authority"] is False, "benchmark metadata changed")
    _require(type(data["elapsed_ns"]) is int and data["elapsed_ns"] > 0
             and type(data["per_batch_ns"]) in (int, float) and math.isfinite(data["per_batch_ns"])
             and math.isclose(data["per_batch_ns"], data["elapsed_ns"] / 2, rel_tol=1e-6),
             "benchmark timing is invalid")
    c.complete(row)


def run_controls(binary: Path, build: Path, output: Path) -> dict:
    """Execute required controls, retain real evidence, and raise on any failure."""
    controls = _Controls(binary, build, output)
    try:
        _exercise(controls)
        rows = controls.receipt["controls"]
        _require(len(rows) == CONTROL_COUNT and all(row["status"] == "passed" for row in rows),
                 "native controls did not complete their registered inventory")
        _require(_sha256(controls.binary.read_bytes()) == controls.receipt["binary"]["sha256"],
                 "native binary changed while controls were executing")
    except Exception as error:
        controls.receipt.update(status="failed", error={"type": type(error).__name__, "message": str(error)})
        for row in controls.receipt["controls"]:
            if row["status"] == "running":
                row["status"] = "failed"
        raise
    else:
        controls.receipt["status"] = "passed"
    finally:
        controls.receipt.update(finished_at_utc=_now(), elapsed_seconds=time.monotonic() - controls.started)
        controls.save()
    return {"status": "passed", "count": len(rows), "commands": sum(len(row["commands"]) for row in rows),
            "log": controls.path.name, "sha256": _sha256(controls.path.read_bytes()), "acceptance_authority": False}
