"""Finite transformation inputs and strict pure-model/native wire adapters.

Lean and Quint compute lifting, substitution, height, and scope. This adapter
generates raw fixtures, checks framing and original IDs, and matches the model's
result expression against the actual native result root. It implements none of
the transformations or their scope/height semantics.
"""
from __future__ import annotations

from copy import deepcopy
from itertools import product
import json
from typing import Any

import expression_dag_profile as dag

FINITE_GRAPH_COUNT = 84
FINITE_CASE_COUNT = 2520
NAMED_CASE_COUNT = 20
MALFORMED_CASE_COUNT = 6
CASE_COUNT = FINITE_CASE_COUNT + NAMED_CASE_COUNT + MALFORMED_CASE_COUNT
DEPTHS = tuple(range(7))
CHECK_FUEL = 10000000
TRACE_SCHEMA = "lean-goose.substitution-trace.v1"
MAX_TRACE_BYTES = dag.MAX_TRACE_BYTES
MAX_ARENA_NODES = dag.MAX_ARENA_NODES
MAX_WIRE_TOKENS = dag.MAX_WIRE_TOKENS
MAX_MODEL_LINE_BYTES = dag.MAX_MODEL_LINE_BYTES
PARSER_DIAGNOSTIC = dag.PARSER_DIAGNOSTIC
ERRORS = {7: "Limit_exceeded", 8: "Height_limit"}
_require = dag._require
_natural = dag._natural


def validate_request(request: Any, *, topology: bool = True) -> None:
    fields = {"nodes", "operation", "root", "parameter", "cutoff", "depths"}
    _require(type(request) is dict and set(request) == fields, "unknown transformation request fields")
    _require(type(request["depths"]) is list and request["depths"] == list(DEPTHS)
             and all(type(value) is int for value in request["depths"]),
             "transformation profile depths must be exactly 0..6")
    dag.validate_request({"nodes": request["nodes"], "depths": list(dag.DEPTHS)}, topology=topology)
    _require(request["nodes"] and type(request["operation"]) is int and request["operation"] in (0, 1),
             "transformation requires a nonempty raw DAG and an exact operation")
    _require(all(_natural(request[field]) for field in ("root", "parameter", "cutoff")),
             "transformation arguments must be exact natural numbers")
    _require(request["root"] < len(request["nodes"]), "transformation root outside raw arena")
    _require(request["operation"] == 0 or request["parameter"] < len(request["nodes"]),
             "replacement root outside raw arena")


def _case_request(case: dict) -> dict:
    _require(type(case) is dict and type(case.get("id")) is str and case["id"]
             and type(case.get("category")) is str and type(case.get("decoded")) is bool,
             "malformed transformation case identity")
    request = case.get("model_input")
    validate_request(request, topology=False)
    valid = dag._topology_valid(request["nodes"])
    _require(valid == case["decoded"], "case topology differs from its declared decoder expectation")
    if valid:
        dag._wire_bound(request)
    if "expected_result_id" in case:
        _require(valid and _natural(case["expected_result_id"])
                 and case["expected_result_id"] < len(request["nodes"]),
                 "invalid authored unchanged/replacement ID control")
    return request


def encode(case: dict) -> str:
    result = json.dumps(_case_request(case), sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    _require(len(result.encode()) <= MAX_MODEL_LINE_BYTES, "transformation input exceeds JSON-line bound")
    return result


def _validate_wire(wire: Any) -> None:
    """Validate prefix syntax only, without computing an expression or meaning."""
    _require(type(wire) is list and len(wire) <= MAX_WIRE_TOKENS
             and all(_natural(value) for value in wire), "result wire must contain bounded exact naturals")
    pending, position = 1, 0
    while pending:
        _require(position < len(wire), "truncated result expression wire")
        tag = wire[position]
        _require(tag in range(7), "unknown result expression wire tag")
        position += 1
        pending -= 1
        if tag in (0, 1):
            _require(position < len(wire), "truncated literal result wire")
            position += 1
        elif tag == 2:
            _require(position < len(wire), "truncated constant result wire")
            count = wire[position]
            position += 1
            name = wire[position:position + count]
            _require(len(name) == count and count > 0 and all(value < 128 for value in name)
                     and dag._name(bytes(name).decode("ascii")), "invalid result constant name bytes")
            position += count
        else:
            pending += 3 if tag == 6 else 2
    _require(position == len(wire), "trailing result expression wire payload")


def validate_model(row: Any, case: dict) -> None:
    _case_request(case)
    fields = {"decoded", "expressions", "heights", "loose", "scoped", "acceptance_authority"}
    _require(type(row) is dict and set(row) == fields and type(row["decoded"]) is bool
             and row["acceptance_authority"] is False, "unknown transformation model envelope or authority")
    _require(row["decoded"] == case["decoded"], "model accepted malformed topology or refused a valid DAG")
    arrays = ("expressions", "heights", "loose", "scoped")
    _require(all(type(row[field]) is list for field in arrays), "transformation result fields must be lists")
    if not row["decoded"]:
        _require(all(row[field] == [] for field in arrays), "topology refusal leaked a partial transformation")
        return
    _require(all(len(row[field]) == 1 for field in arrays), "transformation must return exactly one result root")
    _validate_wire(row["expressions"][0])
    _require(_natural(row["heights"][0]) and row["heights"][0] > 0 and _natural(row["loose"][0]),
             "height/loose fields must be exact natural numbers")
    _require(type(row["scoped"][0]) is list and len(row["scoped"][0]) == len(DEPTHS)
             and all(type(value) is bool for value in row["scoped"][0]),
             "transformed root scope row must contain exactly seven Booleans")


def decode_models(text: str, inventory: list[dict]) -> list[dict]:
    _require(type(text) is str and text.endswith("\n"), "transformation replay must end with LF")
    lines = text.splitlines()
    _require(len(lines) == len(inventory), "transformation replay omitted or added results")
    result = []
    for line, case in zip(lines, inventory):
        row = dag._json_object(line)
        validate_model(row, case)
        result.append(row)
    return result


def _case(identifier: str, nodes: list, operation: int, root: int, parameter: int, cutoff: int,
          *, category: str = "named", decoded: bool = True, expected_result_id: int | None = None) -> dict:
    result = {"id": identifier, "category": category, "decoded": decoded,
              "model_input": {"nodes": deepcopy(nodes), "operation": operation, "root": root,
                              "parameter": parameter, "cutoff": cutoff, "depths": list(DEPTHS)}}
    if expected_result_id is not None:
        result["expected_result_id"] = expected_result_id
    return result


def _raw(nodes: list[tuple]) -> list[list]:
    return [[tag, a, b, c, list(name)] for tag, a, b, c, name in dag._raw_nodes(nodes)]


def _named_cases() -> list[dict]:
    entries = [
        ("lift-nested-lambda", [("s", 0), ("v", 2), ("l", 0, 1), ("l", 0, 2)], 0, 3, 2, 0, None),
        ("lift-pi-domain-body", [("v", 0), ("v", 1), ("p", 0, 1)], 0, 2, 2, 0, None),
        ("lift-let-type-value-body", [("v", 0), ("v", 1), ("t", 0, 0, 1)], 0, 2, 2, 0, None),
        ("lift-shared-var0-context", [("s", 0), ("v", 0), ("l", 0, 1), ("a", 1, 2)], 0, 3, 1, 0, None),
        ("lift-shared-var1-context", [("s", 0), ("v", 1), ("l", 0, 1), ("a", 1, 2)], 0, 3, 2, 1, None),
        ("lift-zero-original-id", [("v", 0), ("v", 0)], 0, 1, 0, 0, 1),
        ("lift-high-cutoff-original-id", [("s", 0), ("v", 1), ("l", 0, 1)], 0, 2, 2, 3, 2),
        ("lift-name-payload", [("c", "Az_09"), ("v", 0), ("a", 0, 1)], 0, 2, 2, 0, None),
        ("substitute-lambda-capture", [("s", 0), ("v", 1), ("l", 0, 1), ("v", 0)], 1, 2, 3, 0, None),
        ("substitute-pi-capture", [("s", 0), ("v", 1), ("p", 0, 1), ("v", 0)], 1, 2, 3, 0, None),
        ("substitute-let-capture", [("s", 0), ("v", 1), ("t", 0, 0, 1), ("v", 0)], 1, 2, 3, 0, None),
        ("substitute-two-binders", [("s", 0), ("v", 2), ("l", 0, 1), ("l", 0, 2), ("v", 0)], 1, 3, 4, 0, None),
        ("substitute-three-binders", [("s", 0), ("v", 3), ("l", 0, 1), ("p", 0, 2),
                                       ("t", 0, 0, 3), ("v", 0)], 1, 4, 5, 0, None),
        ("substitute-shared-var0-context", [("s", 0), ("v", 0), ("l", 0, 1), ("a", 1, 2), ("v", 1)],
         1, 3, 4, 0, None),
        ("substitute-shared-var1-context", [("s", 0), ("v", 1), ("l", 0, 1), ("a", 1, 2), ("v", 0)],
         1, 3, 4, 0, None),
        ("substitute-compound-app", [("s", 0), ("v", 1), ("l", 0, 1), ("v", 0),
                                    ("c", "Az_09"), ("a", 3, 4)], 1, 2, 5, 0, None),
        ("substitute-compound-lambda", [("s", 0), ("v", 1), ("l", 0, 1), ("v", 0),
                                       ("a", 3, 1), ("l", 0, 4)], 1, 2, 5, 0, None),
        ("substitute-compound-pi", [("s", 0), ("v", 1), ("l", 0, 1), ("v", 0), ("p", 3, 1)],
         1, 2, 4, 0, None),
        ("substitute-compound-let", [("s", 0), ("v", 1), ("l", 0, 1), ("v", 0), ("t", 3, 3, 1)],
         1, 2, 4, 0, None),
        ("substitute-original-replacement-id", [("v", 0), ("v", 2), ("v", 2)], 1, 0, 2, 0, 2),
    ]
    return [_case(name, _raw(nodes), op, root, parameter, cutoff, expected_result_id=result_id)
            for name, nodes, op, root, parameter, cutoff, result_id in entries]


def cases() -> list[dict]:
    leaves = [[0, 0, 0, 0, []], [0, 1, 0, 0, []]] + [[1, i, 0, 0, []] for i in range(4)] \
             + [[2, 0, 0, 0, list(b"missing")]]

    def options(index: int) -> list[list]:
        return leaves + [[tag, a, b, 0, []] for tag in (3, 4, 5) for a, b in product(range(index), repeat=2)] \
               + [[6, a, b, c, []] for a, b, c in product(range(index), repeat=3)]

    result, graph_count = [], 0
    for size in (1, 2):
        for graph in product(*(options(index) for index in range(size))):
            nodes = list(graph)
            for amount, cutoff in product(range(3), repeat=2):
                result.append(_case(f"finite-lift-{graph_count:02d}-a{amount}-c{cutoff}", nodes, 0,
                                    size - 1, amount, cutoff, category="finite"))
            for replacement, leaf in enumerate(leaves):
                for cutoff in range(3):
                    result.append(_case(f"finite-substitute-{graph_count:02d}-r{replacement}-c{cutoff}",
                                        nodes + [leaf], 1, size - 1, size, cutoff, category="finite"))
            graph_count += 1
    _require(graph_count == FINITE_GRAPH_COUNT and len(result) == FINITE_CASE_COUNT,
             "finite transformation graph/operation inventory changed")
    result.extend(_named_cases())
    for operation in (0, 1):
        for kind, target in (("self", 1), ("forward", 2), ("missing", 3)):
            result.append(_case(f"topology-{operation}-{kind}", _raw([("s", 0), ("a", target, 0), ("s", 1)]),
                                operation, 1, 0, 0, category="malformed", decoded=False))
    _require(len(result) == CASE_COUNT and len({case["id"] for case in result}) == CASE_COUNT,
             "transformation case identity inventory changed")
    return result


def fixture(nodes: list[list], definitions: list[dict] | None = None) -> str:
    """Lossless raw serialization; deliberately invalid control edges remain invalid."""
    if definitions is None:
        definitions = [{"name": "transformation", "type": 0, "value": 0}]
    rows = ["lean-ocaml-benchmark-dag-v1"]
    for index, (tag, a, b, c, name) in enumerate(nodes):
        payload = [a] if tag in (0, 1) else [bytes(name).decode("ascii")] if tag == 2 \
                  else [a, b, c] if tag == 6 else [a, b]
        rows.append("\t".join(map(str, ("n", index, dag.TAGS[tag], *payload))))
    rows.extend("\t".join(map(str, ("d", d["name"], d["type"], d["value"]))) for d in definitions)
    return "\n".join(rows) + "\n"


def native_fixture(case: dict) -> str:
    return fixture(_case_request(case)["nodes"])


def native_arguments(case: dict) -> list[str]:
    """Place fixture after item zero: [binary, args[0], fixture, *args[1:]]."""
    request = _case_request(case)
    return ["--lift" if request["operation"] == 0 else "--substitute",
            str(request["root"]), str(request["parameter"]), str(request["cutoff"])]


def _native_trace(case: dict, exit_code: int, stdout: str, stderr: str, *, error: int = 0,
                  fuel_budget: int = CHECK_FUEL) -> tuple[dict, list[list]]:
    request = _case_request(case)
    halted = error != 0
    _require(error == 0 or error in ERRORS, "unsupported transformation execution refusal")
    diagnostic = f"goose bounded checker: {ERRORS[error]}\n" if halted else ""
    _require(type(exit_code) is int and exit_code == (2 if halted else 0) and stderr == diagnostic,
             "native transformation process status differs from its expected computation/resource outcome")
    _require(type(stdout) is str and stdout.endswith("\n") and stdout.count("\n") == 1
             and len(stdout.encode()) <= MAX_TRACE_BYTES, "native transformation must emit one bounded JSON line")
    trace = dag._json_object(stdout)
    fields = {"schema", "engine", "status", "operation", "root", "parameter", "cutoff", "fuel_budget",
              "result", "error", "snapshot", "acceptance_authority"}
    _require(set(trace) == fields and trace["schema"] == TRACE_SCHEMA and trace["engine"] == "goose-aot"
             and trace["status"] == ("halted" if halted else "transformed")
             and trace["operation"] == ("lift" if request["operation"] == 0 else "substitute")
             and trace["acceptance_authority"] is False, "unknown native transformation envelope or authority")
    for key in ("root", "parameter", "cutoff"):
        _require(_natural(trace[key]) and trace[key] == request[key], "native operation changed an original argument/ID")
    _require(type(trace["error"]) is int and trace["error"] == error and _natural(trace["fuel_budget"])
             and trace["fuel_budget"] == fuel_budget, "native transformation error or operation fuel changed")
    snapshot = trace["snapshot"]
    _require(type(snapshot) is dict and set(snapshot) == {"name", "outcome", "nodes", "bindings"}
             and snapshot["name"] == "transformation"
             and snapshot["outcome"] == (ERRORS[error] if halted else "observed_success")
             and type(snapshot["bindings"]) is list and snapshot["bindings"] == [],
             "transformation snapshot performed definition insertion or changed its operation identity")
    nodes = dag._arena_request(snapshot["nodes"])["nodes"]
    _require(nodes[:len(request["nodes"])] == request["nodes"],
             "native transformation changed an imported/unused node payload or original raw ID")
    if halted:
        _require(trace["result"] is None, "resource failure exposed a sentinel node as a pure-model result")
    else:
        _require(_natural(trace["result"]) and trace["result"] < len(nodes), "native result ID is not in the raw arena")
        if "expected_result_id" in case:
            _require(trace["result"] == case["expected_result_id"], "native unchanged/replacement root ID changed")
    return trace, nodes


def check_native(case: dict, prediction: dict, exit_code: int, stdout: str, stderr: str) -> dict:
    validate_model(prediction, case)
    if not case["decoded"]:
        _require(type(exit_code) is int and exit_code == 3 and stdout == "" and stderr == PARSER_DIAGNOSTIC,
                 "malformed topology did not produce exact native parser refusal with empty stdout")
        return {"id": case["id"], "status": "parser_refused", "trace": None,
                "result_wire_matched": False, "input_prefix_preserved": False, "acceptance_authority": False}
    trace, nodes = _native_trace(case, exit_code, stdout, stderr)
    dag._wire_matches(nodes, trace["result"], prediction["expressions"][0])
    return {"id": case["id"], "status": "transformed", "trace": trace, "node_payloads": len(nodes),
            "input_prefix_preserved": True, "result_wire_matched": True, "acceptance_authority": False}


def native_controls() -> list[dict]:
    """Parser/import/envelope/fuel boundaries, distinct from pure model results."""
    result = []
    seed = _case("seed", _raw([("v", 0)]), 0, 0, 1, 0, category="control")

    def add(identifier: str, category: str, *, case: dict = seed, text: str | None = None,
            args: list[str] | None = None, exit_code: int = 3, message: str,
            envelope: bool = False, error: int = 0, fuel_budget: int = CHECK_FUEL) -> None:
        result.append({"id": identifier, "category": category, "fixture": native_fixture(case) if text is None else text,
                       "args": native_arguments(case) if args is None else args, "exit_code": exit_code,
                       "stderr": message, "envelope": envelope, "error": error, "fuel_budget": fuel_budget,
                       "case": deepcopy(case)})

    parser = "goose benchmark parser: "
    add("parser-operation", "parser", args=["--unknown", "0", "1", "0"], message=parser + "unknown transformation operation\n")
    add("parser-root", "parser", args=["--lift", "1", "1", "0"], message=parser + "transformation root outside arena\n")
    add("parser-replacement", "parser", args=["--substitute", "0", "1", "0"], message=parser + "replacement root outside arena\n")
    add("parser-sentinel", "parser", text=native_fixture(seed).replace("d\ttransformation", "d\tdifferent"),
        message=parser + "invalid transformation sentinel\n")
    add("parser-final-lf", "parser", text=native_fixture(seed)[:-1], message=parser + "missing final LF\n")
    add("parser-negative-cutoff", "parser", args=["--lift", "0", "1", "-1"], message=parser + "invalid natural\n")
    for name, budget in (("operation-fuel-zero", 0), ("operation-fuel-allocation", 1)):
        add(name, "operation_resource", args=native_arguments(seed) + [str(budget)], exit_code=2,
            message="goose bounded checker: Limit_exceeded\n", envelope=True, error=7, fuel_budget=budget)
    overflow = _case("overflow", _raw([("v", 1000000)]), 0, 0, 1, 0, category="control")
    add("operation-lift-index-limit", "operation_resource", case=overflow, exit_code=2,
        message="goose bounded checker: Limit_exceeded\n", envelope=True, error=7)
    capture = _case("capture-overflow", _raw([("s", 0), ("v", 1), ("l", 0, 1), ("v", 1000000)]),
                    1, 2, 3, 0, category="control")
    add("operation-capture-lift-index-limit", "operation_resource", case=capture, exit_code=2,
        message="goose bounded checker: Limit_exceeded\n", envelope=True, error=7)
    # Both roots import at legal heights; substitution creates height 129.
    height_nodes = _raw([("s", 0), ("v", 0), ("a", 0, 1)])
    for _ in range(127):
        height_nodes.append([3, 0, len(height_nodes) - 1 if len(height_nodes) > 3 else 0, 0, []])
    height = _case("derived-height", height_nodes, 1, 2, len(height_nodes) - 1, 0, category="control")
    add("operation-result-height", "operation_resource", case=height, exit_code=2,
        message="goose bounded checker: Height_limit\n", envelope=True, error=8)
    imported = _raw([("s", 0)])
    for _ in range(128):
        imported.append([3, 0, len(imported) - 1, 0, []])
    add("import-height", "import_resource", text=fixture(imported), args=["--lift", "0", "0", "0"],
        exit_code=2, message="goose bounded checker: Height_limit\n")
    too_many = _raw([("v", 0)] * (MAX_ARENA_NODES + 1))
    add("envelope-input-nodes", "envelope", text=fixture(too_many), exit_code=2,
        message="goose binding trace: input nodes exceed trace bound\n")
    full = _raw([("v", 0)] * MAX_ARENA_NODES)
    add("envelope-derived-nodes", "envelope", text=fixture(full), exit_code=2,
        message="goose binding trace: derived nodes exceed trace bound\n")
    return result


def check_control(control: dict, exit_code: int, stdout: str, stderr: str) -> dict:
    _require(type(exit_code) is int and exit_code == control["exit_code"] and stderr == control["stderr"],
             "native parser/resource control changed its designated process refusal")
    trace = None
    if control["envelope"]:
        trace, _ = _native_trace(control["case"], exit_code, stdout, stderr,
                                 error=control["error"], fuel_budget=control["fuel_budget"])
    else:
        _require(stdout == "", "parser/import/envelope refusal emitted a partial or completed result")
    return {"id": control["id"], "category": control["category"], "status": "passed", "trace": trace,
            "pure_model_result": False, "acceptance_authority": False}


def ordinary_controls() -> list[dict]:
    """Definition checking exercises beta/zeta capture and malformed scope."""
    selected = {"application_beta", "let_nested_capture", "lambda_domain_open", "pi_domain_open",
                "let_type_open", "let_value_open", "let_body_var1_open"}
    result = []
    for case in dag._named_cases():
        if case["id"].removeprefix("named-") in selected:
            result.append({"id": "ordinary-" + case["id"].removeprefix("named-"),
                           "fixture": dag.native_fixture(case), "nodes": case["model_input"]["nodes"],
                           "definitions": case["definitions"], "outcomes": case["outcomes"]})
    nodes = _raw([("s", 0), ("s", 1), ("s", 2), ("v", 0), ("v", 1), ("l", 1, 4),
                  ("l", 1, 5), ("a", 6, 3), ("l", 1, 7), ("p", 1, 1), ("p", 1, 9)])
    definitions = [{"name": "beta_capture", "type": 10, "value": 8}]
    result.append({"id": "ordinary-open-beta-capture", "fixture": fixture(nodes, definitions), "nodes": nodes,
                   "definitions": definitions, "outcomes": ["observed_success"]})
    return result


def check_ordinary(control: dict, mode: str, exit_code: int, stdout: str, stderr: str) -> dict:
    """Validate fixed typing controls without calculating typing or reduction."""
    _require(mode in ("--check", "--trace"), "unknown ordinary control mode")
    halted = control["outcomes"][-1] == "Invalid_scope"
    _require(type(exit_code) is int and exit_code == (2 if halted else 0)
             and stderr == (dag.SCOPE_DIAGNOSTIC if halted else ""), "ordinary control process outcome changed")
    if mode == "--check" and halted:
        _require(stdout == "", "ordinary scope failure emitted a completed receipt")
        return {"id": control["id"], "mode": mode, "status": "passed", "completed_receipt": False,
                "acceptance_authority": False}
    _require(type(stdout) is str and stdout.endswith("\n") and stdout.count("\n") == 1,
             "ordinary control output must be one JSON line")
    data = dag._json_object(stdout)
    successes = sum(value == "observed_success" for value in control["outcomes"])
    if mode == "--check":
        expected = {"schema": "lean-goose.definition-observations.v1", "engine": "goose-aot", "status": "checked",
                    "outcomes": [{"name": definition["name"], "outcome": outcome}
                                 for definition, outcome in zip(control["definitions"], control["outcomes"])],
                    "success_observations": successes, "acceptance_authority": False}
        _require(_natural(data.get("success_observations")) and data.get("acceptance_authority") is False
                 and data == expected, "ordinary completed control receipt changed")
    else:
        _require(set(data) == {"schema", "engine", "status", "steps", "success_observations", "acceptance_authority"}
                 and data["schema"] == dag.TRACE_SCHEMA and data["engine"] == "goose-aot"
                 and data["status"] == ("halted" if halted else "traced") and data["acceptance_authority"] is False
                 and _natural(data["success_observations"]) and data["success_observations"] == successes
                 and type(data["steps"]) is list and len(data["steps"]) == len(control["outcomes"]),
                 "ordinary trace control envelope changed")
        previous, bindings = control["nodes"], []
        for step, definition, outcome in zip(data["steps"], control["definitions"], control["outcomes"]):
            _require(type(step) is dict and set(step) == {"name", "outcome", "nodes", "bindings"}
                     and step["name"] == definition["name"] and step["outcome"] == outcome,
                     "ordinary trace definition or outcome changed")
            nodes = dag._arena_request(step["nodes"])["nodes"]
            _require(nodes[:len(previous)] == previous, "ordinary trace changed original/previous raw payload IDs")
            dag._bindings(step["bindings"], len(nodes))
            if outcome == "observed_success":
                _require(len(step["bindings"]) == len(bindings) + 1 and step["bindings"][:-1] == bindings
                         and all(step["bindings"][-1][field] == definition[field] for field in ("name", "type", "value")),
                         "ordinary trace changed inserted or previous raw binding IDs")
            else:
                _require(step["bindings"] == bindings, "ordinary trace refusal changed the environment")
            previous, bindings = nodes, step["bindings"]
    return {"id": control["id"], "mode": mode, "status": "passed", "completed_receipt": not halted,
            "observation": data, "acceptance_authority": False}
