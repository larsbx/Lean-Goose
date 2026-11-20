"""Structural DAG inputs and strict model/native correspondence adapters.

Lean and Quint compute height, loose-variable requirements, and scope. Python
generates fixtures and validates lossless framing, topology, payloads, and raw
ID preservation. It implements neither expression typing nor scope prediction.
"""
from __future__ import annotations

from copy import deepcopy
from itertools import product
import json
import re
from typing import Any


CASE_COUNT = 2208
FINITE_CASE_COUNT = 2163
MALFORMED_CASE_COUNT = 27
NAMED_CASE_COUNT = 17
PROBE_COUNT = 8696
NATIVE_COMMAND_COUNT = 8740
DEPTHS = (0, 1, 2, 3)
MAX_ARENA_NODES = 4096
MAX_WIRE_TOKENS = 262144
MAX_MODEL_LINE_BYTES = 4194304
MAX_TRACE_BYTES = 4194304
TAGS = ("s", "v", "c", "a", "l", "p", "t")
NAME = re.compile(r"[A-Za-z0-9_]+")
TRACE_SCHEMA = "lean-goose.binding-trace.v1"
PARSER_DIAGNOSTIC = "goose benchmark parser: node reference must precede its use\n"
SCOPE_DIAGNOSTIC = "goose bounded checker: Invalid_scope\n"
CLOSED_OUTCOMES = {"observed_success", "Unknown_constant", "Expected_sort",
                   "Expected_function", "Type_mismatch"}
ALL_OUTCOMES = CLOSED_OUTCOMES | {"Duplicate_definition", "Invalid_scope"}


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _natural(value: Any) -> bool:
    return type(value) is int and value >= 0


def _children(node: list) -> tuple[int, ...]:
    return tuple(node[1:4] if node[0] == 6 else node[1:3] if node[0] in (3, 4, 5) else ())


def _name(value: Any) -> bool:
    return type(value) is str and NAME.fullmatch(value) is not None


def validate_request(request: Any, *, topology: bool = True) -> None:
    """Validate canonical raw fields; optionally permit deliberately bad edges."""
    _require(type(request) is dict and set(request) == {"nodes", "depths"}, "unknown model input fields")
    _require(type(request["depths"]) is list and request["depths"] == list(DEPTHS)
             and all(type(depth) is int for depth in request["depths"]), "model depths must be exactly 0..3")
    nodes = request["nodes"]
    _require(type(nodes) is list and len(nodes) <= MAX_ARENA_NODES, "raw DAG exceeds the structural arena bound")
    for index, node in enumerate(nodes):
        _require(type(node) is list and len(node) == 5 and type(node[0]) is int and 0 <= node[0] <= 6,
                 "malformed raw node tag or record")
        tag, a, b, c, name = node
        _require(all(_natural(value) for value in (a, b, c)) and type(name) is list,
                 "raw numeric fields must be exact natural numbers")
        _require(all(type(code) is int and 0 <= code < 128 for code in name),
                 "constant names must be exact ASCII byte vectors")
        if tag == 2:
            _require(a == b == c == 0 and _name(bytes(name).decode("ascii")),
                     "constant payload has an invalid name or nonzero unused fields")
        else:
            _require(name == [] and (tag == 6 or c == 0) and (tag not in (0, 1) or b == 0),
                     "raw node has unexpected unused fields")
        if topology:
            _require(all(child < index for child in _children(node)),
                     "raw DAG contains a forward, self, or missing child reference")


def _topology_valid(nodes: list[list]) -> bool:
    return all(child < index for index, node in enumerate(nodes) for child in _children(node))


def _wire_bound(request: dict) -> None:
    """Bound only serialized expansion size, never height or variable scope."""
    lengths = []
    total = 0
    for node in request["nodes"]:
        if node[0] in (0, 1):
            length = 2
        elif node[0] == 2:
            length = 2 + len(node[4])
        else:
            length = 1 + sum(lengths[child] for child in _children(node))
        total += length
        _require(total <= MAX_WIRE_TOKENS, "structural prefix-wire expansion exceeds the replay bound")
        lengths.append(length)


def _case_request(case: dict) -> dict:
    _require(type(case) is dict and type(case.get("id")) is str and type(case.get("decoded")) is bool,
             "malformed expression case identity")
    request = case.get("model_input")
    validate_request(request, topology=False)
    valid = _topology_valid(request["nodes"])
    _require(valid == case["decoded"], "case topology differs from its declared decoder expectation")
    if valid:
        _wire_bound(request)
    return request


def encode(case: dict) -> str:
    request = _case_request(case)
    result = json.dumps(request, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    _require(len(result.encode()) <= MAX_MODEL_LINE_BYTES, "model input exceeds the JSON-line bound")
    return result


def _unique_object(pairs: list[tuple]) -> dict:
    result = {}
    for key, value in pairs:
        _require(key not in result, "duplicate JSON object key")
        result[key] = value
    return result


def _bad_constant(value: str) -> None:
    raise ValueError(f"non-JSON numeric constant: {value}")


def _json_object(text: str) -> dict:
    _require(type(text) is str and len(text.encode()) <= MAX_MODEL_LINE_BYTES, "model/native JSON line exceeds bound")
    result = json.loads(text, object_pairs_hook=_unique_object, parse_constant=_bad_constant)
    _require(type(result) is dict, "expected one JSON object")
    return result


def _wire_matches(nodes: list[list], root: int, wire: Any) -> None:
    _require(type(wire) is list and len(wire) <= MAX_WIRE_TOKENS and all(_natural(item) for item in wire),
             "expression wire must contain only bounded exact natural-number payloads")
    pending, position = [root], 0
    while pending:
        node = nodes[pending.pop()]
        if node[0] in (0, 1):
            prefix = node[:2]
        elif node[0] == 2:
            prefix = [2, len(node[4]), *node[4]]
        else:
            prefix = [node[0]]
        _require(wire[position:position + len(prefix)] == prefix,
                 "decoded wire changed a node tag, literal, name byte, child order, or sharing payload")
        position += len(prefix)
        pending.extend(reversed(_children(node)))
    _require(position == len(wire), "decoded wire contains trailing structural payload")


def validate_model(row: Any, case: dict) -> None:
    request = _case_request(case)
    fields = {"decoded", "expressions", "heights", "loose", "scoped", "acceptance_authority"}
    _require(type(row) is dict and set(row) == fields and type(row["decoded"]) is bool
             and row["acceptance_authority"] is False, "unknown expression model result or authority")
    _require(row["decoded"] == case["decoded"], "model accepted invalid topology or refused a valid raw DAG")
    arrays = ("expressions", "heights", "loose", "scoped")
    _require(all(type(row[field]) is list for field in arrays), "model payload fields must be lists")
    if not row["decoded"]:
        _require(all(row[field] == [] for field in arrays), "rejected topology leaked a partial decoded arena")
        return
    nodes = request["nodes"]
    _require(all(len(row[field]) == len(nodes) for field in arrays), "model omitted or added a decoded node")
    _require(all(_natural(value) and value > 0 for value in row["heights"])
             and all(_natural(value) for value in row["loose"]), "height/loose fields must be exact natural numbers")
    _require(all(type(scoped) is list and len(scoped) == len(DEPTHS)
                 and all(type(value) is bool for value in scoped) for scoped in row["scoped"]),
             "scope matrix must contain exactly four Boolean depths per node")
    _require(sum(len(wire) for wire in row["expressions"] if type(wire) is list) <= MAX_WIRE_TOKENS,
             "model expression wires exceed their total expansion bound")
    for index, wire in enumerate(row["expressions"]):
        _wire_matches(nodes, index, wire)


def decode_models(text: str, inventory: list[dict]) -> list[dict]:
    _require(type(text) is str and text.endswith("\n"), "model replay must end with LF")
    lines = text.splitlines()
    _require(len(lines) == len(inventory), "model replay returned missing or additional results")
    result = []
    for line, case in zip(lines, inventory):
        row = _json_object(line)
        validate_model(row, case)
        result.append(row)
    return result


def _request(nodes: list[tuple] | tuple[tuple, ...]) -> dict:
    return {"nodes": [[tag, a, b, c, list(name)] for tag, a, b, c, name in nodes], "depths": list(DEPTHS)}


def _raw_nodes(nodes: list[tuple]) -> list[tuple]:
    result = []
    for tag, *values in nodes:
        numeric = [0, 0, 0]
        name = ()
        if tag == "c":
            name = tuple(values[0].encode("ascii"))
        else:
            numeric[:len(values)] = values
        result.append((TAGS.index(tag), *numeric, name))
    return result


def _named_cases() -> list[dict]:
    base = [("s", 0), ("s", 1), ("v", 0)]
    entries = [
        ("identity_shared_var", base + [("p", 0, 0), ("l", 0, 2)],
         [("identity", 3, 4), ("naked", 1, 2)], ["observed_success", "Invalid_scope"]),
        ("dependent_identity_shared_var", base + [("v", 1), ("p", 2, 3), ("p", 1, 4), ("l", 2, 2), ("l", 1, 6)],
         [("dependent", 5, 7)], ["observed_success"]),
        ("nested_var1", base + [("v", 1), ("p", 0, 0), ("p", 0, 4), ("l", 0, 3), ("l", 0, 6)],
         [("nested", 5, 7)], ["observed_success"]),
        ("application_beta", base + [("p", 1, 1), ("l", 1, 2), ("a", 4, 0)],
         [("applied", 1, 5)], ["observed_success"]),
        ("pi_body_binder", base + [("p", 0, 2)], [("pi_body", 0, 3)], ["observed_success"]),
        ("let_body_binder", base + [("t", 1, 0, 2)], [("let_body", 1, 3)], ["observed_success"]),
        ("let_nested_capture", base + [("v", 1), ("p", 1, 1), ("l", 1, 3), ("t", 1, 0, 5)],
         [("let_nested", 4, 6)], ["observed_success"]),
        ("lambda_domain_open", base + [("l", 2, 2)], [("open_lambda", 1, 3)], ["Invalid_scope"]),
        ("pi_domain_open", base + [("p", 2, 2)], [("open_pi", 1, 3)], ["Invalid_scope"]),
        ("let_type_open", base + [("t", 2, 0, 2)], [("open_let_type", 1, 3)], ["Invalid_scope"]),
        ("let_value_open", base + [("t", 1, 2, 2)], [("open_let_value", 1, 3)], ["Invalid_scope"]),
        ("let_body_var1_open", base + [("v", 1), ("t", 1, 0, 3)],
         [("open_let_body", 1, 4)], ["Invalid_scope"]),
        ("scope_preempts_unknown", base + [("c", "missing"), ("a", 3, 2)],
         [("scope_first", 1, 4)], ["Invalid_scope"]),
        ("duplicate_preempts_open", base + [("c", "missing"), ("a", 3, 2)],
         [("same", 1, 0), ("same", 1, 4)], ["observed_success", "Duplicate_definition"]),
        ("transparent_constant_payload", base + [("c", "expr0")],
         [("expr0", 1, 0), ("alias", 1, 3)], ["observed_success", "observed_success"]),
        ("scope_depth_three", base + [("v", 2), ("p", 1, 1), ("p", 1, 4), ("p", 1, 5),
                                       ("l", 1, 3), ("l", 1, 7), ("l", 1, 8)],
         [("depth_three", 6, 9)], ["observed_success"]),
        ("binding_type_open", base, [("open_type", 2, 0)], ["Invalid_scope"]),
    ]
    return [{"id": "named-" + name, "category": "named", "model_input": _request(_raw_nodes(nodes)),
             "decoded": True, "root": definitions[-1][2],
             "definitions": [{"name": name, "type": ty, "value": value} for name, ty, value in definitions],
             "outcomes": outcomes} for name, nodes, definitions, outcomes in entries]


def cases() -> list[dict]:
    leaves = [(0, 0, 0, 0, ()), (0, 1, 0, 0, ())] + [(1, i, 0, 0, ()) for i in range(4)] \
             + [(2, 0, 0, 0, tuple(b"missing"))]

    def options(index: int) -> list[tuple]:
        return leaves + [(tag, a, b, 0, ()) for tag in (3, 4, 5) for a, b in product(range(index), repeat=2)] \
               + [(6, a, b, c, ()) for a, b, c in product(range(index), repeat=3)]

    result = []
    for size in (1, 2, 3):
        for nodes in product(*(options(index) for index in range(size))):
            result.append({"id": f"finite-{len(result):04d}", "category": "finite",
                           "model_input": _request(nodes), "decoded": True, "root": size - 1})
    _require(len(result) == FINITE_CASE_COUNT, "finite raw DAG inventory changed")
    result.append({"id": "empty", "category": "empty", "model_input": _request([]),
                   "decoded": True, "root": None})
    for tag in (3, 4, 5, 6):
        for slot in range(1, 4 if tag == 6 else 3):
            for kind, target in (("self", 1), ("forward", 2), ("missing", 3)):
                node = [tag, 0, 0, 0, ()]
                node[slot] = target
                result.append({"id": f"topology-{TAGS[tag]}-{'abc'[slot - 1]}-{kind}", "category": "malformed",
                               "model_input": _request([(0, 0, 0, 0, ()), tuple(node), (0, 1, 0, 0, ())]),
                               "decoded": False, "root": 1})
    result.extend(_named_cases())
    _require(len(result) == CASE_COUNT and len({case["id"] for case in result}) == CASE_COUNT,
             "expression profile identity inventory changed")
    return result


def probes(inventory: list[dict]) -> list[dict]:
    result = []
    _require(len({case["id"] for case in inventory}) == len(inventory), "duplicate expression case identity")
    for index, case in enumerate(inventory):
        _case_request(case)
        category = case.get("category")
        if category == "finite":
            result.extend({"id": f"{case['id']}-d{depth}", "case_index": index, "depth": depth, "check": False}
                          for depth in DEPTHS)
        elif category in ("named", "malformed"):
            result.append({"id": case["id"], "case_index": index, "depth": None, "check": True})
        else:
            _require(category == "empty", "unknown initial expression case category")
    return result


def _fixture_spec(case: dict, depth: int | None) -> tuple[list[list], list[dict]]:
    request = _case_request(case)
    nodes = deepcopy(request["nodes"])
    category = case.get("category")
    if category == "finite":
        _require(type(depth) is int and depth in DEPTHS and type(case.get("root")) is int
                 and case["root"] == len(nodes) - 1 and nodes,
                 "invalid finite root or binder-depth probe")
        root, sort0 = case["root"], len(nodes)
        nodes.extend([[0, 0, 0, 0, []], [0, 1, 0, 0, []]])
        for _ in range(depth):
            nodes.append([4, sort0, root, 0, []])
            root = len(nodes) - 1
        definitions = [{"name": "dag_seed", "type": sort0 + 1, "value": sort0},
                       {"name": "dag_probe", "type": sort0 + 1, "value": root}]
    elif category == "named":
        _require(depth is None, "named controls do not take an additional binder depth")
        definitions = deepcopy(case["definitions"])
    elif category == "malformed":
        _require(depth is None and not case["decoded"], "malformed control lost its expected topology refusal")
        definitions = [{"name": "dag_probe", "type": 2, "value": 1}]
    else:
        raise ValueError("empty/arena requests have no native definition probe")
    for definition in definitions:
        _require(type(definition) is dict and set(definition) == {"name", "type", "value"}
                 and _name(definition["name"])
                 and all(_natural(definition[field]) and definition[field] < len(nodes) for field in ("type", "value")),
                 "malformed native definition control")
    return nodes, definitions


def native_fixture(case: dict, depth: int | None = None) -> str:
    nodes, definitions = _fixture_spec(case, depth)
    rows = ["lean-ocaml-benchmark-dag-v1"]
    for index, (tag, a, b, c, name) in enumerate(nodes):
        payload = [a] if tag in (0, 1) else [bytes(name).decode("ascii")] if tag == 2 \
                  else [a, b, c] if tag == 6 else [a, b]
        rows.append("\t".join(map(str, ("n", index, TAGS[tag], *payload))))
    rows.extend("\t".join(map(str, ("d", d["name"], d["type"], d["value"]))) for d in definitions)
    return "\n".join(rows) + "\n"


def _arena_request(nodes: Any) -> dict:
    _require(type(nodes) is list and len(nodes) <= MAX_ARENA_NODES, "native arena is not a bounded node list")
    result = []
    for node in nodes:
        _require(type(node) is dict and set(node) == {"tag", "a", "b", "c", "name"}
                 and type(node["tag"]) is str and node["tag"] in TAGS and type(node["name"]) is str,
                 "native node lost immutable fields or exposed extra metadata")
        _require(node["name"].isascii(), "native constant name is not ASCII")
        result.append([TAGS.index(node["tag"]), node["a"], node["b"], node["c"], list(node["name"].encode("ascii"))])
    request = {"nodes": result, "depths": list(DEPTHS)}
    validate_request(request)
    _wire_bound(request)
    return request


def _bindings(bindings: Any, size: int) -> None:
    _require(type(bindings) is list, "native bindings must be an ordered list")
    for binding in bindings:
        _require(type(binding) is dict and set(binding) == {"name", "type", "value", "inferred"}
                 and _name(binding["name"]), "malformed native stored binding")
        _require(all(_natural(binding[field]) and binding[field] < size for field in ("type", "value", "inferred")),
                 "native binding has a nonintegral or missing raw node ID")
    _require(len({binding["name"] for binding in bindings}) == len(bindings), "native binding names are not unique")


def check_native(case: dict, depth: int | None, prediction: dict, exit_code: int,
                 stdout: str, stderr: str) -> dict:
    validate_model(prediction, case)
    fixture_nodes, definitions = _fixture_spec(case, depth)
    identifier = f"{case['id']}-d{depth}" if case["category"] == "finite" else case["id"]
    if case["category"] == "malformed":
        _require(type(exit_code) is int and exit_code == 3 and stdout == "" and stderr == PARSER_DIAGNOSTIC,
                 "invalid topology did not produce the exact parser refusal with empty stdout")
        return {"id": identifier, "trace": None, "arena_inputs": [], "processed_steps": 0,
                "success_observations": 0, "halted": False}
    if case["category"] == "finite":
        closed = prediction["scoped"][case["root"]][depth]
        expected_outcomes = ["observed_success", None if closed else "Invalid_scope"]
        halted = not closed
    else:
        expected_outcomes = case["outcomes"]
        halted = expected_outcomes[-1] == "Invalid_scope"
    _require(type(exit_code) is int and exit_code == (2 if halted else 0)
             and stderr == (SCOPE_DIAGNOSTIC if halted else ""), "native scope exit differs from the model/control")
    _require(type(stdout) is str and stdout.endswith("\n") and stdout.count("\n") == 1
             and len(stdout.encode()) <= MAX_TRACE_BYTES, "native trace is not one bounded JSON line with LF")
    trace = _json_object(stdout)
    _require(set(trace) == {"schema", "engine", "status", "steps", "success_observations", "acceptance_authority"}
             and trace["schema"] == TRACE_SCHEMA and trace["engine"] == "goose-aot"
             and trace["status"] == ("halted" if halted else "traced")
             and trace["acceptance_authority"] is False and _natural(trace["success_observations"]),
             "unknown native expression trace envelope or authority")
    steps = trace["steps"]
    _require(type(steps) is list and len(steps) == len(expected_outcomes) <= len(definitions),
             "native expression trace processed the wrong definition prefix")
    arenas, previous_nodes, previous_bindings, successes = [], fixture_nodes, [], 0
    for index, step in enumerate(steps):
        _require(type(step) is dict and set(step) == {"name", "outcome", "nodes", "bindings"}
                 and step["name"] == definitions[index]["name"] and type(step["outcome"]) is str
                 and step["outcome"] in ALL_OUTCOMES, "native step identity, outcome, or fields changed")
        expected = expected_outcomes[index]
        _require(step["outcome"] in CLOSED_OUTCOMES if expected is None else step["outcome"] == expected,
                 "native result differs from the model's scope or named control expectation")
        arena = _arena_request(step["nodes"])
        _require(arena["nodes"][:len(previous_nodes)] == previous_nodes,
                 "native trace changed an imported, unused, or previously allocated node payload/ID")
        bindings = step["bindings"]
        _bindings(bindings, len(arena["nodes"]))
        if step["outcome"] == "observed_success":
            successes += 1
            _require(len(bindings) == len(previous_bindings) + 1 and bindings[:-1] == previous_bindings,
                     "successful native insertion changed an earlier raw binding record")
            added = bindings[-1]
            _require(all(added[field] == definitions[index][field] for field in ("name", "type", "value")),
                     "native success did not preserve the original definition node IDs")
        else:
            _require(bindings == previous_bindings, "native refusal/fatal result mutated stored bindings")
        if case["category"] == "named" and step["outcome"] != "Duplicate_definition":
            definition = definitions[index]
            scoped = prediction["scoped"][definition["type"]][0] and prediction["scoped"][definition["value"]][0]
            _require(scoped == (step["outcome"] != "Invalid_scope"), "named control disagrees with model root scope")
        arenas.append(arena)
        previous_nodes, previous_bindings = arena["nodes"], bindings
    _require(trace["success_observations"] == successes == len(previous_bindings),
             "native success count differs from actual stored bindings")
    return {"id": identifier, "trace": trace, "arena_inputs": arenas, "processed_steps": len(steps),
            "success_observations": successes, "halted": halted}


def check_observation(case: dict, depth: int | None, observation: dict, exit_code: int,
                      stdout: str, stderr: str) -> dict:
    _fixture_spec(case, depth)
    if case["category"] == "malformed":
        _require(type(exit_code) is int and exit_code == 3 and stdout == "" and stderr == PARSER_DIAGNOSTIC,
                 "ordinary check accepted malformed topology or changed its parser refusal")
        return {"parser_rejected": True, "completed_receipt": False, "acceptance_authority": False}
    if observation["halted"]:
        _require(type(exit_code) is int and exit_code == 2 and stdout == "" and stderr == SCOPE_DIAGNOSTIC,
                 "ordinary check emitted a receipt or changed its fatal scope contract")
        return {"halted": True, "completed_receipt": False, "acceptance_authority": False}
    _require(type(exit_code) is int and exit_code == 0 and stderr == ""
             and type(stdout) is str and stdout.endswith("\n") and stdout.count("\n") == 1,
             "ordinary check did not produce one completed observation line")
    data = _json_object(stdout)
    expected = {"schema": "lean-goose.definition-observations.v1", "engine": "goose-aot", "status": "checked",
                "outcomes": [{"name": step["name"], "outcome": step["outcome"]} for step in observation["trace"]["steps"]],
                "success_observations": observation["success_observations"], "acceptance_authority": False}
    _require(_natural(data.get("success_observations")) and data.get("acceptance_authority") is False
             and data == expected, "ordinary check differs from the observed trace's outcomes or count")
    return data


def arena_cases(observations: list[dict]) -> tuple[list[dict], list[list[int]]]:
    inventory, mappings, indices = [], [], {}
    for observation in observations:
        mapping = []
        for request in observation["arena_inputs"]:
            case = {"id": f"arena-{len(inventory):05d}", "category": "arena",
                    "model_input": request, "decoded": True}
            key = encode(case)
            if key not in indices:
                indices[key] = len(inventory)
                inventory.append(deepcopy(case))
            mapping.append(indices[key])
        _require(len(mapping) == observation["processed_steps"], "arena mapping omitted a processed snapshot")
        mappings.append(mapping)
    return inventory, mappings


def compare_arenas(case: dict, depth: int | None, prediction: dict, observation: dict,
                   arena_models: list[dict]) -> dict:
    """Compare agreed Lean/Quint arena results to every captured native payload."""
    validate_model(prediction, case)
    trace = observation["trace"]
    verified = check_native(case, depth, prediction,
                            3 if trace is None else 2 if observation["halted"] else 0,
                            "" if trace is None else json.dumps(trace, separators=(",", ":")) + "\n",
                            PARSER_DIAGNOSTIC if trace is None else SCOPE_DIAGNOSTIC if observation["halted"] else "")
    _require(verified == observation, "captured observation or arena mapping changed before replay comparison")
    _require(type(arena_models) is list and len(arena_models) == observation["processed_steps"],
             "arena replay omitted or added a snapshot")
    original_count = len(case["model_input"]["nodes"])
    _, definitions = _fixture_spec(case, depth)
    node_payloads, binding_records, previous_model = 0, 0, None
    for index, (request, row) in enumerate(zip(observation["arena_inputs"], arena_models)):
        arena_case = {"id": f"observed-{index}", "category": "arena", "model_input": request, "decoded": True}
        validate_model(row, arena_case)
        for field in ("expressions", "heights", "loose", "scoped"):
            _require(row[field][:original_count] == prediction[field],
                     "arena replay changed an original expression's wire, height, loose requirement, or scope")
            if previous_model is not None:
                _require(row[field][:len(previous_model[field])] == previous_model[field],
                         "arena replay changed an earlier imported or derived node's complete model payload")
        if case["category"] == "finite":
            _require(row["scoped"][definitions[1]["value"]][0] == prediction["scoped"][case["root"]][depth],
                     "model binder-depth scope disagrees with the actual imported lambda wrappers")
        step = trace["steps"][index]
        for binding in step["bindings"]:
            for field in ("type", "value", "inferred"):
                _wire_matches(request["nodes"], binding[field], row["expressions"][binding[field]])
        node_payloads += len(request["nodes"])
        binding_records += len(step["bindings"])
        previous_model = row
    return {"status": "passed", "snapshots": len(arena_models), "node_payloads": node_payloads,
            "binding_records": binding_records, "input_prefix_preserved": True,
            "native_scope_checked": trace is not None, "acceptance_authority": False}
