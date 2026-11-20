"""Finite stored-binding inputs and strict model/native observation decoders.

Lean and Quint supply the semantic predictions. This module maps actions to
native fixtures and checks complete stored records, immutable DAG payloads,
ordering, and framing. It does not decide whether definitions should succeed.
"""
from __future__ import annotations

from itertools import product
import re
from typing import Any

import run as observations
import transaction_profile

Action = tuple[int, int, int, int]
ACTIONS: tuple[Action, ...] = tuple(action + (0,) for action in transaction_profile.ACTIONS) + (
    (0, 0, 0, 1), (0, 1, 0, 1), (2, 0, 1, 1), (2, 1, 0, 1),
)
CASE_COUNT = 2954
OUTCOMES = transaction_profile.OUTCOMES | {1: "Invalid_scope"}
TRACE_SCHEMA = "lean-goose.binding-trace.v1"
NAME = re.compile(r"[A-Za-z0-9_]+")


def cases() -> list[tuple[Action, ...]]:
    return [word for length in range(1, 4) for word in product(ACTIONS, repeat=length)]


def encode(actions: tuple[Action, ...]) -> str:
    if not isinstance(actions, tuple) or not 1 <= len(actions) <= 3 or any(
            not isinstance(action, tuple) or len(action) != 4
            or any(type(value) is not int for value in action) or action not in ACTIONS for action in actions):
        raise ValueError("trace is outside the stored-binding action profile")
    return ";".join(",".join(str(value) for value in action) for action in actions)


def definition_ids(action: Action) -> tuple[int, int]:
    kind, _, target, level = action
    return level + 1, {0: level, 1: level + 1, 2: 4 + target, 3: 3}[kind]


def fixture(actions: tuple[Action, ...]) -> str:
    encode(actions)
    rows = ["lean-ocaml-benchmark-dag-v1", "n\t0\ts\t0", "n\t1\ts\t1", "n\t2\ts\t2",
            "n\t3\tv\t0", "n\t4\tc\tformal0", "n\t5\tc\tformal1"]
    for action in actions:
        ty, value = definition_ids(action)
        rows.append(f"d\tformal{action[1]}\t{ty}\t{value}")
    return "\n".join(rows) + "\n"


def natural(value: Any) -> bool:
    return type(value) is int and value >= 0


def payload(value: Any) -> None:
    if not isinstance(value, list) or len(value) != 2 or any(not natural(n) for n in value) \
            or (value[0] == 0 and value[1] not in (0, 1, 2)) \
            or (value[0] == 2 and value[1] not in (0, 1)) or value[0] not in (0, 2):
        raise ValueError("expression payload is outside the declared Sort/Const profile")


def environment(value: Any) -> None:
    if not isinstance(value, list):
        raise ValueError("stored environment must be an ordered binding list")
    names = []
    for binding in value:
        if not isinstance(binding, dict) or set(binding) != {"name", "type", "value", "inferred"} \
                or type(binding["name"]) is not int or binding["name"] not in (0, 1):
            raise ValueError("malformed full binding record")
        names.append(binding["name"])
        for field in ("type", "value", "inferred"):
            payload(binding[field])
    if len(names) != len(set(names)):
        raise ValueError("stored binding names must be unique")


def validate_model(row: dict[str, Any], actions: tuple[Action, ...]) -> None:
    encode(actions)
    fields = {"halted", "outcomes", "environment", "successes", "acceptance_authority", "snapshots"}
    if not isinstance(row, dict) or set(row) != fields or type(row["halted"]) is not bool \
            or row["acceptance_authority"] is not False:
        raise ValueError("unknown stored-binding result or non-observational authority")
    environment(row["environment"])
    snapshots = row["snapshots"]
    if not isinstance(snapshots, list) or not 1 <= len(snapshots) <= len(actions) \
            or (not row["halted"] and len(snapshots) != len(actions)):
        raise ValueError("missing or additional stored-binding snapshot")
    previous, outcomes = [], []
    for index, snapshot in enumerate(snapshots):
        if not isinstance(snapshot, dict) or set(snapshot) != {"name", "code", "environment"} \
                or type(snapshot["name"]) is not int or snapshot["name"] != actions[index][1] \
                or type(snapshot["code"]) is not int or snapshot["code"] not in OUTCOMES:
            raise ValueError("malformed or reordered model snapshot")
        current, code = snapshot["environment"], snapshot["code"]
        environment(current)
        if code == 1:
            if not row["halted"] or index != len(snapshots) - 1 or actions[index][0] != 3:
                raise ValueError("fatal snapshot must end a scope-halted trace")
        else:
            outcomes.append({"name": snapshot["name"], "code": code})
        if code == 0:
            if len(current) != len(previous) + 1 or current[:-1] != previous \
                    or current[-1]["name"] != snapshot["name"]:
                raise ValueError("success did not append exactly one complete binding")
        elif current != previous:
            raise ValueError("refusal or fatal failure changed a stored binding field")
        previous = current
    if row["halted"] != (snapshots[-1]["code"] == 1):
        raise ValueError("halt state differs from final diagnostic snapshot")
    if row["environment"] != previous or row["outcomes"] != outcomes \
            or not isinstance(row["outcomes"], list):
        raise ValueError("final model state differs from its snapshot history")
    # Equality alone accepts Boolean-as-integer substitutions in Python.
    for outcome in row["outcomes"]:
        if not isinstance(outcome, dict) or set(outcome) != {"name", "code"} \
                or type(outcome["name"]) is not int or type(outcome["code"]) is not int:
            raise ValueError("model observation fields must be exact integers")
    successful = [outcome["name"] for outcome in outcomes if outcome["code"] == 0]
    if [binding["name"] for binding in previous] != successful \
            or type(row["successes"]) is not int or row["successes"] != len(successful):
        raise ValueError("stored bindings differ from the ordered successful observations")


def decode_models(text: str, inventory: list[tuple[Action, ...]]) -> list[dict[str, Any]]:
    lines = text.splitlines()
    if len(lines) != len(inventory):
        raise ValueError("stored-binding replay returned a missing or additional result")
    result = []
    for line, actions in zip(lines, inventory):
        row = observations.json_object(line)
        validate_model(row, actions)
        result.append(row)
    return result


def nodes_valid(nodes: Any) -> None:
    if not isinstance(nodes, list) or not 1 <= len(nodes) <= 4096:
        raise ValueError("native node table is outside its diagnostic bound")
    for index, node in enumerate(nodes):
        if not isinstance(node, dict) or set(node) != {"tag", "a", "b", "c", "name"} \
                or type(node["tag"]) is not str or node["tag"] not in ("s", "v", "c", "a", "l", "p", "t") \
                or any(not natural(node[field]) for field in ("a", "b", "c")) \
                or not isinstance(node["name"], str):
            raise ValueError("malformed immutable node record")
        tag = node["tag"]
        children = ("a", "b", "c") if tag == "t" else ("a", "b") if tag in ("a", "l", "p") else ()
        if any(node[field] >= index for field in children):
            raise ValueError("native DAG has a forward, self, or escaping child reference")
        if tag == "c":
            if not NAME.fullmatch(node["name"]) or any(node[field] for field in ("a", "b", "c")):
                raise ValueError("malformed constant node payload")
        elif node["name"] or (tag != "t" and node["c"]) or (tag in ("s", "v") and node["b"]):
            raise ValueError("unexpected unused native node fields")


def decoded_payload(nodes: list[dict], index: Any) -> list[int]:
    if not natural(index) or index >= len(nodes):
        raise ValueError("stored binding node ID is outside the snapshot arena")
    node = nodes[index]
    if node["tag"] == "s":
        result = [0, node["a"]]
    elif node["tag"] == "c" and node["name"] in ("formal0", "formal1"):
        result = [2, int(node["name"][-1])]
    else:
        raise ValueError("stored native payload is outside the Sort/Const correspondence scope")
    payload(result)
    return result


def check_trace(expected: dict[str, Any], actions: tuple[Action, ...], exit_code: int,
                stdout: str, stderr: str) -> dict[str, Any]:
    validate_model(expected, actions)
    if expected["halted"]:
        if exit_code != 2 or stderr != "goose bounded checker: Invalid_scope\n":
            raise ValueError("native stored trace did not produce its designated scope failure")
    elif exit_code != 0 or stderr:
        raise ValueError("native stored trace failed instead of completing")
    if not stdout.endswith("\n") or stdout.count("\n") != 1 or len(stdout.encode()) > 4194304:
        raise ValueError("native stored trace must be one bounded JSON line with LF")
    raw = observations.json_object(stdout)
    if set(raw) != {"schema", "engine", "status", "steps", "success_observations", "acceptance_authority"} \
            or raw["schema"] != TRACE_SCHEMA or raw["engine"] != "goose-aot" \
            or raw["status"] != ("halted" if expected["halted"] else "traced") \
            or raw["acceptance_authority"] is not False \
            or type(raw["success_observations"]) is not int \
            or raw["success_observations"] != expected["successes"]:
        raise ValueError("unknown or non-observational stored trace envelope")
    steps = raw["steps"]
    if not isinstance(steps, list) or len(steps) != len(expected["snapshots"]):
        raise ValueError("native trace has missing or additional processed definitions")
    old_nodes, old_bindings = [], []
    input_nodes = [{"tag": "s", "a": level, "b": 0, "c": 0, "name": ""} for level in range(3)] + [
        {"tag": "v", "a": 0, "b": 0, "c": 0, "name": ""},
        {"tag": "c", "a": 0, "b": 0, "c": 0, "name": "formal0"},
        {"tag": "c", "a": 0, "b": 0, "c": 0, "name": "formal1"},
    ]
    for step, model, action in zip(steps, expected["snapshots"], actions):
        if not isinstance(step, dict) or set(step) != {"name", "outcome", "bindings", "nodes"} \
                or step["name"] != f"formal{model['name']}" or step["outcome"] != OUTCOMES[model["code"]]:
            raise ValueError("native trace name, order, or outcome differs from the model")
        nodes, bindings = step["nodes"], step["bindings"]
        nodes_valid(nodes)
        if nodes[:len(input_nodes)] != input_nodes or nodes[:len(old_nodes)] != old_nodes:
            raise ValueError("native trace changed an existing immutable node payload")
        if not isinstance(bindings, list):
            raise ValueError("native bindings must be an ordered list")
        decoded = []
        for binding in bindings:
            if not isinstance(binding, dict) or set(binding) != {"name", "type", "value", "inferred"} \
                    or binding["name"] not in ("formal0", "formal1"):
                raise ValueError("malformed native binding record")
            decoded.append({"name": int(binding["name"][-1]), **{
                field: decoded_payload(nodes, binding[field]) for field in ("type", "value", "inferred")}})
        if decoded != model["environment"]:
            raise ValueError("native type, value, or inferred payload differs from the model")
        if model["code"] == 0:
            ty, value = definition_ids(action)
            if bindings[:-1] != old_bindings or len(bindings) != len(old_bindings) + 1 \
                    or bindings[-1]["type"] != ty or bindings[-1]["value"] != value:
                raise ValueError("native success changed old IDs or failed to retain declared input IDs")
        elif bindings != old_bindings:
            raise ValueError("native refusal or fatal failure changed a raw stored binding")
        old_nodes, old_bindings = nodes, bindings
    return raw


def check_observation(expected: dict[str, Any], exit_code: int, stdout: str,
                      stderr: str) -> dict[str, Any]:
    """Require the existing --check contract on the same finite native input."""
    return transaction_profile.check_native(expected, exit_code, stdout, stderr)
