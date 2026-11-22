"""Authored typing specimens and strict complete-binding correspondence checks.

This module constructs syntax and checks observations. It does not implement
inference, normalization, conversion, or substitution. The expected successful
inferred types below are independently authored examples, not oracle outputs.
"""
from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
import json
import re
from typing import Any

import run as observations
import stored_binding_profile as stored

SCHEMA = "lean-goose.typing-conversion-model.v1"
TAGS = "svcalpt"
OUTCOMES = {0: "observed_success", 1: "Invalid_scope", 2: "Unknown_constant",
            3: "Duplicate_definition", 4: "Expected_sort", 5: "Expected_function",
            6: "Type_mismatch", 9: "ModelFuelExhausted"}
Expr = tuple
MAX_WIRE_TOKENS = 1_000_000
MAX_TABLE_TOKENS = 2_000_000
MAX_TRACE_BYTES = 4_194_304


def expression(text: str) -> Expr:
    """Parse authored prefix syntax only; this is not a semantic evaluator."""
    tokens = iter(text.split())

    def read() -> Expr:
        token = next(tokens)
        if token in ("a", "l", "p"):
            return (token, read(), read())
        if token == "t":
            return (token, read(), read(), read())
        if token[0] in ("s", "v") and token[1:].isdigit():
            return (token[0], int(token[1:]))
        if token[0] == "c" and re.fullmatch(r"[A-Za-z0-9_]+", token[1:]):
            return ("c", token[1:])
        raise ValueError(f"invalid authored syntax: {token}")

    value = read()
    if next(tokens, None) is not None:
        raise ValueError("trailing authored syntax")
    return value


def wire(expr: Expr) -> list[int]:
    tag = TAGS.index(expr[0])
    if tag in (0, 1):
        return [tag, expr[1]]
    if tag == 2:
        return [2, len(expr[1]), *expr[1].encode("ascii")]
    return [tag, *(item for child in expr[1:] for item in wire(child))]


def validate_wire(value: Any) -> None:
    if not isinstance(value, list) or not 1 <= len(value) <= MAX_WIRE_TOKENS \
            or any(type(n) is not int or n < 0 for n in value):
        raise ValueError("expression wire must be a nonempty natural-number vector")
    cursor = 0

    def take() -> int:
        nonlocal cursor
        if cursor >= len(value):
            raise ValueError("truncated expression wire")
        token = value[cursor]
        cursor += 1
        return token

    pending = 1
    while pending:
        pending -= 1
        tag = take()
        if tag in (0, 1):
            take()
        elif tag == 2:
            size = take()
            name = [take() for _ in range(size)]
            validate_name(name)
        elif tag in (3, 4, 5, 6):
            pending += 3 if tag == 6 else 2
        else:
            raise ValueError("unknown structural expression tag")

    if cursor != len(value):
        raise ValueError("trailing structural expression tokens")


def validate_name(value: Any) -> None:
    if not isinstance(value, list) or not value or any(
            type(n) is not int or not (48 <= n <= 57 or 65 <= n <= 90 or 97 <= n <= 122 or n == 95)
            for n in value):
        raise ValueError("name must be nonempty ASCII letters, digits or underscores")


def exact(left: Any, right: Any) -> bool:
    """JSON equality that cannot silently equate booleans and integer fields."""
    return type(left) is type(right) and (
        set(left) == set(right) and all(exact(left[k], right[k]) for k in left) if isinstance(left, dict)
        else len(left) == len(right) and all(exact(a, b) for a, b in zip(left, right))
        if isinstance(left, list) else left == right)


class Dag:
    def __init__(self) -> None:
        self.nodes: list[list] = []
        self.ids: dict[Expr, int] = {}
        self.definitions: list[list] = []

    def add(self, expr: Expr) -> int:
        if expr in self.ids:
            return self.ids[expr]
        tag = TAGS.index(expr[0])
        if tag in (0, 1):
            node = [tag, expr[1], 0, 0, []]
        elif tag == 2:
            node = [2, 0, 0, 0, list(expr[1].encode("ascii"))]
        else:
            children = [self.add(child) for child in expr[1:]]
            node = [tag, *children, *([0] if tag != 6 else []), []]
        self.ids[expr] = len(self.nodes)
        self.nodes.append(node)
        return len(self.nodes) - 1

    def define(self, name: str, ty: Expr, value: Expr) -> None:
        self.definitions.append([list(name.encode("ascii")), self.add(ty), self.add(value)])


@dataclass
class Case:
    name: str
    request: dict
    expected: dict
    lean_outcomes: list[str] | None
    purpose: str


def case(name: str, rows: list[tuple], purpose: str, *, references: bool = True) -> Case:
    """Rows: name, declared syntax, value syntax, result code, inferred or Lean error."""
    graph = Dag()
    steps, bindings, lean_errors = [], [], []
    halted = False
    for label, ty_text, value_text, code, answer in rows:
        ty, value = expression(ty_text), expression(value_text)
        graph.define(label, ty, value)
        if halted:
            continue
        if code == 0:
            bindings.append({"name": list(label.encode("ascii")), "type": wire(ty),
                             "value": wire(value), "inferred": wire(expression(answer))})
            lean_errors.append("observed_success")
        else:
            lean_errors.append(answer)
        steps.append({"name": list(label.encode("ascii")), "outcome": code, "bindings": deepcopy(bindings)})
        halted = code in (1, 9)
    request = {"nodes": graph.nodes, "definitions": graph.definitions, "fuel": 128}
    result = Case(name, request, {"schema": SCHEMA, "steps": steps, "halted": halted,
                                  "acceptance_authority": False},
                  lean_errors if references else None, purpose)
    validate_model(result.expected, request)
    return result


def cases() -> list[Case]:
    result = [
        case("identity", [("id", "p s1 s1", "l s1 v0", 0, "p s1 s1")],
             "Lambda and Pi inference; retain compound stored value and inferred Pi."),
        case("beta_value", [("beta", "s1", "a l s1 v0 s0", 0, "s1")],
             "Application typing substitutes the codomain and retains the original lambda application."),
        case("beta_declared_type", [("betaTy", "a l s2 v0 s1", "s0", 0, "s1")],
             "Successful conversion retains unreduced compound declared type."),
        case("zeta_value", [("zeta", "s1", "t s1 s0 v0", 0, "s1")],
             "Typed let checks its annotation and value before substituting."),
        case("zeta_declared_type", [("zetaTy", "t s2 s1 v0", "s0", 0, "s1")],
             "Zeta reduction in a declared type with distinct stored inferred field."),
        case("beta_zeta", [("both", "s1", "t s1 s0 a l s1 v0 v0", 0, "s1")],
             "Zeta substitution feeds a typed lambda application; original let syntax remains stored."),
        case("dependent_identity", [("dep", "p s1 p v0 v1", "l s1 l v0 v0", 0, "p s1 p v0 v1")],
             "Dependent context lookup must lift a binder's stored type."),
        case("dependent_application", [("atProp", "p s0 s0", "a l s1 l v0 v0 s0", 0, "p s0 s0")],
             "Application substitutes its argument into a dependent codomain."),
        case("open_zeta_under_binder", [("openLet", "p s1 p s1 s1", "l s1 t s1 v0 l s1 v1", 0, "p s1 p s1 s1")],
             "A let replacement containing a free variable crosses a lambda without capture."),
        case("open_beta_under_binder", [("openBeta", "p s1 s1", "l s1 a l s1 v0 v0", 0, "p s1 s1")],
             "An application under a binder uses its current context."),
        case("stored_alias_fields", [
            ("U", "s2", "s1", 0, "s2"),
            ("id", "p cU cU", "l cU v0", 0, "p s1 s1"),
            ("alias", "p cU cU", "cid", 0, "p s1 s1"),
            ("call", "s1", "a calias s0", 0, "s1")],
             "Declared type, original value and normalized inferred type remain distinct across aliases."),
        case("delta_function_type", [
            ("F", "s2", "p s1 s1", 0, "s2"),
            ("id", "cF", "l s1 v0", 0, "p s1 s1"),
            ("call", "s1", "a cid s0", 0, "s1")],
             "Constant inference returns declared type; application unfolds that type to expose Pi."),
        case("delta_dependent_application", [
            ("dep", "p s1 p v0 v1", "l s1 l v0 v0", 0, "p s1 p v0 v1"),
            ("atProp", "p s0 s0", "a cdep s0", 0, "p s0 s0")],
             "Constant inference reads a stored dependent Pi and application substitutes its codomain."),
        case("refusal_retry_and_lookup", [
            ("id", "p s1 s1", "l s1 v0", 0, "p s1 s1"),
            ("bad", "s1", "s1", 6, "declTypeMismatch"),
            ("absent", "s1", "cbad", 2, "unknownConstant"),
            ("bad", "s1", "a cid s0", 0, "s1"),
            ("use", "s1", "cbad", 0, "s1")],
             "Refusal preserves all previous compound bindings and allows retry of its unused name."),
        case("duplicate_compound_preservation", [
            ("id", "p s1 s1", "l s1 v0", 0, "p s1 s1"),
            ("id", "s1", "s0", 3, "alreadyDeclared"),
            ("call", "s1", "a cid s0", 0, "s1")],
             "A duplicate cannot overwrite a stored compound type or value."),
        case("declared_term_not_type", [("bad", "l s1 v0", "s0", 4, "typeExpected")],
             "Reject a lambda used as the declared type."),
        case("lambda_domain_not_type", [("bad", "s0", "l l s1 v0 v0", 4, "typeExpected")],
             "Lambda-domain inference must produce a sort."),
        case("pi_domain_not_type", [("bad", "s0", "p l s1 v0 s1", 4, "typeExpected")],
             "Pi-domain inference must produce a sort."),
        case("pi_codomain_not_type", [("bad", "s0", "p s1 l s1 v0", 4, "typeExpected")],
             "Pi-codomain inference must produce a sort under the extended context."),
        case("nonfunction", [("bad", "s1", "a s0 s0", 5, "funExpected")],
             "Application must expose a Pi type before checking the argument."),
        case("erased_bad_beta_argument", [("bad", "s1", "a l s1 s0 s1", 6, "appTypeMismatch")],
             "An argument that beta would erase still needs the correct type."),
        case("erased_bad_let_value", [("bad", "s1", "t s1 s1 s0", 6, "letTypeMismatch")],
             "An unused let value is checked before zeta reduction."),
        case("bad_beta_annotation", [("bad", "a l s2 s1 s0", "s0", 6, "appTypeMismatch")],
             "Normalizing a malformed declared type before checking it would incorrectly succeed."),
        case("bad_zeta_annotation", [("bad", "t s2 s0 s1", "s0", 6, "letTypeMismatch")],
             "An erased ill-typed let inside an annotation is refused."),
        case("unknown_erased_beta_argument", [("bad", "s1", "a l s1 s0 cmissing", 2, "unknownConstant")],
             "Unknown constant validation precedes beta erasure."),
        case("unknown_erased_let_value", [("bad", "s1", "t s1 cmissing s0", 2, "unknownConstant")],
             "Unknown constant validation precedes zeta erasure."),
        case("unknown_in_declared_type", [("bad", "t s2 cmissing s1", "s0", 2, "unknownConstant")],
             "Prevalidate constants in the complete original declared type."),
        case("universe_mismatch", [("bad", "s1", "s1", 6, "declTypeMismatch")],
             "Conversion does not treat unequal numeric sorts as equal."),
        case("wrong_dependent_codomain", [("bad", "p s1 p v0 s1", "l s1 l v0 v0", 6, "declTypeMismatch")],
             "Reject a syntactically well-scoped but incorrect dependent result type."),
        case("impredicative_pi", [("propPi", "s0", "p s1 p s0 v0", 0, "s0")],
             "Pi sort uses codomain-zero imax, not plain max."),
        case("shared_open_context", [
            ("good", "p s1 p s1 p v1 v2", "l s1 l s1 l v1 a l v2 v0 v0", 0, "p s1 p s1 p v1 v2"),
            ("bad", "p s1 p s1 p v0 v2", "l s1 l s1 l v0 a l v2 v0 v0", 6, "appTypeMismatch"),
            ("again", "p s1 p s1 p v1 v2", "l s1 l s1 l v1 a l v2 v0 v0", 0, "p s1 p s1 p v1 v2")],
             "Identical raw open syntax under different contexts cannot reuse a closed-expression typing cache."),
        case("capture_avoided", [
            ("good", "p s1 p s1 p v1 p v1 v3", "l s1 l s1 l v1 a l v2 l v2 v1 v0", 0, "p s1 p s1 p v1 p v1 v3"),
            ("bad", "p s1 p s1 p v1 p v1 v2", "l s1 l s1 l v1 a l v2 l v2 v1 v0", 6, "declTypeMismatch")],
             "The type distinguishes capture-avoiding substitution from a shifted-variable error."),
        case("duplicate_precedes_scope", [
            ("id", "p s1 s1", "l s1 v0", 0, "p s1 s1"),
            ("id", "v0", "cmissing", 3, "alreadyDeclared"),
            ("call", "s1", "a cid s0", 0, "s1")],
             "Native priority control: duplicate precedes scope and unknown-constant checks.", references=False),
        case("scope_halts_after_compound", [
            ("id", "p s1 s1", "l s1 v0", 0, "p s1 s1"),
            ("bad", "s1", "a l s1 v0 v0", 1, "Invalid_scope"),
            ("unprocessed", "s1", "s0", 0, "s1")],
             "Fatal scope rejection retains prior full bindings and suppresses later definitions.", references=False),
        case("scope_precedes_unknown", [("bad", "v0", "cmissing", 1, "Invalid_scope")],
             "Native priority control: closedness before syntactic constant validation.", references=False),
        case("unknown_precedes_inference", [("bad", "s1", "a s0 cmissing", 2, "unknownConstant")],
             "Native priority control: prevalidation before a nonfunction inference error.", references=False),
    ]
    for depth in range(1, 5):
        beta, zeta = "s1", "s0"
        for _ in range(depth):
            beta = "a l s2 v0 " + beta
            zeta = "t s1 " + zeta + " v0"
        result.append(case(f"beta_chain_{depth}", [("chain", beta, "s0", 0, "s1")],
                           f"Declared-type conversion forces composed beta reductions, depth {depth}."))
        result.append(case(f"zeta_chain_{depth}", [("chain", "s1", zeta, 0, "s1")],
                           f"Composed typed lets, depth {depth}."))
    for left, right in ((0, 0), (0, 2), (2, 0), (2, 2)):
        inferred = f"s{max(left + 1, right + 1)}"
        result.append(case(f"pi_numeric_{left}_{right}", [("pi", inferred, f"p s{left} s{right}", 0, inferred)],
                           "Numeric-sort Pi formation at two independently varied levels."))
    if len(result) != 48 or len({c.name for c in result}) != len(result):
        raise ValueError("typing fixture inventory changed")
    return result


def encode(request: dict) -> str:
    return json.dumps(request, separators=(",", ":"), allow_nan=False)


def fixture(request: dict) -> str:
    rows = ["lean-ocaml-benchmark-dag-v1"]
    for index, (tag, a, b, c, name) in enumerate(request["nodes"]):
        fields = [a] if tag in (0, 1) else [bytes(name).decode("ascii")] if tag == 2 \
            else [a, b, c] if tag == 6 else [a, b]
        rows.append("\t".join(map(str, ["n", index, TAGS[tag], *fields])))
    rows.extend("\t".join(map(str, ["d", bytes(name).decode("ascii"), ty, value]))
                for name, ty, value in request["definitions"])
    return "\n".join(rows) + "\n"


def validate_model(row: dict, request: dict) -> None:
    if not isinstance(row, dict) or set(row) != {"schema", "steps", "halted", "acceptance_authority"} \
            or row["schema"] != SCHEMA or type(row["halted"]) is not bool or row["acceptance_authority"] is not False:
        raise ValueError("unknown typing result envelope or authority")
    steps = row["steps"]
    if not isinstance(steps, list) or not 1 <= len(steps) <= len(request["definitions"]) \
            or not row["halted"] and len(steps) != len(request["definitions"]):
        raise ValueError("missing or additional typing snapshots")
    previous = []
    for index, step in enumerate(steps):
        if not isinstance(step, dict) or set(step) != {"name", "outcome", "bindings"} \
                or not exact(step["name"], request["definitions"][index][0]) \
                or type(step["outcome"]) is not int or step["outcome"] not in OUTCOMES:
            raise ValueError("typing snapshot identity or outcome mismatch")
        validate_name(step["name"])
        current, code = step["bindings"], step["outcome"]
        if not isinstance(current, list):
            raise ValueError("bindings must be an ordered list")
        for binding in current:
            if not isinstance(binding, dict) or set(binding) != {"name", "type", "value", "inferred"}:
                raise ValueError("typing binding fields mismatch")
            validate_name(binding["name"])
            for field in ("type", "value", "inferred"):
                validate_wire(binding[field])
        if len({tuple(b["name"]) for b in current}) != len(current):
            raise ValueError("duplicate stored binding names")
        if code == 0:
            if len(current) != len(previous) + 1 or not exact(current[:-1], previous) \
                    or not exact(current[-1]["name"], step["name"]):
                raise ValueError("successful typing did not append exactly one complete binding")
        elif not exact(current, previous):
            raise ValueError("refusal changed a stored binding")
        if code in (1, 9) and (not row["halted"] or index != len(steps) - 1):
            raise ValueError("fatal outcome did not terminate the model trace")
        previous = current
    if row["halted"] != (steps[-1]["outcome"] in (1, 9)):
        raise ValueError("typing halt status differs from final outcome")


def decode_models(text: str, inventory: list[Case]) -> list[dict]:
    if not text.endswith("\n") or len(text.splitlines()) != len(inventory):
        raise ValueError("typing replay returned missing, additional or unterminated results")
    rows = [observations.json_object(line) for line in text.splitlines()]
    for item, row in zip(inventory, rows):
        validate_model(row, item.request)
        if not exact(row, item.expected):
            raise ValueError(f"typing model differs from authored complete-field expectation: {item.name}: {row!r}")
    return rows


def raw_nodes(request: dict) -> list[dict]:
    return [{"tag": TAGS[tag], "a": a, "b": b, "c": c, "name": bytes(name).decode("ascii")}
            for tag, a, b, c, name in request["nodes"]]


def decode_nodes(nodes: list[dict]) -> list[list[int]]:
    stored.nodes_valid(nodes)
    table = []
    tokens = 0
    for node in nodes:
        tag = TAGS.index(node["tag"])
        size = 2 if tag in (0, 1) else 2 + len(node["name"]) if tag == 2 \
            else 1 + len(table[node["a"]]) + len(table[node["b"]]) \
            + (len(table[node["c"]]) if tag == 6 else 0)
        tokens += size
        if size > MAX_WIRE_TOKENS or tokens > MAX_TABLE_TOKENS:
            raise ValueError("typing observation structural expansion exceeds its diagnostic bound")
        if tag in (0, 1):
            row = [tag, node["a"]]
        elif tag == 2:
            row = [2, len(node["name"]), *node["name"].encode("ascii")]
        else:
            row = [tag, *table[node["a"]], *table[node["b"]]]
            if tag == 6:
                row += table[node["c"]]
        table.append(row)
    return table


def check_trace(item: Case, expected: dict, exit_code: int, stdout: str, stderr: str) -> dict:
    validate_model(expected, item.request)
    if any(step["outcome"] == 9 for step in expected["steps"]):
        raise ValueError("model exhaustion is not a native correspondence expectation")
    wanted_exit = 2 if expected["halted"] else 0
    wanted_error = "goose bounded checker: Invalid_scope\n" if expected["halted"] else ""
    if type(exit_code) is not int or exit_code != wanted_exit or stderr != wanted_error:
        raise ValueError(f"native trace process status mismatch: {item.name}")
    if not stdout.endswith("\n") or stdout.count("\n") != 1 or len(stdout.encode()) > MAX_TRACE_BYTES:
        raise ValueError("native typing trace must be one complete JSON line")
    raw = observations.json_object(stdout)
    if set(raw) != {"schema", "engine", "status", "steps", "success_observations", "acceptance_authority"} \
            or raw["schema"] != stored.TRACE_SCHEMA or raw["engine"] != "goose-aot" \
            or raw["status"] != ("halted" if expected["halted"] else "traced") \
            or raw["acceptance_authority"] is not False or type(raw["success_observations"]) is not int \
            or raw["success_observations"] != len(expected["steps"][-1]["bindings"]) \
            or not isinstance(raw["steps"], list) or len(raw["steps"]) != len(expected["steps"]):
        raise ValueError("native typing trace envelope mismatch")
    original = raw_nodes(item.request)
    old_nodes, old_bindings = original, []
    for index, (snapshot, model) in enumerate(zip(raw["steps"], expected["steps"])):
        if not isinstance(snapshot, dict) or set(snapshot) != {"name", "outcome", "bindings", "nodes"} \
                or snapshot["name"] != bytes(model["name"]).decode("ascii") \
                or snapshot["outcome"] != OUTCOMES[model["outcome"]]:
            raise ValueError("native typing snapshot identity or outcome mismatch")
        nodes, bindings = snapshot["nodes"], snapshot["bindings"]
        table = decode_nodes(nodes)
        if not exact(nodes[:len(old_nodes)], old_nodes) or not exact(nodes[:len(original)], original):
            raise ValueError("native typing trace changed immutable raw nodes")
        if not isinstance(bindings, list):
            raise ValueError("native bindings must be an ordered list")
        decoded = []
        for binding in bindings:
            if not isinstance(binding, dict) or set(binding) != {"name", "type", "value", "inferred"} \
                    or not isinstance(binding["name"], str) or not stored.NAME.fullmatch(binding["name"]) \
                    or any(type(binding[field]) is not int or not 0 <= binding[field] < len(table)
                           for field in ("type", "value", "inferred")):
                raise ValueError("native full binding record mismatch")
            decoded.append({"name": list(binding["name"].encode("ascii")), **{
                field: table[binding[field]] for field in ("type", "value", "inferred")}})
        if not exact(decoded, model["bindings"]):
            raise ValueError(f"native compound type/value/inferred differs from models: {item.name}")
        if model["outcome"] == 0:
            _, ty, value = item.request["definitions"][index]
            if not exact(bindings[:-1], old_bindings) or bindings[-1]["type"] != ty or bindings[-1]["value"] != value:
                raise ValueError("native success changed original binding IDs")
        elif not exact(bindings, old_bindings):
            raise ValueError("native refusal changed original binding IDs")
        old_nodes, old_bindings = nodes, bindings
    return raw


def semantic_expectations(item: Case, engine: str) -> list[dict]:
    if item.lean_outcomes is None:
        raise ValueError("this native/model priority control is outside the reference comparison profile")
    return [{"name": bytes(step["name"]).decode("ascii"),
             "outcome": item.lean_outcomes[i] if engine == "lean-kernel" else OUTCOMES[step["outcome"]]}
            for i, step in enumerate(item.expected["steps"])]
