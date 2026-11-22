"""Adversarial controls for complete typing observations and comparison framing.

Synthetic traces below serialize the separately authored fixture expectations.
They compute no typing, normalization, conversion, or substitution result.
Actual model and native executions belong to the required formal gate.
"""
from copy import deepcopy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import typing_conversion_profile as profile


def specimen(name):
    return next(item for item in profile.cases() if item.name == name)


def syntax_from_wire(wire):
    """Parse fixture syntax only; never infer an expected payload."""
    tokens = iter(wire)

    def read():
        tag = next(tokens)
        if tag in (0, 1):
            return (profile.TAGS[tag], next(tokens))
        if tag == 2:
            return ("c", bytes(next(tokens) for _ in range(next(tokens))).decode("ascii"))
        return (profile.TAGS[tag], *(read() for _ in range(3 if tag == 6 else 2)))

    result = read()
    if next(tokens, None) is not None:
        raise AssertionError("authored fixture has trailing wire syntax")
    return result


def trace_for(item):
    """Serialize supplied complete binding fields with stable source node IDs."""
    graph = profile.Dag()
    graph.nodes = deepcopy(item.request["nodes"])
    expressions = []
    for index, (tag, a, b, c, name) in enumerate(graph.nodes):
        if tag in (0, 1):
            expression = (profile.TAGS[tag], a)
        elif tag == 2:
            expression = ("c", bytes(name).decode("ascii"))
        else:
            children = (a, b, c) if tag == 6 else (a, b)
            expression = (profile.TAGS[tag], *(expressions[child] for child in children))
        expressions.append(expression)
        graph.ids[expression] = index
    bindings, steps = [], []
    for index, expected in enumerate(item.expected["steps"]):
        if expected["outcome"] == 0:
            supplied = expected["bindings"][-1]
            _, ty, value = item.request["definitions"][index]
            bindings.append({"name": bytes(supplied["name"]).decode("ascii"),
                             "type": ty, "value": value,
                             "inferred": graph.add(syntax_from_wire(supplied["inferred"]))})
        steps.append({"name": bytes(expected["name"]).decode("ascii"),
                      "outcome": profile.OUTCOMES[expected["outcome"]],
                      "bindings": deepcopy(bindings),
                      "nodes": profile.raw_nodes({"nodes": graph.nodes})})
    return {"schema": profile.stored.TRACE_SCHEMA, "engine": "goose-aot",
            "status": "halted" if item.expected["halted"] else "traced",
            "steps": steps, "success_observations": len(bindings), "acceptance_authority": False}


def observe(item, trace, *, exit_code=None, stderr=None, expected=None):
    halted = item.expected["halted"]
    if exit_code is None:
        exit_code = 2 if halted else 0
    if stderr is None:
        stderr = "goose bounded checker: Invalid_scope\n" if halted else ""
    return profile.check_trace(item, item.expected if expected is None else expected,
                               exit_code, json.dumps(trace) + "\n", stderr)


class TypingCorrespondenceControls(unittest.TestCase):
    def test_authored_compound_snapshots_have_lossless_native_framing(self):
        items = profile.cases()
        for item in items:
            with self.subTest(case=item.name):
                trace = trace_for(item)
                self.assertEqual(observe(item, trace), trace)
        self.assertEqual(profile.decode_models(
            "".join(json.dumps(item.expected) + "\n" for item in items), items),
            [item.expected for item in items])

    def test_model_payloads_reject_boolean_numeric_and_field_coercion(self):
        item = specimen("identity")
        mutations = [
            lambda r: r.update(halted=0), lambda r: r.update(acceptance_authority=0),
            lambda r: r.update(extra=[]), lambda r: r.pop("schema"),
            lambda r: r["steps"][0].update(outcome=False),
            lambda r: r["steps"][0].update(outcome=0.0),
            lambda r: r["steps"][0].update(outcome=10),
            lambda r: r["steps"][0]["name"].__setitem__(0, True),
            lambda r: r["steps"][0]["bindings"][0].update(inferred=[0, True]),
            lambda r: r["steps"][0]["bindings"][0].update(inferred=[0, 1.0]),
            lambda r: r["steps"][0]["bindings"][0].update(inferred=[0, -1]),
            lambda r: r["steps"][0]["bindings"][0].update(value=[False, 1]),
            lambda r: r["steps"][0]["bindings"][0].update(extra=0),
        ]
        for index, mutate in enumerate(mutations):
            changed = deepcopy(item.expected)
            mutate(changed)
            with self.subTest(mutation=index), self.assertRaises(ValueError):
                profile.validate_model(changed, item.request)

    def test_wire_validation_rejects_malformed_syntax_without_recursive_stack(self):
        for wire in ([], [7], [0], [1], [4, 0, 1], [0, 1, 0, 2],
                     [2, 0], [2, 2, 65], [2, 1, 233], [2, 1, 45], [2, 1, True]):
            with self.subTest(wire=wire), self.assertRaises(ValueError):
                profile.validate_wire(wire)
        # Thousands of nested syntax nodes must not raise Python RecursionError.
        profile.validate_wire([4, 0, 1] * 2000 + [1, 0])
        with patch.object(profile, "MAX_WIRE_TOKENS", 4), self.assertRaises(ValueError):
            profile.validate_wire([4, 0, 1, 1, 0])

    def test_model_refusal_cannot_rewrite_or_append_existing_bindings(self):
        item = specimen("refusal_retry_and_lookup")
        for mutation in ("rewrite", "append", "remove", "duplicate"):
            changed = deepcopy(item.expected)
            bindings = changed["steps"][1]["bindings"]
            if mutation == "rewrite":
                bindings[0]["inferred"] = [0, 1]
            elif mutation == "append":
                bindings.append(dict(deepcopy(bindings[0]), name=list(b"forged")))
            elif mutation == "remove":
                bindings.clear()
            else:
                bindings.append(deepcopy(bindings[0]))
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                profile.validate_model(changed, item.request)

    def test_model_stream_rejects_missing_extra_reordered_and_duplicate_results(self):
        items = [specimen("identity"), specimen("beta_declared_type")]
        lines = [json.dumps(item.expected) for item in items]
        good = "\n".join(lines) + "\n"
        malformed = [good.rstrip("\n"), lines[0] + "\n", good + lines[0] + "\n",
                     "\n".join(reversed(lines)) + "\n", "\n" + good,
                     good.replace('"halted": false', '"halted": false, "halted": false', 1),
                     good.replace('"outcome": 0', '"outcome": NaN', 1)]
        for index, text in enumerate(malformed):
            with self.subTest(mutation=index), self.assertRaises(ValueError):
                profile.decode_models(text, items)

    def test_native_process_and_trace_envelopes_cannot_forge_success(self):
        item = specimen("identity")
        trace = trace_for(item)
        for code, error in ((False, ""), (0.0, ""), (2, ""), (0, "warning\n")):
            with self.subTest(exit_code=code, stderr=error), self.assertRaises(ValueError):
                observe(item, trace, exit_code=code, stderr=error)
        mutations = [lambda r: r.update(success_observations=True),
                     lambda r: r.update(success_observations=0),
                     lambda r: r.update(acceptance_authority=0),
                     lambda r: r.update(acceptance_authority=True),
                     lambda r: r.update(engine="lean-kernel"),
                     lambda r: r.update(status="halted"), lambda r: r.update(extra=0)]
        for index, mutate in enumerate(mutations):
            changed = deepcopy(trace)
            mutate(changed)
            with self.subTest(mutation=index), self.assertRaises(ValueError):
                observe(item, changed)

    def test_native_snapshot_identity_order_and_cardinality_are_exact(self):
        item = specimen("stored_alias_fields")
        trace = trace_for(item)
        mutations = [lambda r: r["steps"].reverse(), lambda r: r["steps"].pop(),
                     lambda r: r["steps"].append(deepcopy(r["steps"][-1])),
                     lambda r: r["steps"][1].update(name="wrong"),
                     lambda r: r["steps"][1].update(outcome="accepted"),
                     lambda r: r["steps"][1]["bindings"].reverse()]
        for index, mutate in enumerate(mutations):
            changed = deepcopy(trace)
            mutate(changed)
            with self.subTest(mutation=index), self.assertRaises(ValueError):
                observe(item, changed)

    def test_native_node_ids_and_payload_naturals_have_exact_integer_types(self):
        item = specimen("identity")
        trace = trace_for(item)
        for field in ("type", "value", "inferred"):
            for value in (True, False, 0.0, -1, len(trace["steps"][0]["nodes"])):
                changed = deepcopy(trace)
                changed["steps"][0]["bindings"][0][field] = value
                with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                    observe(item, changed)
        for field in ("a", "b", "c"):
            for value in (False, 0.0, -1):
                changed = deepcopy(trace)
                changed["steps"][0]["nodes"][0][field] = value
                with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                    observe(item, changed)

    def test_native_complete_inferred_type_cannot_be_corrupted(self):
        item = specimen("identity")
        trace = trace_for(item)
        for field in ("type", "value", "inferred"):
            changed = deepcopy(trace)
            snapshot = changed["steps"][0]
            snapshot["nodes"].append({"tag": "s", "a": 42, "b": 0, "c": 0, "name": ""})
            snapshot["bindings"][0][field] = len(snapshot["nodes"]) - 1
            with self.subTest(field=field), self.assertRaises(ValueError):
                observe(item, changed)

    def test_native_original_ids_survive_structurally_identical_replacements(self):
        item = specimen("identity")
        trace = trace_for(item)
        for field in ("type", "value"):
            changed = deepcopy(trace)
            snapshot = changed["steps"][0]
            old_id = snapshot["bindings"][0][field]
            snapshot["nodes"].append(deepcopy(snapshot["nodes"][old_id]))
            snapshot["bindings"][0][field] = len(snapshot["nodes"]) - 1
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "original binding IDs"):
                observe(item, changed)

    def test_native_existing_raw_inferred_ids_survive_success_and_refusal(self):
        for name in ("stored_alias_fields", "refusal_retry_and_lookup"):
            item = specimen(name)
            changed = trace_for(item)
            snapshot = changed["steps"][1]
            old_id = snapshot["bindings"][0]["inferred"]
            snapshot["nodes"].append(deepcopy(snapshot["nodes"][old_id]))
            snapshot["bindings"][0]["inferred"] = len(snapshot["nodes"]) - 1
            with self.subTest(case=name), self.assertRaisesRegex(ValueError, "original binding IDs"):
                observe(item, changed)

    def test_native_input_and_generated_node_prefixes_are_immutable(self):
        item = specimen("stored_alias_fields")
        trace = trace_for(item)
        changed = deepcopy(trace)
        changed["steps"][0]["nodes"][0]["a"] += 1
        with self.assertRaisesRegex(ValueError, "immutable raw nodes"):
            observe(item, changed)
        generated = len(item.request["nodes"])
        self.assertGreater(len(trace["steps"][1]["nodes"]), generated)
        changed = deepcopy(trace)
        changed["steps"][2]["nodes"][generated]["tag"] = "a"
        with self.assertRaisesRegex(ValueError, "immutable raw nodes"):
            observe(item, changed)
        changed = deepcopy(trace)
        changed["steps"][2]["nodes"] = changed["steps"][2]["nodes"][:generated]
        with self.assertRaisesRegex(ValueError, "immutable raw nodes"):
            observe(item, changed)

    def test_scope_halt_stops_suffix_and_model_exhaustion_is_never_native_evidence(self):
        item = specimen("scope_halts_after_compound")
        trace = trace_for(item)
        observe(item, trace)
        for code, error in ((0, ""), (2, ""), (2, "goose bounded checker: Fuel_exhausted\n")):
            with self.subTest(code=code, error=error), self.assertRaises(ValueError):
                observe(item, trace, exit_code=code, stderr=error)
        changed = deepcopy(item.expected)
        changed["steps"][-1]["outcome"] = 9
        profile.validate_model(changed, item.request)
        with self.assertRaisesRegex(ValueError, "model exhaustion"):
            observe(item, trace, expected=changed)
        changed = deepcopy(item.expected)
        changed["steps"].append({"name": list(b"unprocessed"), "outcome": 2,
                                 "bindings": deepcopy(changed["steps"][-1]["bindings"])})
        with self.assertRaises(ValueError):
            profile.validate_model(changed, item.request)

    def test_expansion_and_output_limits_refuse_before_unbounded_allocation(self):
        nodes = [{"tag": "s", "a": 0, "b": 0, "c": 0, "name": ""}]
        for i in range(1, 7):
            nodes.append({"tag": "a", "a": i - 1, "b": i - 1, "c": 0, "name": ""})
        for wire_bound, table_bound in ((64, 10_000), (1000, 100)):
            with self.subTest(wire=wire_bound, table=table_bound), \
                    patch.object(profile, "MAX_WIRE_TOKENS", wire_bound), \
                    patch.object(profile, "MAX_TABLE_TOKENS", table_bound), \
                    self.assertRaisesRegex(ValueError, "structural expansion"):
                profile.decode_nodes(nodes)
        item = specimen("identity")
        with patch.object(profile, "MAX_TRACE_BYTES", 32), self.assertRaises(ValueError):
            observe(item, trace_for(item))

    def test_native_json_requires_unique_fields_exact_schema_and_complete_line(self):
        item = specimen("identity")
        text = json.dumps(trace_for(item)) + "\n"
        malformed = [text.rstrip("\n"), text * 2, "\n" + text,
                     text.replace('"engine": "goose-aot"', '"engine": "goose-aot", "engine": "goose-aot"'),
                     text.replace('"success_observations": 1', '"success_observations": NaN')]
        for index, changed in enumerate(malformed):
            with self.subTest(mutation=index), self.assertRaises(ValueError):
                profile.check_trace(item, item.expected, 0, changed, "")

    def test_reference_projection_cannot_promote_priority_or_unchecked_results(self):
        for name in ("duplicate_precedes_scope", "scope_halts_after_compound",
                     "scope_precedes_unknown", "unknown_precedes_inference"):
            with self.subTest(case=name), self.assertRaises(ValueError):
                profile.semantic_expectations(specimen(name), "lean-kernel")
        item = specimen("identity")
        expected = profile.semantic_expectations(item, "lean-kernel")
        raw = {"engine": "lean-kernel", "status": "checked", "outcomes": expected,
               "accepted": 1, "acceptance_authority": False, "trust_level": 0,
               "checked_insertion": True}
        profile.observations.definition_observation("lean-kernel", raw, expected)
        mutations = [lambda r: r.update(trust_level=False), lambda r: r.update(trust_level=1),
                     lambda r: r.update(checked_insertion=False), lambda r: r.update(accepted=True),
                     lambda r: r["outcomes"][0].update(outcome="deterministicTimeout")]
        for index, mutate in enumerate(mutations):
            changed = deepcopy(raw)
            mutate(changed)
            with self.subTest(mutation=index), self.assertRaises(RuntimeError):
                profile.observations.definition_observation("lean-kernel", changed, expected)


class ReplayIdentityControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        sys.path.insert(0, str(ROOT / "formal/quint"))
        import typing_replay
        cls.replay = typing_replay

    def test_actual_quint_wire_binds_every_request_field(self):
        query = {"nodes": [[2, 0, 0, 0, [122]], [0, 1, 0, 0, []]],
                 "definitions": [[[120], 1, 0]], "fuel": 128}
        values = self.replay.identity(0, query) + [0, 0, 1, 1, 120, 2, 0]
        self.assertEqual(self.replay.Wire(values).observation(0, query)["steps"][0]["outcome"], 2)
        mutants = [lambda q: q["nodes"][0][4].__setitem__(0, 121),
                   lambda q: q["nodes"][1].__setitem__(1, 2),
                   lambda q: q["definitions"][0].__setitem__(1, 0),
                   lambda q: q.update(fuel=127)]
        for mutate in mutants:
            changed = deepcopy(query)
            mutate(changed)
            with self.assertRaisesRegex(ValueError, "request identity"):
                self.replay.Wire(values).observation(0, changed)
        with self.assertRaisesRegex(ValueError, "request identity"):
            self.replay.Wire(values).observation(1, query)

    def test_machine_exhaustion_is_harness_failure(self):
        query = {"nodes": [[0, 0, 0, 0, []]], "definitions": [[[120], 0, 0]], "fuel": 128}
        values = self.replay.identity(0, query) + [1, 0, 1, 1, 120, 10, 0]
        with self.assertRaisesRegex(ValueError, "2048-transition cap"):
            self.replay.Wire(values).observation(0, query)

    def test_standalone_receipt_covers_comparison_dependencies(self):
        import runtime
        observed = {row["path"] for row in runtime.source_files()}
        expected = {path.relative_to(ROOT).as_posix() for path in (ROOT / "tools").glob("*.py")}
        self.assertTrue(expected <= observed)
        self.assertIn("tools/typing_conversion_profile.py", observed)
        self.assertIn("tools/check_typing_conversion.py", observed)

    def test_reference_comparison_repeats_and_replaces_stale_fixtures(self):
        import check_typing_conversion as gate
        from types import SimpleNamespace
        import tempfile
        item = specimen("identity")
        binaries = {name: Path(name) for name in ("goose-aot", "lean-kernel", "ocaml-check")}

        def run(command, **_):
            engine = "ocaml-bytecode" if command[0] == "ocaml-check" else command[0]
            result = {"engine": engine, "status": "checked", "acceptance_authority": False,
                      "outcomes": [{"name": "id", "outcome": "observed_success" if engine == "goose-aot" else "accepted"}]}
            result["success_observations" if engine == "goose-aot" else "accepted"] = 1
            if engine == "goose-aot":
                result["schema"] = "lean-goose.definition-observations.v1"
            elif engine == "lean-kernel":
                result.update(trust_level=0, checked_insertion=True)
            return SimpleNamespace(returncode=0, stdout=json.dumps(result) + "\n", stderr="")

        with tempfile.TemporaryDirectory() as directory, \
                patch.object(gate, "REFERENCE_CASE_COUNT", 1), \
                patch.object(gate, "REFERENCE_OUTCOME_COUNT", 1), \
                patch.object(gate.profile, "cases", return_value=[item]), \
                patch.object(gate.subprocess, "run", side_effect=run) as commands:
            output = Path(directory)
            (output / "typing-conversion").mkdir()
            target = output / "typing-conversion/identity.tsv"
            for attempt in range(2):
                target.write_text("stale observation must be replaced")
                self.assertEqual(gate.check_reference_engines(binaries, output)["status"], "passed")
                self.assertEqual(target.read_text(), profile.fixture(item.request))
                self.assertEqual(commands.call_count, (attempt + 1) * 3)


if __name__ == "__main__":
    unittest.main()
