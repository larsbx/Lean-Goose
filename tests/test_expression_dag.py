"""Negative controls for expression framing, raw IDs, topology, and binder evidence."""
from copy import deepcopy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import check_expression_dag as gate
import expression_dag_profile as profile

spec = importlib.util.spec_from_file_location("dag_quint_wire", ROOT / "formal/quint/dag_replay.py")
quint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(quint)


def request_case(nodes, *, decoded=True, category="arena", root=None):
    return {"id": "authored-case", "category": category, "decoded": decoded,
            "model_input": {"nodes": deepcopy(nodes), "depths": [0, 1, 2, 3]}, "root": root}


def all_tags_example():
    """A fixed structural example, not an alternate DAG/scope evaluator."""
    case = request_case([
        [0, 0, 0, 0, []], [0, 1, 0, 0, []], [1, 0, 0, 0, []], [2, 0, 0, 0, [120, 95, 57]],
        [3, 0, 1, 0, []], [4, 0, 2, 0, []], [5, 0, 2, 0, []], [6, 1, 0, 2, []],
    ])
    row = {"decoded": True,
           "expressions": [[0, 0], [0, 1], [1, 0], [2, 3, 120, 95, 57], [3, 0, 0, 0, 1],
                           [4, 0, 0, 1, 0], [5, 0, 0, 1, 0], [6, 0, 1, 0, 0, 1, 0]],
           "heights": [1, 1, 1, 1, 2, 2, 2, 2], "loose": [0, 0, 1, 0, 0, 0, 0, 0],
           "scoped": [[True] * 4, [True] * 4, [False, True, True, True], *([[True] * 4] * 5)],
           "acceptance_authority": False}
    return case, row


def native_example():
    """Authored from the actual sort probe, including an unused constant node."""
    case = request_case([[2, 0, 0, 0, list(b"missing")], [0, 0, 0, 0, []], [0, 0, 0, 0, []]],
                        category="finite", root=2)
    row = {"decoded": True, "expressions": [[2, 7, *b"missing"], [0, 0], [0, 0]],
           "heights": [1, 1, 1], "loose": [0, 0, 0], "scoped": [[True] * 4 for _ in range(3)],
           "acceptance_authority": False}
    nodes = [{"tag": "c", "a": 0, "b": 0, "c": 0, "name": "missing"}] + [
        {"tag": "s", "a": level, "b": 0, "c": 0, "name": ""} for level in (0, 0, 0, 1, 2, 1)]
    seed = {"name": "dag_seed", "type": 4, "value": 3, "inferred": 6}
    probe = {"name": "dag_probe", "type": 4, "value": 2, "inferred": 7}
    trace = {"schema": profile.TRACE_SCHEMA, "engine": "goose-aot", "status": "traced", "steps": [
        {"name": "dag_seed", "outcome": "observed_success", "nodes": deepcopy(nodes), "bindings": [deepcopy(seed)]},
        {"name": "dag_probe", "outcome": "observed_success",
         "nodes": deepcopy(nodes) + [{"tag": "s", "a": 1, "b": 0, "c": 0, "name": ""}],
         "bindings": [deepcopy(seed), probe]}], "success_observations": 2, "acceptance_authority": False}
    arenas = []
    for suffix in ([[0, 0], [0, 1], [0, 2], [0, 1]], [[0, 0], [0, 1], [0, 2], [0, 1], [0, 1]]):
        expressions = deepcopy(row["expressions"]) + suffix
        arenas.append({"decoded": True, "expressions": expressions, "heights": [1] * len(expressions),
                       "loose": [0] * len(expressions), "scoped": [[True] * 4 for _ in expressions],
                       "acceptance_authority": False})
    return case, row, trace, arenas


def observe(case, row, trace, *, exit_code=0, stderr=""):
    return profile.check_native(case, 0, row, exit_code, json.dumps(trace) + "\n", stderr)


def bad_scope_witness():
    sort = {"tag": 0, "a": 0, "b": 0, "c": 0, "name": []}
    variable = {"tag": 1, "a": 1, "b": 0, "c": 0, "name": []}
    binder = {"tag": 4, "a": 0, "b": 1, "c": 0, "name": []}
    before = {"nodes": [sort, variable], "rows": [
        {"expression": [0, 0], "height": 1, "loose": 0},
        {"expression": [1, 1], "height": 1, "loose": 2}],
        "decoded": True, "acceptance_authority": False}
    after = deepcopy(before)
    after["nodes"].append(binder)
    after["rows"].append({"expression": [4, 0, 0, 1, 1], "height": 2, "loose": 0})
    return {"states": [{"s": deepcopy(before), "previous": deepcopy(before), "last": variable, "hasStep": False},
                       {"s": after, "previous": deepcopy(before), "last": binder, "hasStep": True}]}


class InventoryTests(unittest.TestCase):
    def test_complete_finite_depth_and_control_inventory(self):
        cases = profile.cases()
        probes = profile.probes(cases)
        self.assertEqual(len(cases), 2208)
        self.assertEqual(len({case["id"] for case in cases}), 2208)
        self.assertEqual(len(probes), 8696)
        self.assertEqual(len(probes) + sum(probe["check"] for probe in probes), 8740)
        finite = [case for case in cases if case["category"] == "finite"]
        self.assertEqual([sum(len(case["model_input"]["nodes"]) == n for case in finite) for n in (1, 2, 3)],
                         [7, 77, 2079])
        self.assertEqual({node[0] for case in finite for node in case["model_input"]["nodes"]}, set(range(7)))
        for case in cases:
            self.assertEqual(json.loads(profile.encode(case)), case["model_input"])
        self.assertEqual(len([case for case in cases if case["category"] == "malformed"]), 27)
        self.assertEqual(len([case for case in cases if case["category"] == "named"]), 17)

    def test_empty_dag_is_model_only(self):
        case = next(case for case in profile.cases() if case["category"] == "empty")
        row = {"decoded": True, "expressions": [], "heights": [], "loose": [], "scoped": [],
               "acceptance_authority": False}
        profile.validate_model(row, case)
        self.assertEqual(profile.probes([case]), [])
        with self.assertRaises(ValueError):
            profile.native_fixture(case)

    def test_native_root_and_depth_are_not_boolean_ids(self):
        case, _, _, _ = native_example()
        for root, depth in ((True, 0), (2, False), (-1, 0), (2, 4)):
            altered = deepcopy(case)
            altered["root"] = root
            with self.subTest(root=root, depth=depth), self.assertRaises(ValueError):
                profile.native_fixture(altered, depth)

    def test_all_malformed_child_slots_are_rejected_atomically(self):
        row = {"decoded": False, "expressions": [], "heights": [], "loose": [], "scoped": [],
               "acceptance_authority": False}
        for case in (case for case in profile.cases() if case["category"] == "malformed"):
            with self.subTest(case=case["id"]):
                with self.assertRaises(ValueError):
                    profile.validate_request(case["model_input"])
                profile.validate_model(row, case)
                for changed in (dict(row, decoded=True), dict(row, expressions=[[0, 0]])):
                    with self.assertRaises(ValueError):
                        profile.validate_model(changed, case)
                observation = profile.check_native(case, None, row, 3, "", profile.PARSER_DIAGNOSTIC)
                self.assertEqual(observation["arena_inputs"], [])
                self.assertIsNone(observation["trace"])
                for code, stdout, stderr in ((0, "", ""), (2, "", profile.SCOPE_DIAGNOSTIC),
                                              (3, "{}\n", profile.PARSER_DIAGNOSTIC)):
                    with self.assertRaises(ValueError):
                        profile.check_native(case, None, row, code, stdout, stderr)


class ModelFramingTests(unittest.TestCase):
    def test_fixed_all_tag_payloads_are_lossless(self):
        case, row = all_tags_example()
        profile.validate_model(row, case)
        self.assertEqual(profile.decode_models(json.dumps(row) + "\n", [case]), [row])

    def test_malformed_raw_fields_are_not_coerced(self):
        case, _ = all_tags_example()
        mutations = [
            lambda r: r["nodes"][0].__setitem__(0, False),
            lambda r: r["nodes"][0].__setitem__(1, 0.0),
            lambda r: r["nodes"][0].__setitem__(2, 1),
            lambda r: r["nodes"][3].__setitem__(4, []),
            lambda r: r["nodes"][3][4].__setitem__(0, True),
            lambda r: r["nodes"][3][4].__setitem__(0, 233),
            lambda r: r["nodes"][4].__setitem__(3, 1),
            lambda r: r["nodes"][5].__setitem__(1, 5),
            lambda r: r["depths"].__setitem__(0, False),
            lambda r: r.__setitem__("extra", []),
        ]
        for mutation in mutations:
            raw = deepcopy(case["model_input"])
            mutation(raw)
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                profile.validate_request(raw)

    def test_model_frame_rejects_extra_missing_duplicate_and_nonfinite_fields(self):
        case, row = all_tags_example()
        text = json.dumps(row)
        for bad in (text, text + "\n" + text + "\n", "\n", text[:-1] + ',"decoded":true}\n',
                    text.replace('"heights": [1', '"heights": [NaN', 1) + "\n"):
            with self.subTest(text=bad[:80]), self.assertRaises(ValueError):
                profile.decode_models(bad, [case])
        for key in row:
            changed = deepcopy(row)
            del changed[key]
            with self.subTest(missing=key), self.assertRaises(ValueError):
                profile.validate_model(changed, case)

    def test_bool_numeric_flags_and_wire_mutations_fail(self):
        case, row = all_tags_example()
        mutations = [
            lambda r: r.__setitem__("decoded", 1),
            lambda r: r.__setitem__("acceptance_authority", 0),
            lambda r: r["heights"].__setitem__(0, True),
            lambda r: r["loose"].__setitem__(0, False),
            lambda r: r["scoped"][0].__setitem__(0, 1),
            lambda r: r["scoped"][0].pop(),
            lambda r: r["expressions"][0].__setitem__(0, False),
            lambda r: r["expressions"][3].__setitem__(2, 121),
            lambda r: r["expressions"].__setitem__(4, [3, 0, 1, 0, 0]),
            lambda r: r["expressions"][7].append(0),
        ]
        for mutation in mutations:
            changed = deepcopy(row)
            mutation(changed)
            with self.subTest(row=changed), self.assertRaises(ValueError):
                profile.validate_model(changed, case)

    def test_shared_wire_expansion_is_bounded_before_replay(self):
        nodes = [[0, 0, 0, 0, []]]
        for index in range(1, 30):
            nodes.append([3, index - 1, index - 1, 0, []])
        case = request_case(nodes)
        profile.validate_request(case["model_input"])
        with self.assertRaisesRegex(ValueError, "expansion"):
            profile.encode(case)


class NativeCorrespondenceTests(unittest.TestCase):
    def test_raw_fixture_preserves_ids_and_unused_node(self):
        case, row, trace, arenas = native_example()
        fixture = profile.native_fixture(case, 0)
        self.assertIn("n\t0\tc\tmissing\n", fixture)
        self.assertIn("d\tdag_seed\t4\t3\n", fixture)
        self.assertIn("d\tdag_probe\t4\t2\n", fixture)
        observation = observe(case, row, trace)
        summary = profile.compare_arenas(case, 0, row, observation, arenas)
        self.assertEqual((summary["snapshots"], summary["node_payloads"], summary["binding_records"]), (2, 15, 3))
        self.assertTrue(summary["native_scope_checked"])

    def test_raw_binding_ids_cannot_be_replaced_by_equivalent_payload_ids(self):
        case, row, trace, _ = native_example()
        for binding, field, replacement in ((0, "inferred", 4), (1, "type", 6), (1, "value", 1)):
            changed = deepcopy(trace)
            changed["steps"][1]["bindings"][binding][field] = replacement
            with self.subTest(binding=binding, field=field), self.assertRaises(ValueError):
                observe(case, row, changed)

    def test_unused_original_and_previous_derived_nodes_are_preserved(self):
        case, row, trace, _ = native_example()
        changes = [(0, 0, "name", "different"), (1, 0, "name", "different"), (1, 5, "a", 3)]
        for step, node, field, value in changes:
            changed = deepcopy(trace)
            changed["steps"][step]["nodes"][node][field] = value
            with self.subTest(step=step, node=node), self.assertRaises(ValueError):
                observe(case, row, changed)

    def test_native_node_shapes_metadata_and_numeric_ids_are_strict(self):
        case, row, trace, _ = native_example()
        mutations = [
            lambda t: t["steps"][0]["nodes"][0].__setitem__("normal", -1),
            lambda t: t["steps"][0]["nodes"][0].__setitem__("b", 1),
            lambda t: t["steps"][0]["nodes"][1].__setitem__("a", False),
            lambda t: t["steps"][0]["bindings"][0].__setitem__("type", True),
            lambda t: t["steps"][0]["bindings"][0].__setitem__("inferred", 99),
            lambda t: t.__setitem__("success_observations", True),
            lambda t: t.__setitem__("acceptance_authority", 0),
            lambda t: t["steps"].reverse(),
            lambda t: t["steps"].pop(),
        ]
        for mutation in mutations:
            changed = deepcopy(trace)
            mutation(changed)
            with self.subTest(trace=changed), self.assertRaises(ValueError):
                observe(case, row, changed)

    def test_native_framing_and_model_scope_are_required(self):
        case, row, trace, _ = native_example()
        text = json.dumps(trace) + "\n"
        for code, stdout, stderr in ((True, text, ""), (0, text + "\n", ""), (0, text[:-1], ""),
                                     (0, text, "unexpected\n"), (2, text, profile.SCOPE_DIAGNOSTIC)):
            with self.subTest(code=code, stderr=stderr), self.assertRaises(ValueError):
                profile.check_native(case, 0, row, code, stdout, stderr)
        changed = deepcopy(row)
        changed["scoped"][2][0] = False
        with self.assertRaises(ValueError):
            observe(case, changed, trace)

    def test_model_append_prefix_includes_prior_derived_nodes(self):
        case, row, trace, arenas = native_example()
        observation = observe(case, row, trace)
        for field, value in (("heights", 2), ("loose", 1), ("scoped", [False, True, True, True])):
            changed = deepcopy(arenas)
            changed[1][field][5] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "earlier imported or derived"):
                profile.compare_arenas(case, 0, row, observation, changed)

    def test_arena_dedup_uses_complete_canonical_request_equality(self):
        case, row, trace, _ = native_example()
        observation = observe(case, row, trace)
        inventory, mappings = profile.arena_cases([observation, deepcopy(observation)])
        self.assertEqual(len(inventory), 2)
        self.assertEqual(mappings, [[0, 1], [0, 1]])
        changed = deepcopy(observation)
        changed["arena_inputs"][0]["nodes"][0][4] = list(b"another")
        inventory, mappings = profile.arena_cases([observation, changed])
        self.assertEqual(len(inventory), 3)
        self.assertEqual(mappings, [[0, 1], [2, 1]])

    def test_comparison_rejects_mutated_capture_or_missing_arena(self):
        case, row, trace, arenas = native_example()
        observation = observe(case, row, trace)
        changed = deepcopy(observation)
        changed["arena_inputs"][0]["nodes"][0][4] = list(b"another")
        with self.assertRaises(ValueError):
            profile.compare_arenas(case, 0, row, changed, arenas)
        with self.assertRaises(ValueError):
            profile.compare_arenas(case, 0, row, observation, arenas[:1])

    def test_completed_check_contract_is_tied_to_trace(self):
        case, row, trace, _ = native_example()
        observation = observe(case, row, trace)
        checked = {"schema": "lean-goose.definition-observations.v1", "engine": "goose-aot", "status": "checked",
                   "outcomes": [{"name": "dag_seed", "outcome": "observed_success"},
                                {"name": "dag_probe", "outcome": "observed_success"}],
                   "success_observations": 2, "acceptance_authority": False}
        profile.check_observation(case, 0, observation, 0, json.dumps(checked) + "\n", "")
        checked["outcomes"][1]["outcome"] = "Type_mismatch"
        with self.assertRaises(ValueError):
            profile.check_observation(case, 0, observation, 0, json.dumps(checked) + "\n", "")


class CounterexampleTests(unittest.TestCase):
    def test_bad_binder_witness_requires_real_designated_violation(self):
        message = "[violation] Found an issue\nerror: Invariant violated"
        witness = bad_scope_witness()
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "witness.json"
            path.write_text(json.dumps(witness))
            gate.counterexample(1, message, path)
            for code, text in ((0, message), (2, message), (1, "typecheck failed")):
                with self.subTest(code=code, text=text), self.assertRaises(ValueError):
                    gate.counterexample(code, text, path)

    def test_witness_cannot_substitute_another_state_or_boolean_payload(self):
        message = "[violation] Found an issue\nerror: Invariant violated"
        mutations = [
            lambda w: w["states"].pop(),
            lambda w: w["states"][1]["s"]["rows"][-1].__setitem__("loose", 1),
            lambda w: w["states"][1]["s"]["rows"][-1].__setitem__("loose", False),
            lambda w: w["states"][1]["s"]["rows"][-1]["expression"].__setitem__(4, 0),
            lambda w: w["states"][1]["last"].__setitem__("b", 0),
            lambda w: w["states"][1].__setitem__("hasStep", 1),
            lambda w: w["states"][0]["s"].__setitem__("acceptance_authority", 0),
            lambda w: w["states"][1].__setitem__("previous", {}),
        ]
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "witness.json"
            for mutation in mutations:
                witness = bad_scope_witness()
                mutation(witness)
                path.write_text(json.dumps(witness))
                with self.subTest(witness=witness), self.assertRaises(ValueError):
                    gate.counterexample(1, message, path)


class QuintAdapterTests(unittest.TestCase):
    @staticmethod
    def wire(index, request, observation):
        """Encode only the adapter's numeric framing around an authored result."""
        result = quint.identity(index, request) + [int(observation["decoded"]), 0, len(observation["expressions"])]
        for expression, height, loose, scoped in zip(observation["expressions"], observation["heights"],
                                                     observation["loose"], observation["scoped"]):
            result.extend([len(expression), *expression, height, loose, len(scoped), *map(int, scoped)])
        return result

    def test_adapter_request_preserves_invalid_topology_for_model_refusal(self):
        case = next(case for case in profile.cases() if case["category"] == "malformed")
        request = quint.request(profile.encode(case))
        self.assertEqual(request, case["model_input"])
        row = quint.Wire(quint.identity(0, request) + [0, 0, 0]).observation(0, request)
        profile.validate_model(row, case)
        self.assertFalse(row["decoded"])

    def test_adapter_rejects_noncanonical_or_coerced_request_fields(self):
        case, _ = all_tags_example()
        invalid = [
            '{"nodes":[],"depths":[],"nodes":[]}',
            '{"nodes":[[false,0,0,0,[]]],"depths":[0]}',
            '{"nodes":[[0,1.0,0,0,[]]],"depths":[0]}',
            '{"nodes":[[0,NaN,0,0,[]]],"depths":[0]}',
            '{"nodes":[[0,0,1,0,[]]],"depths":[0]}',
            '{"nodes":[[2,0,0,0,[true]]],"depths":[0]}',
            '{"nodes":[[2,0,0,0,[233]]],"depths":[0]}',
            '{"nodes":[],"depths":[false]}',
        ]
        self.assertEqual(quint.request(profile.encode(case)), case["model_input"])
        for text in invalid:
            with self.subTest(text=text), self.assertRaises(ValueError):
                quint.request(text)

    def test_adapter_requires_complete_exact_integer_result_framing(self):
        case, row = all_tags_example()
        request = case["model_input"]
        wire = self.wire(0, request, row)
        self.assertEqual(quint.Wire(wire).observation(0, request), row)
        identity_size = len(quint.identity(0, request))
        invalid = [wire[:-1], wire + [0]]
        for position, value in ((0, 1), (1, True), (identity_size, 0),
                                (identity_size + 1, 1), (len(wire) - 1, 2)):
            changed = list(wire)
            changed[position] = value
            invalid.append(changed)
        for changed in invalid:
            with self.subTest(wire=changed), self.assertRaises(ValueError):
                quint.Wire(changed).observation(0, request)

    def test_adapter_batch_identity_rejects_reordering_duplication_and_trailing_batches(self):
        case, row = all_tags_example()
        request = case["model_input"]
        first, second = self.wire(0, request, row), self.wire(1, request, row)
        with patch.object(quint, "BATCH_SIZE", 1):
            good = json.dumps([first]) + "\n" + json.dumps([second]) + "\n"
            self.assertEqual(quint.decode_batches(good, [request, request]), [row, row])
            invalid = [json.dumps([first]), json.dumps([second]) + "\n" + json.dumps([first]),
                       json.dumps([first]) + "\n" + json.dumps([first]),
                       good + json.dumps([second]), json.dumps([first, second])]
            for text in invalid:
                with self.subTest(text=text[:80]), self.assertRaises(ValueError):
                    quint.decode_batches(text, [request, request])


if __name__ == "__main__":
    unittest.main()
