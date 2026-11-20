"""Rejection controls for the formal/native comparison and evidence wrapper."""
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
import acceptance
import check_formal as gate
import transaction_profile as profile


def model():
    return {"halted": False, "outcomes": [{"name": 0, "code": 0}, {"name": 1, "code": 0}],
            "environment": [0, 1], "successes": 2, "acceptance_authority": False}


def native():
    return {"schema": "lean-goose.definition-observations.v1", "engine": "goose-aot", "status": "checked",
            "outcomes": [{"name": "formal0", "outcome": "observed_success"},
                         {"name": "formal1", "outcome": "observed_success"}],
            "success_observations": 2, "acceptance_authority": False}


class ProfileControls(unittest.TestCase):
    def test_complete_declared_inventory(self):
        cases = profile.cases()
        self.assertEqual(len(set(cases)), 1110)
        self.assertEqual([sum(len(row) == n for row in cases) for n in (1, 2, 3)], [10, 100, 1000])
        self.assertIn(((0, 0, 0), (3, 0, 0), (2, 1, 0)), cases)
        self.assertIn(((1, 0, 0), (0, 0, 0), (2, 1, 0)), cases)

    def test_input_profile_bounds(self):
        for actions in ((), ((4, 0, 0),), ((0, 2, 0),), ((0, 0, 1),), ((0, 0, 0),) * 4):
            with self.subTest(actions=actions), self.assertRaises(ValueError):
                profile.fixture(actions)

    def test_models_preserve_success_order(self):
        actions = ((0, 0, 0), (0, 1, 0))
        profile.validate_model(model(), actions)
        bad = model(); bad["environment"] = [1, 0]
        with self.assertRaisesRegex(ValueError, "ordered successful"):
            profile.validate_model(bad, actions)

    def test_model_malformed_or_incomplete_results(self):
        actions = ((0, 0, 0), (0, 1, 0))
        mutations = [lambda r: r.update(acceptance_authority=True), lambda r: r.update(successes=True),
            lambda r: r.update(extra="ignored"), lambda r: r.update(outcomes=r["outcomes"][:1]),
            lambda r: r["outcomes"][0].update(code=99), lambda r: r["outcomes"][0].update(name=True),
            lambda r: r.update(environment=[0, 0]), lambda r: r.update(halted=True)]
        for mutate in mutations:
            bad = model(); mutate(bad)
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                profile.validate_model(bad, actions)

    def test_replay_rejects_missing_extra_and_duplicate_json_fields(self):
        cases = [((0, 0, 0), (0, 1, 0))]
        good = json.dumps(model()) + "\n"
        self.assertEqual(profile.decode_models(good, cases), [model()])
        for text in ("", good * 2, good.replace('"halted": false', '"halted": false, "halted": false')):
            with self.subTest(text=text), self.assertRaises(ValueError):
                profile.decode_models(text, cases)

    def test_native_exact_observation(self):
        self.assertEqual(profile.check_native(model(), 0, json.dumps(native()), ""), native())

    def test_native_rejects_reorder_wrong_count_authority_and_categories(self):
        mutations = [lambda r: r.update(outcomes=list(reversed(r["outcomes"]))),
            lambda r: r.update(success_observations=1), lambda r: r.update(success_observations=True),
            lambda r: r.update(acceptance_authority=True), lambda r: r["outcomes"][0].update(outcome="accepted"),
            lambda r: r["outcomes"][0].update(outcome="Type_mismatch"), lambda r: r.update(extra="ignored")]
        for mutate in mutations:
            bad = native(); mutate(bad)
            with self.subTest(bad=bad), self.assertRaises((RuntimeError, ValueError)):
                profile.check_native(model(), 0, json.dumps(bad), "")

    def test_fatal_requires_designated_exit_diagnostic_and_no_receipt(self):
        expected = {"halted": True}
        diagnostic = "goose bounded checker: Invalid_scope\n"
        self.assertFalse(profile.check_native(expected, 2, "", diagnostic)["completed_receipt"])
        for code, stdout, stderr in ((0, "", diagnostic), (1, "", diagnostic), (2, "{}", diagnostic),
                                     (2, "", "parse error"), (2, "", "goose bounded checker: Limit_exceeded\n")):
            with self.subTest(code=code, stdout=stdout, stderr=stderr), self.assertRaises(ValueError):
                profile.check_native(expected, code, stdout, stderr)

    def test_failed_process_cannot_supply_successful_observation(self):
        for code, stderr in ((2, ""), (0, "unexpected diagnostic")):
            with self.assertRaises(ValueError):
                profile.check_native(model(), code, json.dumps(native()), stderr)


class ReceiptControls(unittest.TestCase):
    def test_declared_scope_must_be_in_source_inventory(self):
        spec, paths = gate.configuration(ROOT)
        files = [{"path": path} for path in paths if path != spec["scope"]]
        with self.assertRaisesRegex(ValueError, "excluded from the source digest"):
            gate.covered_inputs(ROOT, files)

    def test_every_declared_input_is_covered(self):
        files, _ = acceptance.source_snapshot()
        _, paths = gate.covered_inputs(ROOT, files)
        self.assertIn("reference/checker.goose", paths)
        self.assertIn("formal/quint/replay.py", paths)
        self.assertIn("tools/transaction_profile.py", paths)

    def test_escaping_and_symlinked_inputs_refused(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder); (root / "source").write_text("x")
            (root / "link").symlink_to(root / "source")
            for name in ("../source", str(root / "source"), "./source", "link", "missing", "a//b"):
                with self.subTest(name=name), self.assertRaises(ValueError):
                    gate.owned(root, name)

    def test_node_attestation_must_match_quint_path_node(self):
        with tempfile.TemporaryDirectory() as folder:
            first, second = Path(folder) / "node-a", Path(folder) / "node-b"
            first.write_text("node"); second.write_text("node")
            with patch.object(gate.shutil, "which", return_value=str(first)):
                gate.require_quint_node(first)
                with self.assertRaisesRegex(ValueError, "node used by Quint"):
                    gate.require_quint_node(second)

    def test_stale_success_is_invalidated_before_source_failure(self):
        with tempfile.TemporaryDirectory() as folder:
            output = Path(folder)
            (output / "results.json").write_text('{"status":"passed"}')
            with patch.object(acceptance, "source_snapshot", side_effect=ValueError("source unavailable")):
                self.assertEqual(gate.verify(output), 1)
            receipt = json.loads((output / "results.json").read_text())
            self.assertEqual(receipt["status"], "failed")
            self.assertIn("source unavailable", receipt["failure"])
            self.assertEqual(receipt["commands"], [])

    def test_source_change_cannot_leave_formal_success(self):
        with tempfile.TemporaryDirectory() as folder:
            files = [{"path": "source", "sha256": "before"}]
            after = [{"path": "source", "sha256": "after"}]
            with patch.object(acceptance, "source_snapshot", side_effect=[(files, "before"), (after, "after")]), \
                    patch.object(gate, "covered_inputs", return_value=({}, ["source"])), \
                    patch.object(gate, "execute"):
                self.assertEqual(gate.verify(Path(folder)), 1)
            receipt = json.loads((Path(folder) / "results.json").read_text())
            self.assertEqual(receipt["status"], "failed")
            self.assertFalse(receipt["source_unchanged"])

    def test_negative_control_requires_real_refusal_mutation(self):
        before = {"environment": [], "outcomes": [], "halted": False, "acceptance_authority": False}
        after = {"environment": [{"#bigint": "0"}],
                 "outcomes": [{"name": {"#bigint": "0"}, "code": {"#bigint": "6"}}],
                 "halted": False, "acceptance_authority": False}
        text = "[violation] Found an issue\nerror: Invariant violated"
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / "trace.json"
            path.write_text(json.dumps({"states": [{"s": before}, {"s": after}]}))
            gate.counterexample(1, text, path)
            for code, message in ((2, text), (1, "typecheck failed"), (0, text)):
                with self.assertRaises(ValueError):
                    gate.counterexample(code, message, path)
            after["outcomes"][0]["code"] = {"#bigint": "0"}
            path.write_text(json.dumps({"states": [{"s": before}, {"s": after}]}))
            with self.assertRaises(ValueError):
                gate.counterexample(1, text, path)


if __name__ == "__main__":
    unittest.main()
