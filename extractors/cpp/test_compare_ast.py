#!/usr/bin/env python3
"""Regress complete-AST diagnostic comparison, not C++ execution semantics."""

import copy
import importlib.util
import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile
import unittest


HERE = pathlib.Path(__file__).resolve().parent
MODULE_SPEC = importlib.util.spec_from_file_location(
    "cpp_compare_ast_under_test", HERE / "compare_ast.py",
)
comparison = importlib.util.module_from_spec(MODULE_SPEC)
sys.modules[MODULE_SPEC.name] = comparison
MODULE_SPEC.loader.exec_module(comparison)

POINTER_FIELDS = frozenset((
    "id", "previousDecl", "parentDeclContextId", "firstRedecl", "declId",
    "referencedMemberDecl", "labelDeclId", "typeAliasDeclId", "temp", "targetLabelDeclId",
))
POINTER_PATTERN = re.compile(r"^0x[0-9a-fA-F]+$")


def child_path(path, segment):
    return path + "/" + str(segment).replace("~", "~0").replace("/", "~1")


def occurrence_paths(ast):
    paths = {}
    pending = [("", ast)]
    while pending:
        path, value = pending.pop()
        if isinstance(value, dict):
            identifier = value.get("id")
            if isinstance(identifier, str):
                paths.setdefault(identifier, []).append(path)
            pending.extend((child_path(path, field), value[field]) for field in value)
        elif isinstance(value, list):
            pending.extend((child_path(path, ordinal), child)
                           for ordinal, child in enumerate(value))
    return {identifier: tuple(sorted(group)) for identifier, group in paths.items()}


def small_all_paths_oracle(value, groups, pointer_mode, field=None):
    if isinstance(value, dict):
        return ("object", tuple((key, small_all_paths_oracle(
            value[key], groups, pointer_mode, key,
        )) for key in sorted(value)))
    if isinstance(value, list):
        return ("array", tuple(small_all_paths_oracle(
            child, groups, pointer_mode,
        ) for child in value))
    if isinstance(value, str) and POINTER_PATTERN.fullmatch(value):
        if field not in POINTER_FIELDS:
            return ("unknown-pointer", value)
        if pointer_mode == "erase":
            return ("recognized-pointer",)
        return ("witness", groups.get(value, ("unwitnessed",)))
    return (type(value).__name__, value)


def rename_pointers(value, renaming):
    if isinstance(value, dict):
        return {field: rename_pointers(child, renaming) for field, child in value.items()}
    if isinstance(value, list):
        return [rename_pointers(child, renaming) for child in value]
    if isinstance(value, str):
        return renaming.get(value, value)
    return value


def fixture_ast():
    return {
        "id": "0x1",
        "kind": "TranslationUnitDecl",
        "inner": [
            {
                "id": "0x2", "kind": "DeclRefExpr",
                "referencedDecl": {"id": "0x3", "kind": "VarDecl", "name": "value"},
                "type": {"qualType": "int"}, "valueCategory": "lvalue",
            },
            {
                "id": "0x3", "kind": "VarDecl", "name": "value",
                "loc": {"line": 3, "col": 8, "file": "input.cpp"},
                "type": {"qualType": "int"},
                "inner": [{"id": "0x4", "kind": "IntegerLiteral", "value": "17"}],
            },
        ],
    }


def nested_ast(depth, literal):
    result = {"id": "0x1", "kind": "IntegerLiteral", "value": literal}
    for ordinal in range(depth):
        result = {"kind": "ParenExpr", "depth": ordinal, "inner": [result]}
    return result


class AstComparisonTests(unittest.TestCase):
    def compare(self, left, right):
        return comparison.compare_fingerprints(
            comparison.fingerprint_ast(left), comparison.fingerprint_ast(right),
        )

    def assert_comparison(self, left, right, nonpointer="equal", witnessed="equal"):
        result = self.compare(left, right)
        self.assertEqual(result["nonpointer_comparison_status"], nonpointer)
        self.assertEqual(result["witnessed_comparison_status"], witnessed)
        if nonpointer in ("equal", "different"):
            self.assertEqual(result["nonpointer_digest_equal"], nonpointer == "equal")
        if witnessed in ("equal", "different"):
            self.assertEqual(result["witnessed_digest_equal"], witnessed == "equal")
        return result

    def assert_small_oracle(self, left, right):
        result = self.compare(left, right)
        for mode, field in (("erase", "nonpointer_digest_equal"),
                            ("witness", "witnessed_digest_equal")):
            expected = small_all_paths_oracle(left, occurrence_paths(left), mode)
            observed = small_all_paths_oracle(right, occurrence_paths(right), mode)
            self.assertEqual(result[field], expected == observed)

    def test_summary_counts_include_skeletal_and_nested_ids(self):
        result = comparison.fingerprint_ast(fixture_ast())
        self.assertEqual(result["id_bearing_records"], 5)
        self.assertEqual(result["distinct_ids"], 4)
        self.assertEqual(result["pointer_slots"], 5)
        self.assertGreater(result["tokens"], 0)
        self.assertEqual(result["format"], "cpp-ast-fingerprint-2")
        self.assertRegex(result["nonpointer_sha256"], r"^[0-9a-f]{64}$")
        self.assertRegex(result["witnessed_sha256"], r"^[0-9a-f]{64}$")

    def test_consistent_pointer_renaming(self):
        original = fixture_ast()
        renamed = rename_pointers(original, {
            "0x1": "0xA1", "0x2": "0xA2", "0x3": "0xA3", "0x4": "0xA4",
        })
        self.assert_comparison(original, renamed)
        self.assert_small_oracle(original, renamed)

    def test_forward_reference_to_later_id(self):
        original = {"a": {"declId": "0x2"}, "z": {"id": "0x2"}}
        renamed = {"a": {"declId": "0x3"}, "z": {"id": "0x3"}}
        self.assert_comparison(original, renamed)
        self.assert_small_oracle(original, renamed)
        self.assertEqual(comparison.fingerprint_ast(original)["problems"], {
            "unrecognized_pointer_slots": [], "unwitnessed_pointer_slots": [],
        })

    def test_all_ten_known_fields_normalize(self):
        original = {field: "0x1" for field in POINTER_FIELDS}
        original["kind"] = "VarDecl"
        renamed = rename_pointers(original, {"0x1": "0xBA9"})
        self.assert_comparison(original, renamed)
        self.assert_small_oracle(original, renamed)

    def test_every_known_field_preserves_its_target(self):
        for field in sorted(POINTER_FIELDS):
            with self.subTest(field=field):
                original = {"inner": [{"id": "0x2"}, {"id": "0x3"}],
                            "link": {field: "0x2"}}
                changed = copy.deepcopy(original)
                changed["link"][field] = "0x3"
                self.assert_comparison(original, changed, witnessed="different")
                self.assert_small_oracle(original, changed)

    def test_goto_label_target_renaming_and_retargeting(self):
        original = {"inner": [
            {"id": "0x1", "kind": "LabelDecl", "name": "first"},
            {"id": "0x2", "kind": "LabelDecl", "name": "second"},
            {"kind": "LabelStmt", "declId": "0x1"},
            {"kind": "GotoStmt", "targetLabelDeclId": "0x1"},
        ]}
        renamed = rename_pointers(original, {"0x1": "0xA1", "0x2": "0xA2"})
        self.assert_comparison(original, renamed)
        self.assert_small_oracle(original, renamed)
        retargeted = copy.deepcopy(original)
        retargeted["inner"][3]["targetLabelDeclId"] = "0x2"
        self.assert_comparison(original, retargeted, witnessed="different")
        self.assert_small_oracle(original, retargeted)

    def test_label_declid_is_not_an_id_occurrence_witness(self):
        original = {"inner": [
            {"kind": "LabelStmt", "declId": "0x1"},
            {"kind": "GotoStmt", "targetLabelDeclId": "0x1"},
        ]}
        renamed = rename_pointers(original, {"0x1": "0xA1"})
        self.assert_comparison(
            original, renamed, witnessed="refused-unwitnessed-or-unrecognized-pointer-slots",
        )
        result = comparison.fingerprint_ast(original)
        self.assertEqual(result["id_bearing_records"], 0)
        self.assertEqual(result["distinct_ids"], 0)
        self.assertEqual(result["problems"], {
            "unrecognized_pointer_slots": [],
            "unwitnessed_pointer_slots": ["/inner/0/declId", "/inner/1/targetLabelDeclId"],
        })

    def test_repeated_id_alias_partition_is_observable(self):
        original = {"inner": [{"id": "0x1"}, {"id": "0x1"}, {"id": "0x2"}]}
        changed = copy.deepcopy(original)
        changed["inner"][1]["id"] = "0x2"
        self.assert_comparison(original, changed, witnessed="different")
        self.assert_small_oracle(original, changed)

    def test_reference_shaped_id_is_an_occurrence_witness(self):
        original = {"referencedDecl": {"id": "0x1", "kind": "VarDecl"},
                    "temp": "0x1"}
        renamed = rename_pointers(original, {"0x1": "0x2"})
        self.assert_comparison(original, renamed)
        result = comparison.fingerprint_ast(original)
        self.assertEqual(result["id_bearing_records"], 1)
        self.assertEqual(result["distinct_ids"], 1)
        self.assertEqual(result["problems"]["unwitnessed_pointer_slots"], [])

    def test_duplicate_reference_copy_keeps_independent_payload(self):
        original = fixture_ast()
        changed = copy.deepcopy(original)
        changed["inner"][0]["referencedDecl"]["name"] = "other"
        self.assert_comparison(original, changed, "different", "different")
        self.assert_small_oracle(original, changed)

    def test_dictionary_insertion_order_is_irrelevant(self):
        original = fixture_ast()
        changed = {field: original[field] for field in reversed(list(original))}
        changed["inner"] = [
            {field: node[field] for field in reversed(list(node))}
            for node in original["inner"]
        ]
        self.assert_comparison(original, changed)
        self.assert_small_oracle(original, changed)

    def test_array_order_is_significant(self):
        original = fixture_ast()
        changed = copy.deepcopy(original)
        changed["inner"].reverse()
        self.assert_comparison(original, changed, "different", "different")
        self.assert_small_oracle(original, changed)

    def test_nonpointer_field_and_nested_payload_changes(self):
        changes = (
            ("name", "renamed"), ("kind", "FunctionDecl"),
            ("type", {"qualType": "long"}),
            ("loc", {"line": 4, "col": 8, "file": "input.cpp"}),
            ("inner", [{"id": "0x4", "kind": "FloatingLiteral", "value": "17.0"}]),
        )
        for field, replacement in changes:
            with self.subTest(field=field):
                original = fixture_ast()
                changed = copy.deepcopy(original)
                changed["inner"][1][field] = replacement
                self.assert_comparison(original, changed, "different", "different")
                self.assert_small_oracle(original, changed)

    def test_location_payload_outside_inner_is_not_skipped(self):
        original = {"kind": "VarDecl", "loc": {"offset": 5},
                    "range": {"begin": {"line": 3}, "end": {"line": 4}}}
        changed = copy.deepcopy(original)
        changed["range"]["end"]["line"] = 5
        self.assert_comparison(original, changed, "different", "different")

    def test_missing_field_is_distinct_from_explicit_null(self):
        self.assert_comparison({"kind": "VarDecl"}, {"kind": "VarDecl", "previousDecl": None},
                               "different", "different")

    def test_scalar_types_are_distinct(self):
        scalar_pairs = ((True, 1), (False, 0), (None, "null"),
                        (17, "17"), ([], {}), ("", None))
        for left, right in scalar_pairs:
            with self.subTest(left=left, right=right):
                self.assert_comparison({"value": left}, {"value": right},
                                       "different", "different")

    def test_noninteger_and_nonjson_scalar_values_refuse(self):
        for scalar in (1.0, float("nan"), float("inf"), (1, 2), object()):
            with self.subTest(scalar=scalar):
                with self.assertRaisesRegex(ValueError, "non-integer JSON number or non-JSON value"):
                    comparison.fingerprint_ast({"value": scalar})

    def test_framing_and_escaping_avoid_concatenation_collisions(self):
        payload_pairs = ((["ab", "c"], ["a", "bc"]),
                         ({"a": 1, "bc": 2}, {"ab": 1, "c": 2}),
                         (["[", "]"], ["[]"]),
                         ("\n", "\\n"), ('"', '\\"'),
                         ("é", "\\u00e9"), ("\x00", "\\u0000"))
        for left, right in payload_pairs:
            with self.subTest(left=left, right=right):
                self.assert_comparison({"value": left}, {"value": right},
                                       "different", "different")

    def test_nonpointer_id_strings_remain_literal_payload(self):
        self.assert_comparison({"id": "ordinary-id"}, {"id": "another-id"},
                               "different", "different")

    def test_dangling_known_pointer_erases_only_nonpointer_projection(self):
        original = {"id": "0x1", "previousDecl": "0xD00D"}
        changed = {"id": "0x2", "previousDecl": "0xBEEF"}
        self.assert_comparison(
            original, changed, witnessed="refused-unwitnessed-or-unrecognized-pointer-slots",
        )
        self.assertEqual(comparison.fingerprint_ast(original)["problems"], {
            "unrecognized_pointer_slots": [], "unwitnessed_pointer_slots": ["/previousDecl"],
        })

    def test_unknown_pointer_field_refuses_even_when_target_has_id(self):
        original = {"id": "0x1", "futureDeclField": "0x1"}
        result = self.assert_comparison(
            original, copy.deepcopy(original), "refused-unrecognized-pointer-slots",
            "refused-unwitnessed-or-unrecognized-pointer-slots",
        )
        self.assertTrue(result["nonpointer_digest_equal"])
        self.assertTrue(result["witnessed_digest_equal"])
        self.assertEqual(comparison.fingerprint_ast(original)["problems"][
            "unrecognized_pointer_slots"], ["/futureDeclField"])

    def test_unknown_pointer_payload_is_retained_not_erased(self):
        original = {"literal": "0x123"}
        changed = {"literal": "0x456"}
        result = self.assert_comparison(
            original, changed, "refused-unrecognized-pointer-slots",
            "refused-unwitnessed-or-unrecognized-pointer-slots",
        )
        self.assertFalse(result["nonpointer_digest_equal"])
        self.assertFalse(result["witnessed_digest_equal"])

    def test_problem_paths_use_json_pointer_escaping(self):
        original = {"a~/b": [{"futureDeclField": "0x1"}], "parentDeclContextId": "0x2"}
        result = comparison.fingerprint_ast(original)
        self.assertEqual(result["problems"]["unrecognized_pointer_slots"],
                         ["/a~0~1b/0/futureDeclField"])
        self.assertIn("/parentDeclContextId", result["problems"]["unwitnessed_pointer_slots"])

    def test_bare_array_pointer_does_not_inherit_recognized_field(self):
        original = {"id": "0x1", "declId": ["0x1"]}
        result = comparison.fingerprint_ast(original)
        self.assertEqual(result["problems"]["unrecognized_pointer_slots"], ["/declId/0"])
        self.assert_comparison(
            original, original, "refused-unrecognized-pointer-slots",
            "refused-unwitnessed-or-unrecognized-pointer-slots",
        )

    def test_problem_on_either_side_refuses_the_comparison(self):
        original = {"id": "0x1"}
        dangling = {"id": "0x1", "declId": "0x99"}
        unknown = {"id": "0x1", "newField": "0x1"}
        for left, right in ((original, dangling), (dangling, original)):
            with self.subTest(left=left, right=right):
                self.assert_comparison(left, right, "different",
                                       "refused-unwitnessed-or-unrecognized-pointer-slots")
        for left, right in ((original, unknown), (unknown, original)):
            with self.subTest(left=left, right=right):
                self.assert_comparison(left, right, "refused-unrecognized-pointer-slots",
                                       "refused-unwitnessed-or-unrecognized-pointer-slots")

    def test_deep_nested_payload_is_completely_visited(self):
        original = nested_ast(1500, "17")
        changed = nested_ast(1500, "18")
        self.assert_comparison(original, changed, "different", "different")
        self.assertEqual(comparison.fingerprint_ast(original)["id_bearing_records"], 1)

    def test_fingerprinting_does_not_mutate_input(self):
        original = fixture_ast()
        before = copy.deepcopy(original)
        comparison.fingerprint_ast(original)
        self.assertEqual(original, before)


class AstComparisonCliTests(unittest.TestCase):
    def setUp(self):
        directory = tempfile.TemporaryDirectory(prefix="cpp-ast-comparison-test-")
        self.addCleanup(directory.cleanup)
        self.root = pathlib.Path(directory.name)
        self.output = self.root / "report.json"

    def write(self, name, contents):
        path = self.root / name
        path.write_text(contents, encoding="utf-8")
        return path

    def envelope(self, name, ast=None):
        return self.write(name, json.dumps({"ast": fixture_ast() if ast is None else ast}))

    def run_cli(self, inputs, output=None, arguments=()):
        command = [sys.executable, str(HERE / "compare_ast.py")]
        command.extend(str(path) for path in inputs)
        command.extend(("--out", str(output or self.output)))
        command.extend(arguments)
        return subprocess.run(command, capture_output=True, text=True, timeout=30)

    def assert_refused_preserving_report(self, inputs, message):
        self.output.write_text("previous complete report\n", encoding="utf-8")
        result = self.run_cli(inputs)
        self.assertEqual(result.returncode, 2, result.stdout)
        self.assertIn("cpp-ast-comparison-refused", result.stderr)
        self.assertIn(message, result.stderr)
        self.assertEqual(self.output.read_text(encoding="utf-8"), "previous complete report\n")
        self.assertEqual(list(self.root.glob(".cpp-ast-comparison-*")), [])

    def test_three_inputs_report_equal_and_changed_complete_payload(self):
        original = fixture_ast()
        renamed = rename_pointers(original, {
            "0x1": "0x11", "0x2": "0x12", "0x3": "0x13", "0x4": "0x14",
        })
        changed = copy.deepcopy(original)
        changed["inner"][1]["inner"][0]["value"] = "18"
        inputs = [self.envelope("original.json", original),
                  self.envelope("renamed.json", renamed),
                  self.envelope("changed.json", changed)]
        before = [path.read_bytes() for path in inputs]
        result = self.run_cli(inputs)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(self.output.read_text(encoding="utf-8"))
        self.assertEqual(report["max_input_bytes"], 64 * 1024 * 1024)
        self.assertEqual(len(report["inputs"]), 3)
        self.assertEqual([row["nonpointer_comparison_status"] for row in report["comparisons"]],
                         ["equal", "different"])
        self.assertEqual([row["witnessed_comparison_status"] for row in report["comparisons"]],
                         ["equal", "different"])
        self.assertEqual([path.read_bytes() for path in inputs], before)
        self.assertEqual(list(self.root.glob(".cpp-ast-comparison-*")), [])

    def test_exit_zero_publishes_diagnostic_report_without_dangling_graph_agreement(self):
        original = {"kind": "TranslationUnitDecl", "inner": [
            {"kind": "LabelStmt", "declId": "0x1"},
            {"kind": "GotoStmt", "targetLabelDeclId": "0x1"},
        ]}
        renamed = rename_pointers(original, {"0x1": "0xA1"})
        inputs = [self.envelope("original.json", original), self.envelope("renamed.json", renamed)]
        result = self.run_cli(inputs)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(self.output.is_file())
        report = json.loads(self.output.read_text(encoding="utf-8"))
        diagnostic = report["comparisons"][0]
        self.assertEqual(diagnostic["nonpointer_comparison_status"], "equal")
        self.assertEqual(diagnostic["witnessed_comparison_status"],
                         "refused-unwitnessed-or-unrecognized-pointer-slots")
        self.assertTrue(diagnostic["witnessed_digest_equal"])
        self.assertEqual(report["inputs"][0]["problems"]["unwitnessed_pointer_slots"],
                         ["/inner/0/declId", "/inner/1/targetLabelDeclId"])
        self.assertEqual(json.loads(result.stdout)["comparisons"], report["comparisons"])

    def test_floating_and_nonfinite_json_numbers_refuse(self):
        original = self.envelope("original.json")
        for token in ("1.0", "1e3", "NaN", "Infinity", "-Infinity"):
            with self.subTest(token=token):
                numeric = self.write("numeric.json", '{"ast":{"kind":"TranslationUnitDecl",'
                                     '"number":' + token + '}}')
                self.assert_refused_preserving_report([original, numeric], "non-integer JSON numeric token")

    def test_duplicate_fields_refuse_including_uncompared_envelope_fields(self):
        original = self.envelope("original.json")
        duplicates = (
            '{"ast":{"kind":"TranslationUnitDecl","kind":"TranslationUnitDecl"}}',
            '{"metadata":{"name":"same","name":"same"},'
            '"ast":{"kind":"TranslationUnitDecl"}}',
        )
        for contents in duplicates:
            with self.subTest(contents=contents):
                duplicated = self.write("duplicated.json", contents)
                self.assert_refused_preserving_report([original, duplicated], "duplicate JSON object field")

    def test_input_must_wrap_translation_unit(self):
        for document in ([], fixture_ast(), {"ast": []}, {"ast": {"kind": "VarDecl"}}):
            with self.subTest(document=document):
                malformed = self.write("malformed.json", json.dumps(document))
                self.assert_refused_preserving_report([malformed], "must wrap a TranslationUnitDecl AST")

    def test_later_missing_input_does_not_publish_partial_report(self):
        original = self.envelope("original.json")
        self.assert_refused_preserving_report([original, self.root / "missing.json"], "missing.json")

    def test_invalid_json_does_not_create_output(self):
        original = self.envelope("original.json")
        malformed = self.write("malformed.json", '{"ast":')
        result = self.run_cli([original, malformed])
        self.assertEqual(result.returncode, 2)
        self.assertFalse(self.output.exists())
        self.assertEqual(list(self.root.glob(".cpp-ast-comparison-*")), [])

    def test_explicit_byte_bound_refuses_before_publication(self):
        oversized = self.envelope("oversized.json", {
            "kind": "TranslationUnitDecl", "name": "large" * 220000,
        })
        self.output.write_text("previous report\n", encoding="utf-8")
        result = self.run_cli([oversized], arguments=("--max-input-mib", "1"))
        self.assertEqual(result.returncode, 2)
        self.assertIn("input exceeds explicit byte bound", result.stderr)
        self.assertEqual(self.output.read_text(encoding="utf-8"), "previous report\n")

    def test_nonpositive_input_bound_refuses(self):
        original = self.envelope("original.json")
        for bound in ("0", "-1"):
            with self.subTest(bound=bound):
                result = self.run_cli([original], arguments=("--max-input-mib", bound))
                self.assertEqual(result.returncode, 2)
                self.assertIn("must be positive", result.stderr)
                self.assertFalse(self.output.exists())

    def test_resolved_and_hardlink_output_aliases_refuse_without_modification(self):
        original = self.envelope("original.json")
        symbolic = self.root / "symbolic.json"
        symbolic.symlink_to(original)
        hardlink = self.root / "hardlink.json"
        os.link(original, hardlink)
        before = original.read_bytes()
        for alias in (original, symbolic, hardlink):
            with self.subTest(alias=alias):
                result = self.run_cli([original], output=alias)
                self.assertEqual(result.returncode, 2)
                self.assertIn("output aliases input", result.stderr)
                self.assertEqual(original.read_bytes(), before)

    def test_missing_output_parent_refuses(self):
        original = self.envelope("original.json")
        output = self.root / "absent" / "report.json"
        result = self.run_cli([original], output=output)
        self.assertEqual(result.returncode, 2)
        self.assertIn("cpp-ast-comparison-refused", result.stderr)
        self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
