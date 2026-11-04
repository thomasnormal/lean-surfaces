#!/usr/bin/env python3
"""Check local-declaration pricing without claiming C++ semantic admission."""

import copy
import importlib.util
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest


HERE = pathlib.Path(__file__).resolve().parent
MODULE_SPEC = importlib.util.spec_from_file_location(
    "cpp_price_local_declarations_under_test", HERE / "price_local_declarations.py",
)
pricing = importlib.util.module_from_spec(MODULE_SPEC)
sys.modules[MODULE_SPEC.name] = pricing
MODULE_SPEC.loader.exec_module(pricing)


def body(kinds, kind="FunctionDecl", ownership="target-source", implicit=False):
    return {"kind": kind, "ownership": ownership, "is_implicit": implicit, "body_kinds": kinds}


def inventory(rows):
    return {"schema": pricing.INPUT_SCHEMA, "revision": "0" * 40,
            "counting_rule": "body occurrences", "functions": rows}


class LocalDeclarationPricingTests(unittest.TestCase):
    def test_empty_inventory_claims_no_admission(self):
        report = pricing.price_inventory(inventory([]))
        self.assertEqual(report["body_occurrences"], 0)
        self.assertFalse(report["semantic_admission_claimed"])
        self.assertEqual(report["execution"], "not-attempted")

    def test_ownership_implicit_and_method_filters_remain_separate(self):
        kinds = {"CompoundStmt": 1, "DeclStmt": 1, "VarDecl": 1, "ReturnStmt": 1}
        report = pricing.price_inventory(inventory([
            body(kinds), body(kinds, implicit=True), body(kinds, kind="CXXMethodDecl"),
            body(kinds, ownership="external-dependency"),
        ]))
        self.assertEqual(report["body_occurrences"], 3)
        self.assertEqual(report["nonimplicit_body_occurrences"], 2)
        self.assertEqual(report["nonimplicit_declstmt_bodies"], 2)
        self.assertEqual(report["ordinary_declstmt_bodies"], 1)
        self.assertEqual(report["ordinary_declstmt_kind_only_candidates"], 1)

    def test_remaining_kinds_count_presence_not_node_occurrences(self):
        report = pricing.price_inventory(inventory([
            body({"DeclStmt": 3, "CallExpr": 9, "MemberExpr": 2}),
            body({"DeclStmt": 1, "CallExpr": 1}),
            body({"ReturnStmt": 1}),
        ]))
        self.assertEqual(report["remaining_kind_presence"], {"CallExpr": 2, "MemberExpr": 1})
        self.assertEqual(report["ordinary_declstmt_kind_only_candidates"], 0)
        self.assertEqual(sum(row["bodies"] for row in report["remaining_kind_sets"]), 2)

    def test_occurrence_duplicates_are_not_deduplicated(self):
        row = body({"DeclStmt": 1, "VarDecl": 1})
        report = pricing.price_inventory(inventory([row, copy.deepcopy(row)]))
        self.assertEqual(report["ordinary_declstmt_bodies"], 2)

    def test_empty_for_placeholders_do_not_create_a_false_wall(self):
        report = pricing.price_inventory(inventory([
            body({"DeclStmt": 1, "ForStmt": 1, "<missing>": 1}),
        ]))
        self.assertEqual(report["ordinary_declstmt_kind_only_candidates"], 1)
        self.assertEqual(report["ordinary_declstmt_context_dependent_bodies"], 1)

    def test_declaration_presence_does_not_assert_a_variable(self):
        report = pricing.price_inventory(inventory([body({"DeclStmt": 1, "TypeAliasDecl": 1})]))
        self.assertEqual(report["ordinary_declstmt_bodies"], 1)
        self.assertEqual(report["remaining_kind_presence"], {"TypeAliasDecl": 1})

    def test_external_dependency_selection_is_explicit(self):
        report = pricing.price_inventory(inventory([
            body({"DeclStmt": 1}), body({"DeclStmt": 1}, ownership="external-dependency"),
        ]), "external-dependency")
        self.assertEqual(report["body_occurrences"], 1)
        self.assertEqual(report["ownership"], "external-dependency")

    def test_malformed_and_unknown_inventory_fields_refuse(self):
        original = inventory([body({"DeclStmt": 1})])
        changes = (
            ("schema", "unknown"), ("revision", "/private/revision"), ("counting_rule", None),
            ("functions", None),
        )
        for field, value in changes:
            with self.subTest(field=field):
                document = copy.deepcopy(original)
                document[field] = value
                with self.assertRaises(ValueError):
                    pricing.price_inventory(document)
        for field, value in (("kind", "FutureDecl"), ("ownership", "unknown"),
                             ("is_implicit", 0), ("body_kinds", [])):
            with self.subTest(field=field):
                document = copy.deepcopy(original)
                document["functions"][0][field] = value
                with self.assertRaises(ValueError):
                    pricing.price_inventory(document)
        for value in (None, [], {}, True):
            with self.subTest(kind=value):
                document = copy.deepcopy(original)
                document["functions"][0]["kind"] = value
                with self.assertRaises(ValueError):
                    pricing.price_inventory(document)

    def test_invalid_counts_and_unselected_rows_refuse(self):
        for count in (True, 0, -1, 1.5, "1"):
            with self.subTest(count=count):
                with self.assertRaises(ValueError):
                    pricing.price_inventory(inventory([
                        body({"DeclStmt": count}, ownership="external-dependency"),
                    ]))

    def run_cli(self, source, output, *options):
        return subprocess.run([
            sys.executable, str(HERE / "price_local_declarations.py"), str(source),
            "--out", str(output), *options,
        ], capture_output=True, text=True, timeout=10)

    def test_cli_pins_input_and_does_not_copy_source_names_or_paths(self):
        with tempfile.TemporaryDirectory(prefix="cpp-local-pricing-") as directory:
            source = pathlib.Path(directory) / "inventory.json"
            output = pathlib.Path(directory) / "pricing.json"
            document = inventory([body({"DeclStmt": 1})])
            document["corpus"] = "private-input-label"
            document["functions"][0]["name"] = "private-function-name"
            document["functions"][0]["source_file"] = "/private/source.cpp"
            source.write_text(json.dumps(document), encoding="utf-8")
            result = self.run_cli(source, output)
            self.assertEqual(result.returncode, 0, result.stderr)
            report = json.loads(output.read_text(encoding="utf-8"))
            self.assertEqual(report["input_bytes"], source.stat().st_size)
            self.assertEqual(len(report["input_sha256"]), 64)
            self.assertNotIn("private-", output.read_text(encoding="utf-8"))
            self.assertNotIn("/private/", output.read_text(encoding="utf-8"))

    def test_cli_duplicate_keys_refuse_without_replacing_report(self):
        with tempfile.TemporaryDirectory(prefix="cpp-local-pricing-") as directory:
            source = pathlib.Path(directory) / "inventory.json"
            output = pathlib.Path(directory) / "pricing.json"
            source.write_text('{"schema": "old", "schema": "new"}', encoding="utf-8")
            output.write_text("unchanged", encoding="utf-8")
            result = self.run_cli(source, output)
            self.assertEqual(result.returncode, 2)
            self.assertIn("duplicate JSON object field", result.stderr)
            self.assertEqual(output.read_text(encoding="utf-8"), "unchanged")

    def test_cli_alias_and_byte_bound_refuse(self):
        with tempfile.TemporaryDirectory(prefix="cpp-local-pricing-") as directory:
            source = pathlib.Path(directory) / "inventory.json"
            output = pathlib.Path(directory) / "pricing.json"
            contents = json.dumps(inventory([]))
            source.write_text(contents, encoding="utf-8")
            result = self.run_cli(source, source)
            self.assertEqual(result.returncode, 2)
            self.assertEqual(source.read_text(encoding="utf-8"), contents)
            source.write_bytes(b" " * (1024 * 1024 + 1))
            result = self.run_cli(source, output, "--max-input-mib", "1")
            self.assertEqual(result.returncode, 2)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
