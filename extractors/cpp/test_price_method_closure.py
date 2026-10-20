#!/usr/bin/env python3
"""Controls for observed-wall pricing, including positive counterexamples."""

import copy
import json
import os
import shutil
import pathlib
import subprocess
import sys
import tempfile
import unittest

import price_method_closure as pricing

INT = {"kind": "builtin", "name": "int"}
POINTER = {"kind": "pointer", "pointee": INT}


class Fixture:
    def __init__(self, root):
        self.root, self.next = root, 16
        self.source = root / "input.cpp"
        self.source.write_text("// tooling fixture\n", encoding="utf-8")
        self.ast = {"id": "0x1", "kind": "TranslationUnitDecl", "inner": []}
        self.metadata = {"schema_version": pricing.SCHEMA, "declarations": [],
            "type_evidence_api": "Clang::QualType structured type projection v1", "type_evidence": [],
            "expression_types_api": "Clang::Expr type projection v1", "expression_types": [],
            "variable_evidence_api": "Clang::VarDecl storage and initializer projection v1", "variable_evidence": []}
        self.metadata["declarations"].append({"id": "0x1", "canonical": "0x1",
            "kind": "TranslationUnitDecl", "implicit": False, "dependent_context": False,
            "owning_module": None, "lexical_context": None, "semantic_context": None})
        self.record = self.decl("CXXRecordDecl", "Record", self.ast["inner"])
        self.record.update(completeDefinition=True)
        self.record_row = self.row(self.record["id"])
        self.record_row.update(record_shape_api="CXXRecordDecl aggregate member shape v1",
            record_complete=True, record_union=False, record_aggregate=True, record_base_count=0,
            record_trivial_destructor=True, record_user_destructor=False,
            record_attribute_count=0, record_field_count=1, injected_class_name=False,
            described_template=None, described_template_api="CXXRecordDecl.getDescribedClassTemplate")
        self.field = self.decl("FieldDecl", "value", self.record["inner"])
        self.row(self.field["id"]).update(field_index=0, field_parent=self.record["id"],
            field_shape_api="FieldDecl member shape v1", field_mutable=False, field_bitfield=False,
            field_initializer=False, field_attribute_count=0)
        self.type(self.field["id"], INT)

    def id(self):
        self.next += 1
        return hex(self.next)

    def row(self, identifier):
        return next(row for row in self.metadata["declarations"] if row["id"] == identifier)

    def decl(self, kind, name, children):
        identifier = self.id()
        node = {"id": identifier, "kind": kind, "name": name, "inner": []}
        children.append(node)
        parent = self.record["id"] if hasattr(self, "record") and children is self.record["inner"] else "0x1"
        self.metadata["declarations"].append({"id": identifier, "canonical": identifier,
            "name": name, "kind": kind, "implicit": False, "dependent_context": False,
            "owning_module": None, "semantic_context": parent, "lexical_context": parent,
            "function_templated_kind": 0, "template_specialization_kind": 0, "function_attribute_count": 0,
            **{key: False for key in ("function_has_skipped_body", "function_will_have_body",
                "function_has_defining_attr", "function_late_template_parsed", "function_explicitly_defaulted", "deleted_as_written")},
            "source_origin_api": "SourceManager expansion/spelling file locations v1",
            "source_origin": {key: {"file": "input.cpp", "offset": 0} for key in ("expansion", "spelling")}})
        return node

    def type(self, identifier, type_, expression=False, kind=None):
        row = {"occurrence": identifier, "type": copy.deepcopy(type_)}
        row.update({"kind": kind} if expression else {"canonical": identifier})
        self.metadata["expression_types" if expression else "type_evidence"].append(row)

    def expr(self, kind, type_=INT, **fields):
        node = {"id": self.id(), "kind": kind, **fields}
        self.type(node["id"], type_, True, kind)
        return node

    def member(self):
        this = self.expr("CXXThisExpr", {"kind": "pointer", "pointee": {"kind": "record", "declaration": self.record["id"]}})
        return self.expr("MemberExpr", referencedMemberDecl=self.field["id"], isArrow=True, inner=[this])

    def function(self, name="method", method=True, expression=None, body=True):
        node = self.decl("CXXMethodDecl" if method else "FunctionDecl", name,
                         self.record["inner"] if method else self.ast["inner"])
        if method:
            self.row(node["id"]).update(method_static=False, method_shape_api="CXXMethodDecl receiver shape v1",
                method_parent=self.record["id"], method_const=False, method_volatile=False,
                method_virtual=False, method_pure=False, method_ref_qualifier=0,
                method_signature_api="FunctionDecl return and parameter projection v1",
                method_result_type=INT, method_parameter_types=[], method_variadic=False, method_exception_spec=0)
        else:
            self.type(node["id"], {"kind": "function", "result": INT, "parameters": [], "variadic": False})
        if body:
            self.body(node, expression if expression is not None else self.member() if method else self.expr("IntegerLiteral", value="1"))
        return node

    def body(self, node, expression):
        node["inner"] = [{"kind": "CompoundStmt", "inner": [{"kind": "ReturnStmt", "inner": [expression]}]}]

    def call(self, target):
        ref = self.expr("DeclRefExpr", referencedDecl={"id": target["id"], "kind": target["kind"]})
        decay = self.expr("ImplicitCastExpr", castKind="FunctionToPointerDecay", inner=[ref])
        return self.expr("CallExpr", inner=[decay])

    def document(self):
        return {"ast": self.ast, "metadata": self.metadata}

    def report(self):
        return pricing.price_probe(self.document(), [self.source], self.root)


class MethodClosureTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="cpp-method-pricing-")
        self.addCleanup(temporary.cleanup)
        self.root = pathlib.Path(temporary.name)
        self.f = Fixture(self.root)

    def method_row(self, report):
        return next(row for row in report["bodies"] if row["instance"])

    @unittest.skipUnless(os.environ.get("LEANCPP_CLANG") and os.environ.get("LEANCPP_PROBE_LIBRARY"),
                         "set matching compiler and probe for source controls")
    def test_actual_compiler_methods_signatures_fields_and_call_closure(self):
        source = self.root / "real.cpp"
        source.write_text("""int leaf();
int leaf() { return 1; }
int blocked_leaf() { return static_cast<int>(1.0); }
int external();
int recursive_leaf(int value) { if (value) return recursive_leaf(value - 1); return 0; }
struct Plain {
  int value; mutable int cache;
  int get() const { return value; }
  int touch() const { cache = 3; return cache; }
  int direct() { return leaf(); }
  int blocked() { return blocked_leaf(); }
  int ext() { return external(); }
  int recursive() { return recursive_leaf(2); }
};
struct [[gnu::visibility("default")]] Snapshot {
  int value; void *opaque;
  Snapshot() : value(1), opaque(nullptr) {}
  int read() const { return value; }
};
""", encoding="utf-8")
        environment = dict(os.environ, SOURCE_DATE_EPOCH="0")
        environment.pop("CCC_OVERRIDE_OPTIONS", None); environment.pop("CCC_ADD_ARGS", None)
        result = subprocess.run([shutil.which(os.environ["LEANCPP_CLANG"]), "--no-default-config",
            "-std=c++23", "-pedantic-errors", "-fsyntax-only", str(source), "-Xclang", "-load",
            "-Xclang", str(pathlib.Path(os.environ["LEANCPP_PROBE_LIBRARY"]).resolve()), "-Xclang",
            "-plugin", "-Xclang", "leancpp-canonical-probe"], cwd=self.root, env=environment,
            capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        probe = json.loads(result.stdout)
        report = pricing.price_probe(probe, [source], self.root)
        def raw(path):
            node = probe["ast"]
            for index in path:
                node = node["inner"][index]
            return node
        rows = {raw(row["path"]).get("name"): row for row in report["bodies"]}
        self.assertEqual(report["target_explicit_instance_methods"], 7)
        for name in ("get", "touch"):
            self.assertEqual(set(rows[name]["direct_walls"]) - pricing.RECEIVER, set())
            self.assertTrue(rows[name]["receiver_flags"]["method_const"])
        self.assertTrue(any(member["mutable"] for member in rows["touch"]["members"]))
        removed = pricing.SNAPSHOT | pricing.DIRECT_CALL | {"record:attribute:VisibilityAttr"}
        self.assertEqual(set(rows["direct"]["closure_walls"]) - removed, set())
        self.assertIn("node:CXXStaticCastExpr", rows["blocked"]["closure_walls"])
        self.assertNotIn("node:CXXStaticCastExpr", rows["blocked"]["direct_walls"])
        self.assertIn("call:external-body", rows["ext"]["closure_walls"])
        self.assertIn("call:recursive", rows["recursive"]["closure_walls"])
        self.assertIn("record:attribute:VisibilityAttr", rows["read"]["direct_walls"])
        self.assertIn("record:unused-nonintegral-field", rows["read"]["direct_walls"])
        self.assertEqual({wall for wall in rows["read"]["closure_walls"] if wall not in removed
                          and not wall.startswith("record:unused-field-")}, set())

    def test_positive_aggregate_is_clear_only_after_receiver_extension(self):
        self.f.function()
        report = self.f.report()
        self.assertEqual(report["target_explicit_instance_methods"], 1)
        self.assertEqual(set(self.method_row(report)["direct_walls"]), set(pricing.RECEIVER))
        self.assertEqual(report["scenarios"]["aggregate-this-and-members"]["closure"]["clear"], 1)
        self.assertFalse(report["semantic_admission_claimed"])
        self.assertEqual(report["execution"], "not-attempted")

    def test_independent_walls_are_all_retained_and_ranked_by_sole(self):
        method = self.f.function(expression=self.f.expr("FloatingLiteral", value="1.0"))
        self.f.row(method["id"]).update(function_attribute_count=1, method_result_type=POINTER)
        walls = self.method_row(self.f.report())["direct_walls"]
        self.assertTrue({"node:FloatingLiteral", "signature:nonintegral-result", "declaration:function_attribute_count"}.issubset(walls))
        ranking = pricing.rank([{"first", "second"}, {"second"}, {"first", "second"}])
        self.assertEqual(ranking["walls"][0], {"wall": "second", "present": 3, "sole": 1})

    def test_template_and_namespace_scope_walls_survive_receiver_scenarios(self):
        self.f.function()
        self.f.record_row["described_template"] = "0x999"
        self.f.record_row["dependent_context"] = True
        walls = self.method_row(self.f.report())["direct_walls"]
        self.assertTrue({"scope:template-record", "scope:dependent_context"}.issubset(walls))
        namespace = self.f.decl("NamespaceDecl", "hidden", self.f.ast["inner"])
        self.f.row(namespace["id"]).update(inline_namespace=True, anonymous_namespace=False)
        self.f.record_row["semantic_context"] = namespace["id"]
        self.assertIn("scope:inline_namespace", self.method_row(self.f.report())["direct_walls"])
        self.f.record_row["lexical_context"] = self.f.record["id"]
        self.assertIn("scope:context-cycle", self.method_row(self.f.report())["direct_walls"])

    def test_unsequenced_effects_cost_is_distinct_from_supported_comma(self):
        target = self.f.function("target", method=False)
        expression = self.f.expr("BinaryOperator", opcode="+", inner=[self.f.call(target), self.f.expr("IntegerLiteral", value="1")])
        self.f.function(expression=expression)
        self.assertIn("expression:unsequenced-operand-effects", self.method_row(self.f.report())["direct_walls"])
        expression["opcode"] = ","
        self.assertNotIn("expression:unsequenced-operand-effects", self.method_row(self.f.report())["direct_walls"])

    def test_qualified_result_and_existing_local_storage_policies(self):
        method = self.f.function()
        const_int = {"kind": "qualified", "const": True, "volatile": False, "base": INT}
        local = self.f.decl("VarDecl", "local", method["inner"][0]["inner"])
        self.f.type(local["id"], const_int)
        self.f.metadata["variable_evidence"].append({"occurrence": local["id"],
            "storage_duration": "automatic", "tls": "none", "attribute_count": 0,
            "local": True, "local_or_parameter": True, "storage_class": "register", "constexpr": True})
        self.assertFalse(any(wall.startswith("local:") for wall in self.method_row(self.f.report())["direct_walls"]))
        self.f.row(method["id"])["method_result_type"] = const_int
        self.assertIn("signature:qualified-result", self.method_row(self.f.report())["direct_walls"])
        self.f.metadata["type_evidence"][-1]["type"] = INT
        self.assertIn("local:constexpr", self.method_row(self.f.report())["direct_walls"])

    def test_nonaggregate_snapshot_distinguishes_unused_and_used_pointer_fields(self):
        self.f.function()
        unused = self.f.decl("FieldDecl", "opaque", self.f.record["inner"])
        self.f.row(unused["id"]).update(field_index=1, field_parent=self.f.record["id"],
            field_mutable=False, field_bitfield=False, field_initializer=False, field_attribute_count=0)
        self.f.record_row.update(record_field_count=2, record_aggregate=False, record_user_destructor=True)
        self.f.type(unused["id"], POINTER)
        report = self.f.report()
        self.assertEqual(report["scenarios"]["aggregate-this-and-members"]["direct"]["clear"], 0)
        self.assertEqual(report["scenarios"]["existing-receiver-integral-projection"]["direct"]["clear"], 1)
        self.f.metadata["type_evidence"][0]["type"] = POINTER
        self.assertIn("member:nonintegral-field", self.method_row(self.f.report())["direct_walls"])

    def test_visibility_is_a_separate_explicit_scenario(self):
        self.f.function()
        self.f.record_row.update(record_aggregate=False, record_attribute_count=1)
        self.f.record["inner"].append({"kind": "VisibilityAttr"})
        report = self.f.report()
        self.assertIn("record:attribute:VisibilityAttr", self.method_row(report)["direct_walls"])
        self.assertEqual(report["scenarios"]["existing-receiver-integral-projection"]["direct"]["clear"], 0)
        self.assertEqual(report["scenarios"]["existing-receiver-projection-and-visibility"]["direct"]["clear"], 1)

    def test_const_mutable_receiver_observations_are_not_printed_type_parsing(self):
        method = self.f.function()
        self.f.row(method["id"])["method_const"] = True
        self.f.row(self.f.field["id"])["field_mutable"] = True
        row = self.method_row(self.f.report())
        self.assertTrue(row["receiver_flags"]["method_const"])
        self.assertTrue(row["members"][0]["mutable"])

    def test_non_this_and_escaped_this_are_distinct(self):
        member = self.f.member()
        member["inner"][0]["kind"] = "IntegerLiteral"
        method = self.f.function(expression=member)
        self.assertIn("member:non-this-base", self.method_row(self.f.report())["direct_walls"])
        self.f.body(method, self.f.expr("CXXThisExpr", POINTER))
        self.assertIn("receiver:escaped-this", self.method_row(self.f.report())["direct_walls"])

    def test_base_record_identity_mismatch_stays_a_wall(self):
        member = self.f.member()
        other = self.f.decl("CXXRecordDecl", "Other", self.f.ast["inner"])
        next(row for row in self.f.metadata["expression_types"] if row["occurrence"] == member["inner"][0]["id"])["type"]["pointee"]["declaration"] = other["id"]
        self.f.function(expression=member)
        self.assertIn("member:receiver-type-mismatch", self.method_row(self.f.report())["direct_walls"])

    def test_clean_direct_call_and_transitive_unsupported_body(self):
        target = self.f.function("target", method=False)
        caller = self.f.function(expression=self.f.call(target))
        scenario = "existing-receiver-projection-visibility-and-direct-calls"
        self.assertEqual(self.f.report()["scenarios"][scenario]["closure"]["clear"], 1)
        self.f.body(target, self.f.expr("FloatingLiteral", value="2.0"))
        report = self.f.report()
        self.assertEqual(report["scenarios"][scenario]["direct"]["clear"], 1)
        self.assertEqual(report["scenarios"][scenario]["closure"]["clear"], 0)
        self.assertIn("node:FloatingLiteral", self.method_row(report)["closure_walls"])

    def test_external_and_indirect_targets_never_gain_native_contracts(self):
        target = self.f.function("external", method=False, body=False)
        method = self.f.function(expression=self.f.call(target))
        self.assertIn("call:external-body", self.method_row(self.f.report())["closure_walls"])
        expression = self.f.call(target)
        expression["inner"][0]["inner"][0]["referencedDecl"]["id"] = self.f.field["id"]
        self.f.body(method, expression)
        self.assertIn("call:unresolved-or-indirect", self.method_row(self.f.report())["closure_walls"])

    def test_canonical_redeclaration_finds_body_but_same_name_does_not(self):
        prototype = self.f.function("overload", method=False, body=False)
        definition = self.f.function("overload", method=False)
        self.f.row(definition["id"])["canonical"] = prototype["id"]
        self.f.function(expression=self.f.call(prototype))
        row = self.method_row(self.f.report())
        self.assertNotIn("call:external-body", row["direct_walls"])
        self.f.row(definition["id"])["canonical"] = definition["id"]
        self.assertIn("call:external-body", self.method_row(self.f.report())["direct_walls"])

    def test_recursive_callee_cost_propagates_to_its_caller(self):
        a = self.f.function("a", method=False)
        b = self.f.function("b", method=False)
        self.f.body(a, self.f.call(b)); self.f.body(b, self.f.call(a))
        self.f.function(expression=self.f.call(a))
        self.assertIn("call:recursive", self.method_row(self.f.report())["closure_walls"])

    def test_duplicate_occurrences_are_preserved(self):
        method = self.f.function()
        self.f.record["inner"].append(copy.deepcopy(method))
        report = self.f.report()
        self.assertEqual(report["body_occurrences"], 2)
        self.assertEqual(report["scenarios"]["aggregate-this-and-members"]["direct"]["clear"], 2)

    def test_missing_and_conflicting_evidence_never_clear(self):
        method = self.f.function()
        self.f.row(method["id"]).pop("method_shape_api")
        self.f.metadata["type_evidence"].append({"occurrence": self.f.field["id"], "canonical": self.f.field["id"], "type": POINTER})
        walls = self.method_row(self.f.report())["direct_walls"]
        self.assertIn("evidence:method-shape-api", walls)
        self.assertIn("evidence:conflicting-type:type", walls)
        self.f.metadata["declarations"].append({**self.f.row(method["id"]), "canonical": "0xffff"})
        self.assertIn("evidence:conflicting-declaration:canonical", self.method_row(self.f.report())["direct_walls"])

    def test_bad_numeric_boolean_flags_and_unknown_static_remain_visible(self):
        method = self.f.function()
        self.f.row(self.f.field["id"])["field_index"] = False
        self.f.row(method["id"])["method_ref_qualifier"] = False
        walls = self.method_row(self.f.report())["direct_walls"]
        self.assertIn("record:field-order-or-owner", walls)
        self.assertIn("receiver:ref-qualified-or-unestablished", walls)
        self.f.row(method["id"]).pop("method_static")
        report = self.f.report()
        self.assertEqual(report["target_unestablished_method_static"], 1)
        self.assertEqual(report["body_occurrences"], 1)

    def test_source_dependency_mixed_unknown_and_symlink_identity(self):
        method = self.f.function()
        other = self.root / "dependency.cpp"; other.write_text("", encoding="utf-8")
        origin = self.f.row(method["id"])["source_origin"]
        origin["spelling"]["file"] = str(other)
        self.assertEqual(self.f.report()["ownership_counts"], {"mixed-macro": 1})
        origin["expansion"]["file"] = str(other)
        self.assertEqual(self.f.report()["ownership_counts"], {"dependency": 1})
        origin["expansion"] = None
        self.assertEqual(self.f.report()["ownership_counts"], {"unknown-origin": 1})
        alias = self.root / "alias.cpp"; alias.symlink_to(self.f.source)
        origin.update(expansion={"file": str(alias), "offset": 0}, spelling={"file": str(alias), "offset": 0})
        self.assertEqual(self.f.report()["ownership_counts"], {"target-source": 1})

    def cli(self, contents, *options, output=None):
        source = self.root / "probe.json"; source.write_bytes(contents if isinstance(contents, bytes) else contents.encode())
        out = output or self.root / "report.json"
        result = subprocess.run([sys.executable, str(pathlib.Path(pricing.__file__)), str(source),
            "--sources", str(self.f.source), "--capture-dir", str(self.root), "--out", str(out), *options],
            capture_output=True, text=True, timeout=10)
        return result, out

    def test_baseline_source_drift_refuses_instead_of_silent_profile_drift(self):
        repo = pathlib.Path(pricing.__file__).resolve().parents[2]
        for name in pricing.BASELINE_MODEL_SHA256:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((repo / name).read_bytes())
        pricing.verify_baseline(self.root)
        (self.root / next(iter(pricing.BASELINE_MODEL_SHA256))).write_text("changed")
        with self.assertRaisesRegex(ValueError, "pricing baseline changed"):
            pricing.verify_baseline(self.root)

    def test_missing_origin_component_refuses_and_null_is_unknown(self):
        method = self.f.function()
        origin = self.f.row(method["id"])["source_origin"]
        origin.pop("spelling")
        with self.assertRaisesRegex(ValueError, "missing physical source"):
            self.f.report()
        origin["spelling"] = None
        self.assertEqual(self.f.report()["ownership_counts"], {"unknown-origin": 1})

    def test_used_field_type_absence_is_not_removed_by_snapshot_scenario(self):
        self.f.function()
        self.f.metadata["type_evidence"] = []
        report = self.f.report()
        self.assertEqual(report["scenarios"]["existing-receiver-projection-visibility-and-direct-calls"]["direct"]["clear"], 0)
        self.assertTrue(any(wall.startswith("record:used-field-evidence:missing")
                            for wall in self.method_row(report)["direct_walls"]))

    def test_cli_pins_input_tool_and_omits_source_names_and_paths(self):
        self.f.function("private_method_marker")
        result, out = self.cli(json.dumps(self.f.document()))
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads(out.read_text())
        self.assertEqual(len(report["input_sha256"]), 64)
        self.assertEqual(len(report["tool_sha256"]), 64)
        self.assertNotIn("private_method_marker", out.read_text())
        self.assertNotIn(str(self.root), out.read_text())

    def test_cli_invalid_json_utf8_surrogates_floats_and_schema_do_not_publish(self):
        for data in ('{"ast":{},"ast":{}}', b'\xff', '{"x":"\\ud800"}', '{"x":1.5}', '{"x":NaN}', '{}'):
            with self.subTest(data=data):
                result, out = self.cli(data)
                self.assertEqual(result.returncode, 2)
                self.assertFalse(out.exists())

    def test_cli_bounds_aliases_and_failure_preserve_existing_report(self):
        self.f.function()
        content = json.dumps(self.f.document())
        result, out = self.cli(content, output=self.root / "probe.json")
        self.assertEqual(result.returncode, 2)
        self.assertEqual(out.read_text(), content)
        result, out = self.cli(b" " * (1024 * 1024 + 1), "--max-input-mib", "1")
        self.assertEqual(result.returncode, 2)
        self.assertFalse((self.root / "report.json").exists())
        out = self.root / "report.json"; out.write_text("unchanged")
        result, out = self.cli('{"duplicate":1,"duplicate":2}')
        self.assertEqual(result.returncode, 2)
        self.assertEqual(out.read_text(), "unchanged")


if __name__ == "__main__":
    unittest.main()
