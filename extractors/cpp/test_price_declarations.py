#!/usr/bin/env python3
"""Exercise declaration-query pricing evidence, not C++ semantic admission."""

import copy
import collections
import importlib.util
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest


HERE = pathlib.Path(__file__).resolve().parent
MODULE_SPEC = importlib.util.spec_from_file_location(
    "cpp_price_declarations_under_test", HERE / "price_declarations.py",
)
pricing = importlib.util.module_from_spec(MODULE_SPEC)
sys.modules[MODULE_SPEC.name] = pricing
MODULE_SPEC.loader.exec_module(pricing)

QUERIES = ("canonical-node", "contexts", "definition", "linkage")
FAMILIES = (
    "TranslationUnitDecl", "NamespaceDecl", "FunctionDecl", "VarDecl",
    "EnumDecl", "CXXRecordDecl",
)


def raw_declaration(identifier, kind, name="item", children=None):
    result = {"id": identifier, "kind": kind, "name": name}
    if kind != "TranslationUnitDecl":
        result["loc"] = {"line": 3, "col": 1, "file": "fixture.cpp"}
    if children is not None:
        result["inner"] = children
    return result


def metadata_row(identifier, kind, context="0x1"):
    result = {
        "id": identifier, "kind": kind, "name": "item",
        "canonical": identifier, "previous": None,
        "semantic_context": context, "lexical_context": context,
        "implicit": False, "dependent_context": False, "owning_module": None,
        "definition": None, "definition_api": "not-queried",
        "linkage_internal": "External", "linkage_formal": "External",
    }
    if kind == "TranslationUnitDecl":
        result.update(semantic_context=None, lexical_context=None)
        del result["linkage_internal"]
        del result["linkage_formal"]
    if kind == "NamespaceDecl":
        result.update(original_namespace=identifier, inline_namespace=False,
                      anonymous_namespace=False)
    if kind == "FunctionDecl":
        result.update(definition=True,
                      definition_api="FunctionDecl.isThisDeclarationADefinition",
                      body_present=True, defaulted=False, deleted_as_written=False,
                      language_linkage="C++", template_specialization_kind=0,
                      template_specialization_kind_api="FunctionDecl.getTemplateSpecializationKind",
                      function_templated_kind=0,
                      function_templated_kind_api="FunctionDecl.getTemplatedKind")
    if kind == "VarDecl":
        result.update(definition_api="VarDecl.isThisDeclarationADefinition",
                      variable_definition_kind=2, language_linkage="C++")
    if kind in ("EnumDecl", "CXXRecordDecl"):
        result.update(definition=True,
                      definition_api="TagDecl.isThisDeclarationADefinition")
    if kind == "CXXRecordDecl":
        result.update(injected_class_name=False, represented_class=None)
    if kind in ("VarDecl", "CXXRecordDecl"):
        described_api = ("VarDecl.getDescribedVarTemplate" if kind == "VarDecl"
                         else "CXXRecordDecl.getDescribedClassTemplate")
        result.update(described_template=None, described_template_api=described_api)
    if kind in ("VarDecl", "CXXRecordDecl", "EnumDecl"):
        result.update(template_specialization_kind=0,
                      template_specialization_kind_api=kind + ".getTemplateSpecializationKind")
    return result


def fixture(kind="FunctionDecl"):
    source = raw_declaration("0x3", kind)
    namespace = raw_declaration("0x2", "NamespaceDecl", "scope", [source])
    ast = raw_declaration("0x1", "TranslationUnitDecl", children=[namespace])
    rows = [metadata_row("0x1", "TranslationUnitDecl"),
            metadata_row("0x2", "NamespaceDecl"),
            metadata_row("0x3", kind, "0x2")]
    return ast, rows


def source_node(ast):
    return ast["inner"][0]["inner"][0]


def probe_document(ast, rows):
    return {"ast": ast, "metadata": {
        "schema_version": "cpp-canonical-probe-0.2",
        "compiled_frontend": "21.1.8",
        "runtime_frontend": "clang version 21.1.8",
        "llvm_headers": "21.1.8", "declarations": rows,
    }}


def canonical_parent_occurrence_fixture():
    ast, rows = fixture()
    source_namespace = ast["inner"][0]
    source_namespace["name"] = "inner"
    original_namespace = raw_declaration("0x4", "NamespaceDecl", "inner")
    ast["inner"] = [
        raw_declaration("0x5", "NamespaceDecl", "outer", [source_namespace]),
        raw_declaration("0x7", "NamespaceDecl", "outer", [original_namespace]),
        raw_declaration("0x6", "NamespaceDecl", "outer"),
    ]
    rows[1].update(name="inner", canonical="0x4", previous="0x4",
                   original_namespace="0x4", semantic_context="0x5", lexical_context="0x5")
    rows.extend([metadata_row("0x4", "NamespaceDecl", "0x7"),
                 metadata_row("0x5", "NamespaceDecl"),
                 metadata_row("0x6", "NamespaceDecl"),
                 metadata_row("0x7", "NamespaceDecl")])
    rows[3]["name"] = "inner"
    for row in rows[4:]:
        row["name"] = "outer"
    for ordinal in (4, 6):
        rows[ordinal].update(canonical="0x6", previous="0x6", original_namespace="0x6")
    return ast, rows


class DeclarationPricingTests(unittest.TestCase):
    def query(self, ast, rows, query="canonical-node", identifier="0x3"):
        return pricing.price_query(pricing.build_index(ast, rows), identifier, query)

    def assert_eligible(self, result):
        self.assertEqual(result["status"], "eligible-tooling-evidence")
        self.assertEqual(result["reasons"], [])
        self.assertIsInstance(result["evidence"], dict)

    def assert_refused(self, result):
        self.assertEqual(result["status"], "refused")
        self.assertTrue(result["reasons"])
        self.assertTrue(all(isinstance(reason, str) and reason
                            for reason in result["reasons"]))

    def test_ordinary_function_has_four_tooling_candidates(self):
        ast, rows = fixture()
        for query in QUERIES:
            with self.subTest(query=query):
                self.assert_eligible(self.query(ast, rows, query))

    def test_supported_raw_families_have_canonical_candidates(self):
        for kind in FAMILIES:
            with self.subTest(kind=kind):
                ast, rows = fixture(kind)
                if kind == "TranslationUnitDecl":
                    self.assert_eligible(self.query(ast, rows, identifier="0x1"))
                else:
                    self.assert_eligible(self.query(ast, rows))

    def test_unsupported_family_refuses_without_name_guessing(self):
        ast, rows = fixture("CXXMethodDecl")
        for query in QUERIES:
            with self.subTest(query=query):
                self.assert_refused(self.query(ast, rows, query))

    def test_missing_raw_source_refuses(self):
        ast, rows = fixture()
        self.assert_refused(self.query(ast, rows, identifier="0x99"))

    def test_missing_metadata_source_refuses(self):
        ast, rows = fixture()
        self.assert_refused(self.query(ast, rows[:-1]))

    def test_metadata_only_source_is_not_a_witness(self):
        ast, rows = fixture()
        rows.append(metadata_row("0x99", "FunctionDecl", "0x2"))
        self.assert_refused(self.query(ast, rows, identifier="0x99"))

    def test_unrelated_raw_and_metadata_holes_do_not_block_source(self):
        ast, rows = fixture()
        ast["inner"].append(raw_declaration("0x90", "ImplicitConceptSpecializationDecl"))
        rows.append(metadata_row("0x91", "ParmVarDecl"))
        self.assert_eligible(self.query(ast, rows))

    def test_consistent_duplicate_metadata_rows_are_allowed(self):
        ast, rows = fixture()
        rows.append(copy.deepcopy(rows[-1]))
        self.assert_eligible(self.query(ast, rows))

    def test_relevant_duplicate_metadata_conflict_refuses(self):
        ast, rows = fixture()
        duplicate = copy.deepcopy(rows[-1])
        duplicate["canonical"] = "0x2"
        rows.append(duplicate)
        self.assert_refused(self.query(ast, rows))

    def test_irrelevant_definition_conflict_does_not_block_canonical_query(self):
        ast, rows = fixture()
        duplicate = copy.deepcopy(rows[-1])
        duplicate["definition"] = False
        rows.append(duplicate)
        self.assert_eligible(self.query(ast, rows))
        self.assert_refused(self.query(ast, rows, "definition"))

    def test_raw_and_metadata_kinds_must_match(self):
        ast, rows = fixture()
        rows[-1]["kind"] = "VarDecl"
        self.assert_refused(self.query(ast, rows))

    def test_every_raw_occurrence_kind_is_checked(self):
        ast, rows = fixture()
        ast["inner"].append({"reference": {"id": "0x3", "kind": "VarDecl"}})
        self.assert_refused(self.query(ast, rows))

    def test_skeletal_occurrence_does_not_erase_full_witness(self):
        ast, rows = fixture()
        ast["inner"].append({"reference": {"id": "0x3", "kind": "FunctionDecl"}})
        self.assert_eligible(self.query(ast, rows))

    def test_skeletal_only_source_refuses(self):
        ast, rows = fixture()
        del source_node(ast)["loc"]
        self.assert_refused(self.query(ast, rows))

    def test_range_is_a_complete_source_witness(self):
        ast, rows = fixture()
        node = source_node(ast)
        del node["loc"]
        node["range"] = {"begin": {"line": 3}, "end": {"line": 4}}
        self.assert_eligible(self.query(ast, rows))

    def test_missing_field_is_not_explicit_null(self):
        ast, rows = fixture()
        del rows[-1]["previous"]
        self.assert_refused(self.query(ast, rows))

    def test_missing_and_null_metadata_rows_conflict(self):
        ast, rows = fixture()
        duplicate = copy.deepcopy(rows[-1])
        del duplicate["previous"]
        rows.append(duplicate)
        self.assert_refused(self.query(ast, rows))

    def test_bool_is_not_a_pointer_or_specialization_integer(self):
        for field, value in (("canonical", True), ("template_specialization_kind", False)):
            with self.subTest(field=field):
                ast, rows = fixture()
                rows[-1][field] = value
                self.assert_refused(self.query(ast, rows))

    def test_canonical_target_requires_raw_and_metadata_witnesses(self):
        ast, rows = fixture()
        rows[-1]["canonical"] = "0x99"
        self.assert_refused(self.query(ast, rows))
        rows.append(metadata_row("0x99", "FunctionDecl", "0x2"))
        self.assert_refused(self.query(ast, rows))

    def test_canonical_target_requires_complete_raw_witness(self):
        ast, rows = fixture()
        ast["inner"].append({"id": "0x4", "kind": "FunctionDecl"})
        rows.append(metadata_row("0x4", "FunctionDecl", "0x2"))
        rows[2]["canonical"] = "0x4"
        self.assert_refused(self.query(ast, rows))

    def test_canonical_root_must_be_self_canonical(self):
        ast, rows = fixture()
        ast["inner"].append(raw_declaration("0x4", "FunctionDecl"))
        rows.append(metadata_row("0x4", "FunctionDecl", "0x2"))
        rows[2]["canonical"] = "0x4"
        rows[3]["canonical"] = "0x3"
        self.assert_refused(self.query(ast, rows))

    def test_canonical_family_mismatch_refuses(self):
        ast, rows = fixture()
        rows[-1]["canonical"] = "0x2"
        self.assert_refused(self.query(ast, rows))

    def test_complete_predecessor_chain_has_canonical_candidate(self):
        ast, rows = fixture()
        ast["inner"][0]["inner"].append(raw_declaration("0x4", "FunctionDecl"))
        successor = metadata_row("0x4", "FunctionDecl", "0x2")
        successor.update(canonical="0x3", previous="0x3")
        rows.append(successor)
        self.assert_eligible(self.query(ast, rows, identifier="0x4"))

    def test_dangling_predecessor_refuses(self):
        ast, rows = fixture()
        rows[-1]["previous"] = "0x99"
        self.assert_refused(self.query(ast, rows))

    def test_predecessor_self_cycle_refuses(self):
        ast, rows = fixture()
        rows[-1]["previous"] = "0x3"
        self.assert_refused(self.query(ast, rows))

    def test_predecessor_two_node_cycle_refuses(self):
        ast, rows = fixture()
        ast["inner"][0]["inner"].append(raw_declaration("0x4", "FunctionDecl"))
        successor = metadata_row("0x4", "FunctionDecl", "0x2")
        successor.update(canonical="0x3", previous="0x3")
        rows[-1]["previous"] = "0x4"
        rows.append(successor)
        self.assert_refused(self.query(ast, rows, identifier="0x4"))

    def test_predecessor_canonical_disagreement_refuses(self):
        ast, rows = fixture()
        ast["inner"][0]["inner"].append(raw_declaration("0x4", "FunctionDecl"))
        successor = metadata_row("0x4", "FunctionDecl", "0x2")
        successor["previous"] = "0x3"
        rows.append(successor)
        self.assert_refused(self.query(ast, rows, identifier="0x4"))

    def test_contexts_need_complete_namespace_and_root_witnesses(self):
        ast, rows = fixture()
        rows[-1]["semantic_context"] = "0x99"
        self.assert_refused(self.query(ast, rows, "contexts"))
        rows.append(metadata_row("0x99", "NamespaceDecl"))
        self.assert_refused(self.query(ast, rows, "contexts"))

    def test_context_kind_cannot_be_a_function(self):
        ast, rows = fixture()
        rows[-1]["semantic_context"] = "0x3"
        self.assert_refused(self.query(ast, rows, "contexts"))

    def test_context_chain_cycle_refuses(self):
        ast, rows = fixture()
        rows[1]["semantic_context"] = "0x2"
        self.assert_refused(self.query(ast, rows, "contexts"))

    def test_lexical_context_is_not_inferred_from_semantic_context(self):
        ast, rows = fixture()
        del rows[-1]["lexical_context"]
        self.assert_refused(self.query(ast, rows, "contexts"))

    def test_nonroot_null_context_refuses(self):
        ast, rows = fixture()
        rows[-1]["semantic_context"] = None
        self.assert_refused(self.query(ast, rows, "contexts"))

    def test_dependent_source_and_context_refuse(self):
        for ordinal in (1, 2):
            with self.subTest(ordinal=ordinal):
                ast, rows = fixture()
                rows[ordinal]["dependent_context"] = True
                self.assert_refused(self.query(ast, rows, "contexts"))

    def test_module_ownership_requires_explicit_null(self):
        for value in ("module.fixture", "", False):
            with self.subTest(value=value):
                ast, rows = fixture()
                rows[-1]["owning_module"] = value
                self.assert_refused(self.query(ast, rows))
        ast, rows = fixture()
        del rows[-1]["owning_module"]
        self.assert_refused(self.query(ast, rows))

    def test_template_wrapper_ancestor_refuses(self):
        ast, rows = fixture()
        namespace = ast["inner"][0]
        namespace["inner"] = [raw_declaration(
            "0x4", "FunctionTemplateDecl", children=[source_node(ast)],
        )]
        self.assert_refused(self.query(ast, rows))

    def test_nonzero_function_specialization_refuses(self):
        ast, rows = fixture()
        rows[-1]["template_specialization_kind"] = 1
        self.assert_refused(self.query(ast, rows))

    def test_injected_name_is_not_merged_with_represented_class(self):
        ast, rows = fixture("CXXRecordDecl")
        ast["inner"][0]["inner"].append(raw_declaration("0x4", "CXXRecordDecl"))
        rows.append(metadata_row("0x4", "CXXRecordDecl", "0x2"))
        rows[2].update(injected_class_name=True, represented_class="0x4")
        self.assert_refused(self.query(ast, rows))
        self.assert_eligible(self.query(ast, rows, identifier="0x4"))

    def test_definition_booleans_work_for_function_and_tags(self):
        for kind in ("FunctionDecl", "EnumDecl", "CXXRecordDecl"):
            for value in (True, False):
                with self.subTest(kind=kind, value=value):
                    ast, rows = fixture(kind)
                    rows[-1]["definition"] = value
                    self.assert_eligible(self.query(ast, rows, "definition"))

    def test_definition_true_does_not_require_body_present(self):
        ast, rows = fixture()
        rows[-1].update(body_present=False, defaulted=True)
        self.assert_eligible(self.query(ast, rows, "definition"))

    def test_definition_rejects_nonboolean_and_absent_payload(self):
        for value in (None, 0, 1, "true"):
            with self.subTest(value=value):
                ast, rows = fixture()
                rows[-1]["definition"] = value
                self.assert_refused(self.query(ast, rows, "definition"))
        ast, rows = fixture()
        del rows[-1]["definition"]
        self.assert_refused(self.query(ast, rows, "definition"))

    def test_definition_api_must_match_family(self):
        ast, rows = fixture()
        rows[-1]["definition_api"] = "TagDecl.isThisDeclarationADefinition"
        self.assert_refused(self.query(ast, rows, "definition"))

    def test_variable_definition_enum_is_never_boolean_coerced(self):
        for value in (0, 1, 2):
            with self.subTest(value=value):
                ast, rows = fixture("VarDecl")
                rows[-1]["variable_definition_kind"] = value
                self.assert_refused(self.query(ast, rows, "definition"))
                self.assert_eligible(self.query(ast, rows))

    def test_not_queried_definition_api_refuses(self):
        ast, rows = fixture("NamespaceDecl")
        self.assert_refused(self.query(ast, rows, "definition"))

    def test_language_linkage_values_remain_named_telemetry(self):
        for language in ("C", "C++", "None"):
            with self.subTest(language=language):
                ast, rows = fixture()
                rows[-1]["language_linkage"] = language
                self.assert_eligible(self.query(ast, rows, "linkage"))

    def test_linkage_requires_both_named_enums(self):
        for field in ("linkage_internal", "linkage_formal"):
            with self.subTest(field=field):
                ast, rows = fixture()
                del rows[-1][field]
                self.assert_refused(self.query(ast, rows, "linkage"))
                ast, rows = fixture()
                rows[-1][field] = "unrepresented"
                self.assert_refused(self.query(ast, rows, "linkage"))

    def test_language_linkage_is_required_only_where_probe_queries_it(self):
        ast, rows = fixture()
        del rows[-1]["language_linkage"]
        self.assert_refused(self.query(ast, rows, "linkage"))
        ast, rows = fixture("EnumDecl")
        self.assert_eligible(self.query(ast, rows, "linkage"))

    def test_null_is_not_language_linkage_none_enum(self):
        ast, rows = fixture()
        rows[-1]["language_linkage"] = None
        self.assert_refused(self.query(ast, rows, "linkage"))

    def test_translation_unit_has_no_named_linkage_candidate(self):
        ast, rows = fixture()
        self.assert_refused(self.query(ast, rows, "linkage", identifier="0x1"))


class DeclarationPricingDiagnosticsTests(unittest.TestCase):
    query = DeclarationPricingTests.query
    assert_eligible = DeclarationPricingTests.assert_eligible
    assert_refused = DeclarationPricingTests.assert_refused

    def test_unknown_query_refuses_instead_of_defaulting_to_linkage(self):
        ast, rows = fixture()
        with self.assertRaisesRegex(ValueError, "unknown pricing query"):
            self.query(ast, rows, "name-equivalence")

    def test_probe_rejects_wrong_schema_header_and_metadata_shape(self):
        ast, rows = fixture()
        for metadata in (None, [], True, "metadata"):
            with self.subTest(metadata=metadata):
                with self.assertRaises(ValueError):
                    pricing.price_probe({"ast": ast, "metadata": metadata})
        for field, value in (("schema_version", "other-schema"),
                             ("compiled_frontend", "21.1.9"),
                             ("runtime_frontend", "clang version 21.1.80")):
            with self.subTest(field=field):
                document = probe_document(ast, rows)
                document["metadata"][field] = value
                with self.assertRaises(ValueError):
                    pricing.price_probe(document)

    def test_malformed_metadata_rows_are_explicit_errors(self):
        ast, rows = fixture()
        for row in (None, [], "row", {"id": True}, {"id": "not-a-handle"}):
            with self.subTest(row=row):
                with self.assertRaisesRegex(ValueError, "malformed declaration metadata row"):
                    pricing.build_index(ast, rows + [row])

    def test_census_counts_and_wall_sets_account_for_every_source(self):
        ast, rows = fixture()
        ast["inner"].append(raw_declaration("0x90", "ParmVarDecl"))
        rows.append(metadata_row("0x91", "ParmVarDecl"))
        report = pricing.price_probe(probe_document(ast, rows))
        index = pricing.build_index(ast, rows)
        self.assertEqual(report["source_ids"], 5)
        self.assertEqual(report["scope"], "tooling-pricing-only")
        self.assertEqual(report["semantic_admitted_queries"], 0)
        for query, summary in report["queries"].items():
            with self.subTest(query=query):
                self.assertEqual(sum(summary["counts"].values()), 5)
                self.assertEqual(sum(sum(counts.values()) for counts
                                     in summary["families"].values()), 5)
                self.assertEqual(sum(group["count"] for group in summary["wall_sets"]), 5)
                expected = collections.Counter()
                for identifier in ("0x1", "0x2", "0x3", "0x90", "0x91"):
                    expected.update(pricing.price_query(index, identifier, query)["reasons"])
                self.assertEqual(summary["all_wall_counts"], dict(expected))

    def test_census_sample_limit_caps_examples_without_changing_counts(self):
        ast, rows = fixture()
        document = probe_document(ast, rows)
        zero = pricing.price_probe(document, sample_limit=0)
        one = pricing.price_probe(document, sample_limit=1)
        for query in QUERIES:
            self.assertEqual(zero["queries"][query]["counts"], one["queries"][query]["counts"])
            self.assertFalse(any(zero["queries"][query]["examples"].values()))
            self.assertTrue(all(len(examples) <= 1 for examples
                                in one["queries"][query]["examples"].values()))

    def test_all_nested_noninner_template_ancestor_is_observed(self):
        ast, rows = fixture()
        ast["association"] = {"kind": "FunctionTemplateDecl", "referencedDecl": {
            "id": "0x3", "kind": "FunctionDecl",
        }}
        self.assert_refused(self.query(ast, rows))

    def test_canonical_relation_across_distinct_namespace_contexts_refuses(self):
        ast, rows = fixture()
        alternate = raw_declaration("0x4", "FunctionDecl")
        namespace = raw_declaration("0x5", "NamespaceDecl", "other", [alternate])
        ast["inner"].append(namespace)
        rows[2].update(canonical="0x4", previous="0x4")
        rows.extend([metadata_row("0x4", "FunctionDecl", "0x5"),
                     metadata_row("0x5", "NamespaceDecl")])
        result = self.query(ast, rows)
        self.assert_refused(result)
        self.assertIn("canonical-context-mismatch", result["reasons"])

    def test_declaration_local_definition_ignores_unconsumed_canonical_metadata(self):
        ast, rows = fixture()
        del rows[-1]["canonical"]
        del rows[-1]["previous"]
        self.assert_eligible(self.query(ast, rows, "definition"))
        self.assert_refused(self.query(ast, rows))
        result = self.query(ast, rows, "definition")
        self.assertNotIn("canonical", result["evidence"]["0x3"]["fields"])

    def test_evidence_retains_every_nested_raw_occurrence_path(self):
        ast, rows = fixture()
        ast["association"] = {"referencedDecl": {"id": "0x3", "kind": "FunctionDecl"}}
        result = self.query(ast, rows)
        self.assert_eligible(result)
        paths = {occurrence["path"] for occurrence
                 in result["evidence"]["0x3"]["raw_occurrences"]}
        self.assertEqual(paths, {"/inner/0/inner/0", "/association/referencedDecl"})

    def test_malformed_location_range_and_inner_are_not_rich_witnesses(self):
        for field, value in (("loc", None), ("range", []), ("inner", "not-a-list")):
            with self.subTest(field=field):
                ast, rows = fixture()
                node = source_node(ast)
                del node["loc"]
                node[field] = value
                self.assert_refused(self.query(ast, rows))

    def test_different_canonical_names_refuse(self):
        ast, rows = fixture()
        ast["inner"][0]["inner"].append(raw_declaration("0x4", "FunctionDecl", "other"))
        root = metadata_row("0x4", "FunctionDecl", "0x2")
        root["name"] = "other"
        rows[-1].update(canonical="0x4", previous="0x4")
        rows.append(root)
        self.assert_refused(self.query(ast, rows))

    def test_same_name_distinct_canonical_roots_are_not_merged(self):
        ast, rows = fixture()
        ast["inner"][0]["inner"].append(raw_declaration("0x4", "FunctionDecl"))
        rows.append(metadata_row("0x4", "FunctionDecl", "0x2"))
        first = self.query(ast, rows)
        second = self.query(ast, rows, identifier="0x4")
        self.assert_eligible(first)
        self.assert_eligible(second)
        self.assertEqual(first["observed"]["canonical"], "0x3")
        self.assertEqual(second["observed"]["canonical"], "0x4")

    def test_nested_translation_unit_impostor_is_not_the_root(self):
        ast, rows = fixture()
        ast["inner"].append(raw_declaration("0x4", "TranslationUnitDecl"))
        rows.append(metadata_row("0x4", "TranslationUnitDecl"))
        rows[2]["semantic_context"] = "0x4"
        self.assert_refused(self.query(ast, rows, "contexts"))

    def test_namespace_reopening_with_matching_parent_chain_is_allowed(self):
        ast, rows = fixture()
        ast["inner"].append(raw_declaration("0x4", "NamespaceDecl"))
        rows[1].update(canonical="0x4", original_namespace="0x4", previous="0x4")
        rows.append(metadata_row("0x4", "NamespaceDecl"))
        self.assert_eligible(self.query(ast, rows, "contexts"))

    def test_namespace_context_canonical_parent_disagreement_refuses(self):
        ast, rows = fixture()
        root = raw_declaration("0x4", "NamespaceDecl")
        ast["inner"].append(raw_declaration("0x5", "NamespaceDecl", children=[root]))
        rows[1].update(canonical="0x4", original_namespace="0x4", previous="0x4")
        rows.extend([metadata_row("0x4", "NamespaceDecl", "0x5"),
                     metadata_row("0x5", "NamespaceDecl")])
        self.assert_refused(self.query(ast, rows, "contexts"))

    def test_namespace_inline_and_anonymous_canonical_disagreement_refuses(self):
        for field in ("inline_namespace", "anonymous_namespace"):
            with self.subTest(field=field):
                ast, rows = fixture()
                ast["inner"].append(raw_declaration("0x4", "NamespaceDecl"))
                rows[1].update(canonical="0x4", original_namespace="0x4", previous="0x4")
                root = metadata_row("0x4", "NamespaceDecl")
                root[field] = True
                rows.append(root)
                self.assert_refused(self.query(ast, rows, "contexts"))

    def test_canonical_parent_occurrence_semantic_cycle_refuses(self):
        ast, rows = canonical_parent_occurrence_fixture()
        rows[-1]["semantic_context"] = "0x7"
        self.assert_refused(self.query(ast, rows, "contexts"))

    def test_canonical_parent_occurrence_missing_semantic_context_refuses(self):
        ast, rows = canonical_parent_occurrence_fixture()
        del rows[-1]["semantic_context"]
        self.assert_refused(self.query(ast, rows, "contexts"))


class OwnTemplatePricingTests(unittest.TestCase):
    query = DeclarationPricingTests.query
    assert_eligible = DeclarationPricingTests.assert_eligible
    assert_refused = DeclarationPricingTests.assert_refused

    def template_fields(self, kind):
        fields = ("template_specialization_kind", "template_specialization_kind_api")
        if kind == "FunctionDecl":
            return fields + ("function_templated_kind", "function_templated_kind_api")
        if kind in ("VarDecl", "CXXRecordDecl"):
            return fields + ("described_template", "described_template_api")
        return fields

    def test_missing_own_template_evidence_refuses_every_query(self):
        for kind in ("FunctionDecl", "VarDecl", "CXXRecordDecl", "EnumDecl"):
            for field in self.template_fields(kind):
                for query in QUERIES:
                    with self.subTest(kind=kind, field=field, query=query):
                        ast, rows = fixture(kind)
                        del rows[-1][field]
                        self.assert_refused(self.query(ast, rows, query))

    def test_api_provenance_must_match_exact_declaration_family(self):
        for kind in ("FunctionDecl", "VarDecl", "CXXRecordDecl", "EnumDecl"):
            for field in self.template_fields(kind):
                if not field.endswith("_api"):
                    continue
                for value in (None, False, 0, "wrong-api", "clang." + rows_api(kind, field)):
                    with self.subTest(kind=kind, field=field, value=value):
                        ast, rows = fixture(kind)
                        rows[-1][field] = value
                        self.assert_refused(self.query(ast, rows))

    def test_function_templated_kind_never_coerces_bool_or_unknown_enum(self):
        for value in (None, True, False, 0.0, "0", -1, 6):
            with self.subTest(value=value):
                ast, rows = fixture()
                rows[-1]["function_templated_kind"] = value
                self.assert_refused(self.query(ast, rows))

    def test_each_function_template_category_is_refused(self):
        for value in range(1, 6):
            with self.subTest(value=value):
                ast, rows = fixture()
                rows[-1]["function_templated_kind"] = value
                result = self.query(ast, rows)
                self.assert_refused(result)
                self.assertIn("templated-or-unestablished", result["reasons"])

    def test_specialization_enums_have_strict_integer_domains(self):
        for kind in ("FunctionDecl", "VarDecl", "CXXRecordDecl", "EnumDecl"):
            for value in (None, True, False, 0.0, "0", -1, 5):
                with self.subTest(kind=kind, value=value):
                    ast, rows = fixture(kind)
                    rows[-1]["template_specialization_kind"] = value
                    self.assert_refused(self.query(ast, rows))

    def test_each_specialization_category_is_refused_for_all_families(self):
        for kind in ("FunctionDecl", "VarDecl", "CXXRecordDecl", "EnumDecl"):
            for value in range(1, 5):
                with self.subTest(kind=kind, value=value):
                    ast, rows = fixture(kind)
                    rows[-1]["template_specialization_kind"] = value
                    result = self.query(ast, rows)
                    self.assert_refused(result)
                    self.assertIn("specialization-or-unestablished", result["reasons"])

    def test_described_template_must_be_explicit_null_for_ordinary_candidate(self):
        for kind in ("VarDecl", "CXXRecordDecl"):
            for value in (True, False, 0, "", "not-a-handle", "0x99"):
                with self.subTest(kind=kind, value=value):
                    ast, rows = fixture(kind)
                    rows[-1]["described_template"] = value
                    self.assert_refused(self.query(ast, rows))

    def test_primary_templates_refuse_even_without_dependent_parent_or_raw_wrapper(self):
        for kind in ("VarDecl", "CXXRecordDecl"):
            with self.subTest(kind=kind):
                ast, rows = fixture(kind)
                rows[-1]["described_template"] = "0x99"
                result = self.query(ast, rows)
                self.assert_refused(result)
                self.assertIn("described-template-or-unestablished", result["reasons"])
                self.assertNotIn("dependent-or-unestablished", result["reasons"])
                self.assertNotIn("template-associated-occurrence", result["reasons"])

    def test_conflicting_own_template_evidence_refuses_all_query_kinds(self):
        for kind in ("FunctionDecl", "VarDecl", "CXXRecordDecl", "EnumDecl"):
            for field in self.template_fields(kind):
                for query in QUERIES:
                    with self.subTest(kind=kind, field=field, query=query):
                        ast, rows = fixture(kind)
                        duplicate = copy.deepcopy(rows[-1])
                        duplicate[field] = "conflicting-api" if field.endswith("_api") else True
                        rows.append(duplicate)
                        self.assert_refused(self.query(ast, rows, query))

    def test_canonical_closure_requires_ordinary_own_template_evidence(self):
        ast, rows = fixture()
        predecessor = raw_declaration("0x4", "FunctionDecl")
        ast["inner"][0]["inner"].append(predecessor)
        rows[-1].update(canonical="0x4", previous="0x4")
        rows.append(metadata_row("0x4", "FunctionDecl", "0x2"))
        del rows[-1]["function_templated_kind"]
        self.assert_refused(self.query(ast, rows))

    def test_template_fields_are_not_consumed_for_namespace_and_translation_unit(self):
        ast, rows = fixture("NamespaceDecl")
        malformed = {"function_templated_kind": False,
                     "function_templated_kind_api": None,
                     "template_specialization_kind": True,
                     "template_specialization_kind_api": "bad-api",
                     "described_template": 17, "described_template_api": None}
        rows[0].update(malformed)
        rows[-1].update(malformed)
        self.assert_eligible(self.query(ast, rows))
        self.assert_eligible(self.query(ast, rows, identifier="0x1"))

    def test_obsolete_schema_is_not_silently_upgraded_with_fabricated_evidence(self):
        ast, rows = fixture()
        document = probe_document(ast, rows)
        document["metadata"]["schema_version"] = "cpp-canonical-probe-0.1"
        with self.assertRaisesRegex(ValueError, "unsupported canonical probe schema"):
            pricing.price_probe(document)

    def test_versioned_census_retains_zero_semantic_admissions(self):
        ast, rows = fixture()
        report = pricing.price_probe(probe_document(ast, rows))
        self.assertEqual(report["format"], "cpp-declaration-pricing-2")
        self.assertEqual(report["probe_schema"], "cpp-canonical-probe-0.2")
        self.assertEqual(report["semantic_admitted_queries"], 0)
        for query in QUERIES:
            result = self.query(ast, rows, query)
            self.assert_eligible(result)
            self.assertIn("semantic-validator-not-implemented", result["semantic_barriers"])
            self.assertIn("language-linkage-entity-rules-unestablished", result["semantic_barriers"])
            self.assertNotIn("non-template-evidence-unestablished", result["semantic_barriers"])


def rows_api(kind, field):
    return metadata_row("0x3", kind)[field]


class DeclarationPricingCliTests(unittest.TestCase):
    def run_cli(self, source, output, *extra):
        return subprocess.run([sys.executable, str(HERE / "price_declarations.py"),
                               str(source), "--out", str(output), *extra],
                              capture_output=True, text=True, timeout=20)

    def test_cli_input_bound_precedes_parsing_and_preserves_report(self):
        with tempfile.TemporaryDirectory() as directory:
            source = pathlib.Path(directory) / "large.json"
            output = pathlib.Path(directory) / "report.json"
            source.write_bytes(b" " * (1024 * 1024 + 1))
            output.write_text("existing report", encoding="utf-8")
            result = self.run_cli(source, output, "--max-input-mib", "1")
            self.assertEqual(result.returncode, 2)
            self.assertIn("input exceeds explicit byte bound", result.stderr)
            self.assertEqual(output.read_text(encoding="utf-8"), "existing report")

    def test_cli_refuses_direct_hardlink_and_symlink_output_aliases(self):
        ast, rows = fixture()
        with tempfile.TemporaryDirectory() as directory:
            source = pathlib.Path(directory) / "probe.json"
            source.write_text(json.dumps(probe_document(ast, rows)), encoding="utf-8")
            hardlink = pathlib.Path(directory) / "hardlink.json"
            symlink = pathlib.Path(directory) / "symlink.json"
            os.link(source, hardlink)
            symlink.symlink_to(source)
            original = source.read_bytes()
            for output in (source, hardlink, symlink):
                with self.subTest(output=output.name):
                    result = self.run_cli(source, output)
                    self.assertEqual(result.returncode, 2)
                    self.assertIn("output aliases input", result.stderr)
                    self.assertEqual(source.read_bytes(), original)

    def test_cli_malformed_metadata_and_duplicate_json_have_no_traceback(self):
        payloads = ('{"metadata": []}', '{"metadata": {}, "metadata": {}}')
        with tempfile.TemporaryDirectory() as directory:
            source = pathlib.Path(directory) / "malformed.json"
            output = pathlib.Path(directory) / "report.json"
            for payload in payloads:
                with self.subTest(payload=payload):
                    source.write_text(payload, encoding="utf-8")
                    result = self.run_cli(source, output)
                    self.assertEqual(result.returncode, 2)
                    self.assertIn("declaration pricing refused:", result.stderr)
                    self.assertNotIn("Traceback", result.stderr)
                    self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
