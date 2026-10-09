#!/usr/bin/env python3
"""Price query-local Clang declaration evidence; admit no C++ semantics."""

import argparse
import collections
import json
import pathlib
import sys
import time

from compare_ast import (POINTER_PATTERN, child_path, nested_containers,
                         publish_report, refuse_numeric_token,
                         refuse_output_alias, unique_object)


FORMAT = "cpp-declaration-pricing-1"
SCHEMA = "cpp-canonical-probe-0.1"
FAMILIES = frozenset(("TranslationUnitDecl", "NamespaceDecl", "FunctionDecl",
                      "VarDecl", "EnumDecl", "CXXRecordDecl"))
CONTEXTS = frozenset(("TranslationUnitDecl", "NamespaceDecl"))
QUERIES = ("canonical-node", "contexts", "definition", "linkage")
LINKAGES = frozenset(("Invalid", "None", "Internal", "UniqueExternal",
                      "VisibleNone", "Module", "External"))


def is_handle(value):
    return isinstance(value, str) and POINTER_PATTERN.fullmatch(value) is not None


def raw_occurrence(path, value, templated):
    witness_types = {"loc": dict, "range": dict, "inner": list, "completeDefinition": bool}
    present = [field for field in witness_types if field in value]
    malformed = [field for field in present if type(value[field]) is not witness_types[field]]
    rich = value["kind"] == "TranslationUnitDecl" or bool(present) and not malformed
    return {"path": path, "kind": value["kind"], "rich": rich,
            "malformed_witness_fields": malformed, "template_ancestor": templated}


def build_index(ast, rows):
    if not isinstance(ast, dict) or ast.get("kind") != "TranslationUnitDecl":
        raise ValueError("expected TranslationUnitDecl AST")
    if not is_handle(ast.get("id")):
        raise ValueError("expected translation-unit handle")
    if not isinstance(rows, list):
        raise ValueError("expected declaration metadata array")
    raw = collections.defaultdict(list)
    pending = [("", ast, False)]
    while pending:
        path, value, templated = pending.pop()
        nested_template = templated
        if isinstance(value, dict):
            kind = value.get("kind", "")
            nested_template = templated or (isinstance(kind, str) and
                                            ("Template" in kind or "Specialization" in kind))
            identifier = value.get("id")
            if is_handle(identifier) and isinstance(kind, str) and kind.endswith("Decl"):
                raw[identifier].append(raw_occurrence(path, value, nested_template))
        pending.extend((child_path(path, segment), child, nested_template)
                       for segment, child in nested_containers(value))
    metadata = collections.defaultdict(list)
    for ordinal, row in enumerate(rows):
        if not isinstance(row, dict) or not is_handle(row.get("id")):
            raise ValueError("malformed declaration metadata row: " + str(ordinal))
        metadata[row["id"]].append((ordinal, row))
    return {"raw": dict(raw), "metadata": dict(metadata), "translation_unit": ast["id"]}


class Evidence:
    def __init__(self, index):
        self.index = index
        self.reasons = set()
        self.used = {}

    def field(self, identifier, field, predicate):
        rows = self.index["metadata"].get(identifier, [])
        if not rows:
            self.reasons.add("missing-metadata-witness")
            return None
        values = [row[field] for _, row in rows if field in row]
        if len(values) != len(rows):
            self.reasons.add("missing-field:" + field)
            return None
        if any(type(value) is not type(values[0]) or value != values[0] for value in values):
            self.reasons.add("conflicting-field:" + field)
            return None
        if not predicate(values[0]):
            self.reasons.add("invalid-field:" + field)
            return None
        self.used.setdefault(identifier, {"raw_occurrences": self.index["raw"].get(identifier, []),
                                          "metadata_rows": [ordinal for ordinal, _ in rows],
                                          "fields": {}})["fields"][field] = values[0]
        return values[0]

    def source(self, identifier):
        occurrences = self.index["raw"].get(identifier, [])
        if not occurrences:
            self.reasons.add("missing-raw-witness")
        elif not any(occurrence["rich"] for occurrence in occurrences):
            self.reasons.add("skeletal-only-witness")
        for occurrence in occurrences:
            self.reasons.update("malformed-witness-field:" + field
                                for field in occurrence["malformed_witness_fields"])
        kind = self.field(identifier, "kind", lambda value: isinstance(value, str))
        if any(occurrence["kind"] != kind for occurrence in occurrences):
            self.reasons.add("raw-metadata-kind-conflict")
        if kind not in FAMILIES:
            self.reasons.add("unsupported-family:" + str(kind))
        if any(occurrence["template_ancestor"] for occurrence in occurrences):
            self.reasons.add("template-associated-occurrence")
        self.ordinary(identifier, kind)
        return kind

    def ordinary(self, identifier, kind):
        if self.field(identifier, "implicit", lambda value: type(value) is bool) is not False:
            self.reasons.add("implicit-or-unestablished")
        if self.field(identifier, "dependent_context", lambda value: type(value) is bool) is not False:
            self.reasons.add("dependent-or-unestablished")
        self.field(identifier, "owning_module", lambda value: value is None)
        if kind in FAMILIES - {"TranslationUnitDecl"}:
            self.field(identifier, "name", lambda value: isinstance(value, str))
        if kind == "TranslationUnitDecl" and identifier != self.index["translation_unit"]:
            self.reasons.add("not-artifact-translation-unit")
        if kind == "NamespaceDecl":
            for field in ("inline_namespace", "anonymous_namespace"):
                self.field(identifier, field, lambda value: type(value) is bool)
        if kind == "FunctionDecl":
            specialization = self.field(identifier, "template_specialization_kind",
                                        lambda value: type(value) is int)
            if specialization != 0:
                self.reasons.add("specialization-or-unestablished")
        if kind == "CXXRecordDecl":
            if self.field(identifier, "injected_class_name", lambda value: type(value) is bool) is not False:
                self.reasons.add("injected-name-or-unestablished")
            self.field(identifier, "represented_class", lambda value: value is None)


def canonical_root(evidence, identifier, expected_kind=None):
    kind = evidence.source(identifier)
    if expected_kind is not None and kind != expected_kind:
        evidence.reasons.add("canonical-family-mismatch")
    root = evidence.field(identifier, "canonical", is_handle)
    if root is None:
        return None
    if root != identifier:
        if evidence.source(root) != kind:
            evidence.reasons.add("canonical-family-mismatch")
        if kind in FAMILIES - {"TranslationUnitDecl"}:
            source_name = evidence.field(identifier, "name", lambda value: isinstance(value, str))
            root_name = evidence.field(root, "name", lambda value: isinstance(value, str))
            if source_name != root_name:
                evidence.reasons.add("canonical-name-mismatch")
    if evidence.field(root, "canonical", is_handle) != root:
        evidence.reasons.add("non-idempotent-canonical-root")
    if kind == "NamespaceDecl":
        for target in set((identifier, root)):
            if evidence.field(target, "original_namespace", is_handle) != root:
                evidence.reasons.add("namespace-original-canonical-conflict")
        for field in ("inline_namespace", "anonymous_namespace"):
            source_flag = evidence.field(identifier, field, lambda value: type(value) is bool)
            root_flag = evidence.field(root, field, lambda value: type(value) is bool)
            if source_flag != root_flag:
                evidence.reasons.add("namespace-canonical-flag-conflict:" + field)
    return root


def normalized_parent(evidence, identifier):
    parent = evidence.field(identifier, "semantic_context", is_handle)
    if parent is None:
        return None
    kind = evidence.source(parent)
    if kind not in CONTEXTS:
        evidence.reasons.add("unsupported-context:" + str(kind))
        return None
    return canonical_root(evidence, parent, kind)


def validate_parent_cycles(evidence, parents):
    finished = set()
    for identifier in parents:
        active = set()
        current = identifier
        while current is not None and current not in finished:
            if current in active:
                evidence.reasons.add("namespace-semantic-parent-cycle")
                break
            active.add(current)
            current = parents.get(current)
        finished.update(active)


def namespace_closure(evidence, identifier):
    pending = [identifier]
    parents = {}
    roots = {}
    while pending:
        current = pending.pop()
        if current in parents:
            continue
        kind = evidence.source(current)
        if kind not in CONTEXTS:
            evidence.reasons.add("unsupported-context:" + str(kind))
            parents[current] = None
            continue
        root = canonical_root(evidence, current, kind)
        roots[current] = root
        parent = evidence.field(current, "semantic_context", lambda value: value is None or is_handle(value))
        if kind == "TranslationUnitDecl":
            if parent is not None:
                evidence.reasons.add("translation-unit-context-not-null:semantic_context")
            parents[current] = None
        else:
            parents[current] = parent
            if parent is None:
                evidence.reasons.add("missing-nonroot-context:semantic_context")
            else:
                pending.append(parent)
        if root is not None and root != current:
            pending.append(root)
    for current, root in roots.items():
        if root is not None and root != current:
            if normalized_parent(evidence, current) != normalized_parent(evidence, root):
                evidence.reasons.add("namespace-canonical-parent-mismatch")
    validate_parent_cycles(evidence, parents)


def context_chain(evidence, identifier, field):
    chain = []
    visited = set()
    current = identifier
    while current is not None:
        if current in visited:
            evidence.reasons.add("context-cycle:" + field)
            break
        visited.add(current)
        kind = evidence.source(current)
        context = evidence.field(current, field, lambda value: value is None or is_handle(value))
        if kind == "TranslationUnitDecl":
            if context is not None:
                evidence.reasons.add("translation-unit-context-not-null:" + field)
            break
        if context is None:
            evidence.reasons.add("missing-nonroot-context:" + field)
            break
        context_kind = evidence.source(context)
        if context_kind not in CONTEXTS:
            evidence.reasons.add("unsupported-context:" + str(context_kind))
            break
        root = canonical_root(evidence, context, context_kind)
        chain.append(root)
        if context_kind == "NamespaceDecl":
            namespace_closure(evidence, context)
        current = context
    return chain


def price_contexts(evidence, identifier):
    return {field: context_chain(evidence, identifier, field)
            for field in ("semantic_context", "lexical_context")}


def price_canonical(evidence, identifier, kind):
    root = canonical_root(evidence, identifier)
    chain = []
    visited = set()
    current = identifier
    expected_context = context_chain(evidence, identifier, "semantic_context")
    if root is not None and context_chain(evidence, root, "semantic_context") != expected_context:
        evidence.reasons.add("canonical-context-mismatch")
    while current is not None:
        if current in visited:
            evidence.reasons.add("predecessor-cycle")
            break
        visited.add(current)
        chain.append(current)
        if canonical_root(evidence, current, kind) != root:
            evidence.reasons.add("predecessor-canonical-mismatch")
        if context_chain(evidence, current, "semantic_context") != expected_context:
            evidence.reasons.add("predecessor-context-mismatch")
        previous = evidence.field(current, "previous", lambda value: value is None or is_handle(value))
        if previous is None and current != root:
            evidence.reasons.add("nonroot-predecessor-null")
        current = previous
    if root is not None:
        if evidence.field(root, "previous", lambda value: value is None or is_handle(value)) is not None:
            evidence.reasons.add("canonical-root-has-predecessor")
    return {"canonical": root, "predecessor_chain": chain}


def price_definition(evidence, identifier, kind):
    if kind == "FunctionDecl":
        api = "FunctionDecl.isThisDeclarationADefinition"
        for field in ("body_present", "defaulted", "deleted_as_written"):
            evidence.field(identifier, field, lambda value: type(value) is bool)
    elif kind in ("EnumDecl", "CXXRecordDecl"):
        api = "TagDecl.isThisDeclarationADefinition"
    elif kind == "VarDecl":
        evidence.field(identifier, "definition_api",
                       lambda value: value == "VarDecl.isThisDeclarationADefinition")
        evidence.field(identifier, "variable_definition_kind", lambda value: type(value) is int)
        evidence.reasons.add("variable-definition-rule-unestablished")
        return {}
    else:
        evidence.reasons.add("definition-api-not-supported-for-family")
        return {}
    evidence.field(identifier, "definition_api", lambda value: value == api)
    return {"declaration_local_definition": evidence.field(
        identifier, "definition", lambda value: type(value) is bool)}


def price_linkage(evidence, identifier, kind):
    if kind == "TranslationUnitDecl":
        evidence.reasons.add("unnamed-family-linkage")
        return {}
    result = {field: evidence.field(identifier, field, lambda value: value in LINKAGES
                                   if isinstance(value, str) else False)
              for field in ("linkage_internal", "linkage_formal")}
    if kind in ("FunctionDecl", "VarDecl"):
        result["language_linkage"] = evidence.field(
            identifier, "language_linkage", lambda value: isinstance(value, str)
            and value in ("C", "C++", "None"))
    return result


def price_query(index, identifier, query):
    if query not in QUERIES:
        raise ValueError("unknown pricing query: " + query)
    evidence = Evidence(index)
    kind = evidence.source(identifier)
    if query == "canonical-node":
        observed = price_canonical(evidence, identifier, kind)
    elif query == "contexts":
        observed = price_contexts(evidence, identifier)
    elif query == "definition":
        observed = price_definition(evidence, identifier, kind)
    else:
        observed = price_linkage(evidence, identifier, kind)
    barriers = ["semantic-validator-not-implemented"]
    if kind in ("FunctionDecl", "VarDecl", "CXXRecordDecl"):
        barriers.append("non-template-evidence-unestablished")
    if kind in ("FunctionDecl", "VarDecl"):
        barriers.append("language-linkage-entity-rules-unestablished")
    return {"status": "refused" if evidence.reasons else "eligible-tooling-evidence",
            "reasons": sorted(evidence.reasons), "evidence": evidence.used,
            "observed": observed, "semantic_barriers": barriers}


def price_probe(document, sample_limit=10):
    metadata = document.get("metadata", {}) if isinstance(document, dict) else {}
    if not isinstance(metadata, dict):
        raise ValueError("expected canonical probe metadata object")
    if metadata.get("schema_version") != SCHEMA:
        raise ValueError("unsupported canonical probe schema")
    if metadata.get("compiled_frontend") != "21.1.8":
        raise ValueError("unsupported compiled frontend")
    if metadata.get("llvm_headers") != "21.1.8":
        raise ValueError("unsupported LLVM headers")
    runtime = metadata.get("runtime_frontend")
    if not isinstance(runtime, str) or (runtime != "clang version 21.1.8" and
                                       not runtime.startswith("clang version 21.1.8 ")):
        raise ValueError("unsupported runtime frontend")
    if type(sample_limit) is not int or sample_limit < 0:
        raise ValueError("sample limit must be a nonnegative integer")
    index = build_index(document.get("ast"), metadata.get("declarations"))
    identifiers = sorted(set(index["raw"]) | set(index["metadata"]))
    queries = {}
    eligible_masks = collections.defaultdict(int)
    for query in QUERIES:
        statuses = collections.Counter()
        families = collections.defaultdict(collections.Counter)
        walls = collections.Counter()
        wall_sets = collections.Counter()
        barriers = collections.Counter()
        examples = collections.defaultdict(list)
        for identifier in identifiers:
            result = price_query(index, identifier, query)
            occurrences = index["raw"].get(identifier, [])
            kind = occurrences[0]["kind"] if occurrences else "metadata-only"
            status = result["status"]
            statuses[status] += 1
            families[kind][status] += 1
            walls.update(result["reasons"])
            wall_sets[tuple(result["reasons"])] += 1
            if status == "eligible-tooling-evidence":
                barriers.update(result["semantic_barriers"])
                eligible_masks[identifier] |= 1 << QUERIES.index(query)
            if sample_limit and len(examples[status]) < sample_limit:
                examples[status].append({"id": identifier, "kind": kind, **result})
        queries[query] = {"counts": dict(statuses), "families": dict(families),
                          "all_wall_counts": dict(walls),
                          "eligible_semantic_barrier_counts": dict(barriers),
                          "wall_sets": [{"reasons": list(reasons), "count": count}
                                        for reasons, count in sorted(wall_sets.items())],
                          "examples": dict(examples)}
    return {"format": FORMAT, "scope": "tooling-pricing-only",
            "semantic_admitted_queries": 0, "probe_schema": SCHEMA,
            "compiled_frontend": metadata.get("compiled_frontend"),
            "sample_limit": sample_limit, "source_ids": len(identifiers),
            "raw_ids": len(index["raw"]), "metadata_ids": len(index["metadata"]),
            "raw_declaration_positions": sum(map(len, index["raw"].values())),
            "metadata_rows": sum(map(len, index["metadata"].values())), "queries": queries,
            "eligible_query_sets": [{"queries": [query for ordinal, query in enumerate(QUERIES)
                                                   if mask & (1 << ordinal)], "count": count}
                                    for mask, count in sorted(collections.Counter(
                                        eligible_masks.get(identifier, 0)
                                        for identifier in identifiers).items())]}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=pathlib.Path)
    parser.add_argument("--out", required=True, type=pathlib.Path)
    parser.add_argument("--max-input-mib", default=64, type=int)
    parser.add_argument("--sample-limit", default=10, type=int)
    arguments = parser.parse_args(argv)
    if arguments.max_input_mib <= 0 or arguments.sample_limit < 0:
        parser.error("input bound must be positive and sample limit nonnegative")
    try:
        refuse_output_alias(arguments.out, [arguments.input])
        size = arguments.input.stat().st_size
        if size > arguments.max_input_mib * 1024 * 1024:
            raise ValueError("input exceeds explicit byte bound")
        started = time.monotonic()
        with arguments.input.open(encoding="utf-8") as source:
            document = json.load(source, parse_float=refuse_numeric_token,
                                 parse_constant=refuse_numeric_token, object_pairs_hook=unique_object)
        parsed = time.monotonic()
        report = price_probe(document, arguments.sample_limit)
        report.update(file=str(arguments.input.resolve()), file_bytes=size,
                      parse_seconds=parsed - started, price_seconds=time.monotonic() - parsed)
        publish_report(arguments.out, report)
    except (OSError, ValueError, TypeError, RecursionError) as error:
        print("declaration pricing refused: " + str(error), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
