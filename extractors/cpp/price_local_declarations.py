#!/usr/bin/env python3
"""Price declaration-statement presence in archived body inventories, not admission."""

import argparse
import collections
import hashlib
import json
import pathlib
import re
import sys

from compare_ast import publish_report, refuse_numeric_token, refuse_output_alias, unique_object


INPUT_SCHEMA = "ls-cpp-r0-census-1"
FORMAT = "cpp-local-declaration-pricing-1"
OWNERSHIPS = ("target-source", "corpus-header-dependency", "external-dependency")
FUNCTION_KINDS = frozenset((
    "FunctionDecl", "CXXMethodDecl", "CXXConstructorDecl", "CXXDestructorDecl",
    "CXXConversionDecl",
))
CALLABLE_BODY_KINDS = frozenset((
    "BinaryOperator", "BreakStmt", "CXXBoolLiteralExpr", "CaseStmt",
    "CompoundAssignOperator", "CompoundStmt", "ConditionalOperator", "ConstantExpr",
    "ContinueStmt", "DeclRefExpr", "DefaultStmt", "DoStmt", "ExprWithCleanups",
    "ForStmt", "IfStmt", "ImplicitCastExpr", "IntegerLiteral", "NullStmt",
    "ParenExpr", "ReturnStmt", "SwitchStmt", "UnaryOperator", "WhileStmt",
))
LOCAL_DECLARATION_KINDS = frozenset((
    "DeclStmt", "VarDecl", "InitListExpr", "CXXScalarValueInitExpr",
))
CONTEXT_DEPENDENT_KINDS = frozenset(("<missing>",))


def inventory_rows(document):
    if not isinstance(document, dict) or document.get("schema") != INPUT_SCHEMA:
        raise ValueError("expected body inventory schema " + INPUT_SCHEMA)
    revision = document.get("revision")
    if not isinstance(revision, str) or re.fullmatch(r"[0-9a-f]{40}", revision) is None:
        raise ValueError("expected a pinned 40-digit hexadecimal inventory revision")
    if not isinstance(document.get("counting_rule"), str) or not document["counting_rule"]:
        raise ValueError("expected an explicit inventory counting rule")
    rows = document.get("functions")
    if not isinstance(rows, list):
        raise ValueError("expected a functions array")
    for ordinal, row in enumerate(rows):
        if not isinstance(row, dict):
            raise ValueError("expected a function object at ordinal " + str(ordinal))
        if not isinstance(row.get("kind"), str) or row["kind"] not in FUNCTION_KINDS:
            raise ValueError("unknown function kind at ordinal " + str(ordinal))
        if row.get("ownership") not in OWNERSHIPS:
            raise ValueError("unknown ownership at ordinal " + str(ordinal))
        if type(row.get("is_implicit")) is not bool:
            raise ValueError("expected an implicit boolean at ordinal " + str(ordinal))
        kinds = row.get("body_kinds")
        if not isinstance(kinds, dict):
            raise ValueError("expected body kind counts at ordinal " + str(ordinal))
        for kind, count in kinds.items():
            if not isinstance(kind, str) or not kind or type(count) is not int or count <= 0:
                raise ValueError("invalid body kind count at ordinal " + str(ordinal))
    return rows


def price_inventory(document, ownership="target-source"):
    if ownership not in OWNERSHIPS:
        raise ValueError("unknown selected ownership")
    rows = inventory_rows(document)
    selected = [row for row in rows if row["ownership"] == ownership]
    explicit = [row for row in selected if not row["is_implicit"]]
    ordinary = [row for row in explicit if row["kind"] == "FunctionDecl"]
    declarations = [row for row in ordinary if "DeclStmt" in row["body_kinds"]]
    other_presence = collections.Counter()
    other_sets = collections.Counter()
    candidates = 0
    context_dependent = 0
    for row in declarations:
        kinds = set(row["body_kinds"])
        other = kinds - CALLABLE_BODY_KINDS - LOCAL_DECLARATION_KINDS - CONTEXT_DEPENDENT_KINDS
        other_presence.update(other)
        other_sets[tuple(sorted(other))] += 1
        candidates += not other
        context_dependent += bool(kinds & CONTEXT_DEPENDENT_KINDS)
    return {
        "format": FORMAT,
        "scope": "raw-kind-pricing-only",
        "semantic_admission_claimed": False,
        "execution": "not-attempted",
        "input_schema": INPUT_SCHEMA,
        "input_revision": document["revision"],
        "ownership": ownership,
        "ownership_basis": "input receipt classification; not independently validated",
        "counting_basis": "body occurrences; no deduplication of source sites or instantiations",
        "body_occurrences": len(selected),
        "nonimplicit_body_occurrences": len(explicit),
        "nonimplicit_declstmt_bodies": sum("DeclStmt" in row["body_kinds"] for row in explicit),
        "nonimplicit_function_kinds": dict(sorted(collections.Counter(
            row["kind"] for row in explicit).items())),
        "ordinary_body_occurrences": len(ordinary),
        "ordinary_declstmt_bodies": len(declarations),
        "ordinary_declstmt_kind_only_candidates": candidates,
        "ordinary_declstmt_context_dependent_bodies": context_dependent,
        "remaining_kind_presence": dict(sorted(other_presence.items())),
        "remaining_kind_sets": [{"kinds": list(kinds), "bodies": count}
                                for kinds, count in sorted(other_sets.items())],
        "callable_body_kinds": sorted(CALLABLE_BODY_KINDS),
        "hypothesized_local_kinds": sorted(LOCAL_DECLARATION_KINDS),
        "context_dependent_kinds": sorted(CONTEXT_DEPENDENT_KINDS),
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=pathlib.Path)
    parser.add_argument("--out", required=True, type=pathlib.Path)
    parser.add_argument("--ownership", choices=OWNERSHIPS, default="target-source")
    parser.add_argument("--max-input-mib", default=64, type=int)
    arguments = parser.parse_args(argv)
    if arguments.max_input_mib <= 0:
        parser.error("input byte bound must be positive")
    try:
        refuse_output_alias(arguments.out, [arguments.input])
        if arguments.input.stat().st_size > arguments.max_input_mib * 1024 * 1024:
            raise ValueError("input exceeds explicit byte bound")
        contents = arguments.input.read_bytes()
        if len(contents) > arguments.max_input_mib * 1024 * 1024:
            raise ValueError("input exceeds explicit byte bound")
        document = json.loads(contents, object_pairs_hook=unique_object,
                              parse_constant=refuse_numeric_token)
        report = price_inventory(document, arguments.ownership)
        report.update(input_bytes=len(contents), input_sha256=hashlib.sha256(contents).hexdigest())
        publish_report(arguments.out, report)
    except (OSError, ValueError, TypeError, RecursionError) as error:
        print("local declaration pricing refused: " + str(error), file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
