#!/usr/bin/env python3
"""Price the C survey's static type-layout candidate wall.

The survey's ``type-layout`` wall is intentionally conservative: it is found
from types in the clang envelope, while the runner's refusal says which wall
was actually reached.  This report keeps those measurements separate so a
layout tier is sized from observed refusals rather than from spellings alone.
"""
import argparse
import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_INPUT = ROOT / "docs" / "c-survey.json"
DEFAULT_JSON = ROOT / "docs" / "c-type-layout-price.json"
DEFAULT_PAGE = ROOT / "docs" / "c-type-layout-price.md"


def is_decl_layout(row):
    return (row.get("verdict") == "refused-unsupported" and
            "no layout for declared type" in row.get("detail", ""))


def is_any_layout(row):
    return (row.get("verdict") == "refused-unsupported" and
            "no layout" in row.get("detail", ""))


def envelope_dependencies(data, manifest_path):
    if not manifest_path:
        return {}
    manifest = json.loads(Path(manifest_path).read_text())
    by_name = {item["name"]: item for item in manifest.get("tests", [])}
    out = {}
    for row in data.get("rows", []):
        if "no layout for declared type 'struct S'" not in row.get("detail", ""):
            continue
        item = by_name.get(row.get("name"), {})
        env_path = item.get("envelope")
        if not env_path or not Path(env_path).is_file():
            continue
        env = json.loads(Path(env_path).read_text())
        records = []
        def walk(value):
            if isinstance(value, dict):
                if value.get("kind") == "RecordDecl" and value.get("name") == "S":
                    records.append(value)
                for child in value.values():
                    walk(child)
            elif isinstance(value, list):
                for child in value:
                    walk(child)
        walk(env)
        fields = []
        for record in records:
            for field in record.get("fields", []):
                typ = field.get("type")
                if isinstance(typ, str):
                    typ = re.sub(r"[^ ]*/src/", "src/", typ)
                fields.append({"name": field.get("name"), "type": typ,
                               "kind": field.get("kind"), "c_kind": field.get("c_kind")})
        out.setdefault(row["name"], fields)
    return out


def envelope_identity_joins(data, manifest_path):
    if not manifest_path:
        return {}
    manifest = json.loads(Path(manifest_path).read_text())
    by_name = {item["name"]: item for item in manifest.get("tests", [])}
    out = {}
    for row in data.get("rows", []):
        if "no layout for declared type 'struct S'" not in row.get("detail", ""):
            continue
        item = by_name.get(row.get("name"), {})
        env_path = item.get("envelope")
        if not env_path or not Path(env_path).is_file():
            continue
        env = json.loads(Path(env_path).read_text())
        records, refs = [], []
        def walk(value):
            if isinstance(value, dict):
                if value.get("kind") == "RecordDecl" and value.get("name") == "S":
                    records.append({"decl_id": value.get("decl_id"),
                                    "field_count": len(value.get("fields", []))})
                if value.get("kind") == "VarDecl" and value.get("record_decl_id"):
                    refs.append({"name": value.get("name"),
                                 "record_decl_id": value.get("record_decl_id"),
                                 "type": value.get("type")})
                for child in value.values():
                    walk(child)
            elif isinstance(value, list):
                for child in value:
                    walk(child)
        walk(env)
        out[row["name"]] = {"records": records, "variable_refs": refs}
    return out


def price(data, manifest_path=None):
    rows = data.get("rows", [])
    corpora = sorted({row.get("corpus", "") for row in rows})
    by_corpus = {}
    all_decl_messages = Counter()
    for corpus in corpora:
        rs = [row for row in rows if row.get("corpus", "") == corpus]
        static = [row for row in rs if "type-layout" in row.get("static_walls", [])]
        decl = [row for row in rs if is_decl_layout(row)]
        any_layout = [row for row in rs if is_any_layout(row)]
        both = [row for row in decl if "type-layout" in row.get("static_walls", [])]
        messages = Counter(row.get("detail", "") for row in decl)
        all_decl_messages.update(messages)
        by_corpus[corpus] = {
            "files": len(rs),
            "static_present": len(static),
            "static_sole": sum(len(row.get("static_walls", [])) == 1
                                for row in static),
            "observed_decl_no_layout": len(decl),
            "observed_any_no_layout": len(any_layout),
            "static_and_observed_decl": len(both),
            "observed_decl_without_static_candidate": len(decl) - len(both),
            "static_candidate_without_observed_decl": len(static) - len(both),
            "decl_messages": [
                {"detail": detail, "files": count}
                for detail, count in messages.most_common()
            ],
        }
    report = {
        "schema": "c-type-layout-price-0.1",
        "survey_schema": data.get("schema"),
        "survey_commit": data.get("measured_commit"),
        "survey_measured_at_utc": data.get("measured_at_utc"),
        "corpus": data.get("corpus"),
        "by_corpus": by_corpus,
        "totals": {
            "static_present": sum(x["static_present"] for x in by_corpus.values()),
            "static_sole": sum(x["static_sole"] for x in by_corpus.values()),
            "observed_decl_no_layout": sum(x["observed_decl_no_layout"]
                                            for x in by_corpus.values()),
            "observed_any_no_layout": sum(x["observed_any_no_layout"]
                                           for x in by_corpus.values()),
            "static_and_observed_decl": sum(x["static_and_observed_decl"]
                                             for x in by_corpus.values()),
            "observed_decl_without_static_candidate": sum(
                x["observed_decl_without_static_candidate"] for x in by_corpus.values()),
            "static_candidate_without_observed_decl": sum(
                x["static_candidate_without_observed_decl"] for x in by_corpus.values()),
        },
        "top_decl_messages": [
            {"detail": detail, "files": count}
            for detail, count in all_decl_messages.most_common()
        ],
        "interpretation": (
            "type-layout is a candidate wall, not a dynamic verdict: the static "
            "heuristic over-approximates the files that reach a missing layout "
            "and misses some declaration types. Price a tier from observed "
            "no-layout refusals, retaining the static ranking for discovery."
        ),
    }
    dependencies = envelope_dependencies(data, manifest_path)
    report["struct_S_dependencies"] = {
        "files": len(dependencies),
        "rows": [{"name": name, "fields": fields}
                 for name, fields in sorted(dependencies.items())],
        "interpretation": (
            "field records come directly from the approved Clang envelope; an "
            "empty list means the envelope has no named S record, not that a "
            "layout was guessed."
        ),
    }
    joins = envelope_identity_joins(data, manifest_path)
    report["struct_S_identity_joins"] = {
        "files": len(joins),
        "rows": [{"name": name, **value} for name, value in sorted(joins.items())],
        "interpretation": (
            "RecordDecl.decl_id and VarDecl.record_decl_id are retained from "
            "Clang's envelope; an empty variable_refs list means this envelope "
            "has no variable carrying that direct declaration identity."
        ),
    }
    return report


def render(report):
    t = report["totals"]
    lines = [
        "# C type-layout wall price",
        "",
        "This report compares the envelope-derived candidate wall with the runner's first refusal.",
        "",
        "- survey commit: `%s`" % report.get("survey_commit", ""),
        "- survey measured at: `%s`" % report.get("survey_measured_at_utc", ""),
        "- static candidates: %d present, %d sole" %
        (t["static_present"], t["static_sole"]),
        "- observed declaration `no layout`: %d (candidate overlap %d)" %
        (t["observed_decl_no_layout"], t["static_and_observed_decl"]),
        "- observed declaration refusals without a static candidate: %d" %
        t["observed_decl_without_static_candidate"],
        "- static candidates without an observed declaration refusal: %d" %
        t["static_candidate_without_observed_decl"],
        "",
        "| corpus | static present | static sole | observed declaration no-layout | overlap |",
        "| --- | ---: | ---: | ---: | ---: |",
    ]
    for corpus, item in report["by_corpus"].items():
        lines.append("| `%s` | %d | %d | %d | %d |" % (
            corpus, item["static_present"], item["static_sole"],
            item["observed_decl_no_layout"], item["static_and_observed_decl"]))
    lines += ["", "## Most frequent observed declaration refusals", "",
              "| detail | files |", "| --- | ---: |"]
    for item in report["top_decl_messages"][:20]:
        lines.append("| `%s` | %d |" % (item["detail"], item["files"]))
    deps = report.get("struct_S_dependencies", {})
    if deps.get("rows"):
        lines += ["", "## `struct S` parser-envelope dependencies", "",
                  "| file | fields from Clang envelope |", "| --- | --- |"]
        for item in deps["rows"]:
            fields = ", ".join(
                "%s:%s" % (field.get("name") or "<anonymous>", field.get("type") or field.get("c_kind") or "?")
                for field in item["fields"])
            lines.append("| `%s` | %s |" % (item["name"], fields or "<none>"))
        lines += ["", deps.get("interpretation", ""), ""]
    joins = report.get("struct_S_identity_joins", {})
    if joins.get("rows"):
        lines += ["", "## `struct S` declaration-identity joins", "",
                  "| file | RecordDecl ids | VarDecl identity refs |", "| --- | --- | --- |"]
        for item in joins["rows"]:
            records = ", ".join(str(x.get("decl_id") or "<missing>") for x in item["records"])
            refs = ", ".join(
                "%s→%s" % (x.get("name") or "<unnamed>", x.get("record_decl_id"))
                for x in item["variable_refs"])
            lines.append("| `%s` | %s | %s |" % (item["name"], records or "<none>", refs or "<none>"))
        lines += ["", joins.get("interpretation", ""), ""]
    lines += ["", report["interpretation"], ""]
    return "\n".join(lines)


def self_test():
    data = {"schema": "c-survey-0.1", "rows": [
        {"corpus": "c1", "verdict": "refused-unsupported",
         "detail": "no layout for declared type 'double'",
         "static_walls": ["type-layout"]},
        {"corpus": "c1", "verdict": "passed", "detail": "",
         "static_walls": ["type-layout"]},
        {"corpus": "c1", "verdict": "refused-unsupported",
         "detail": "no layout for declared type 'enum E'", "static_walls": []},
    ]}
    got = price(data)["totals"]
    want = {"static_present": 2, "static_sole": 2,
            "observed_decl_no_layout": 2, "observed_any_no_layout": 2,
            "static_and_observed_decl": 1,
            "observed_decl_without_static_candidate": 1,
            "static_candidate_without_observed_decl": 1}
    if got != want:
        raise SystemExit("c_type_layout_price --self-test: got %r want %r" % (got, want))
    if envelope_identity_joins({"rows": []}, None) != {}:
        raise SystemExit("c_type_layout_price --self-test: empty identity join changed")
    print("c_type_layout_price --self-test: ok")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", default=str(DEFAULT_INPUT))
    ap.add_argument("--json", default=str(DEFAULT_JSON))
    ap.add_argument("--page", default=str(DEFAULT_PAGE))
    ap.add_argument("--manifest", default=None,
                    help="external manifest used to inspect parser envelopes")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        self_test()
        return 0
    report = price(json.loads(Path(args.input).read_text()), args.manifest)
    Path(args.json).write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    Path(args.page).write_text(render(report))
    print("c_type_layout_price: wrote %s and %s" % (args.json, args.page))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
