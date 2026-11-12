#!/usr/bin/env python3
"""C23/C17 frontend census for the rejected frozen survey rows.

The census asks Clang itself two questions for every file whose pinned C23
run was rejected: what was the first C23 diagnostic, and does the same source
parse under the pinned C17 profile?  It never parses C source or diagnostic
locations.  Source paths are execution inputs only; the report keeps logical
names and pinned hashes so it is portable across external cache roots.
"""
import argparse
import hashlib
import json
import re
import subprocess
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SURVEY = ROOT / "docs" / "c-survey.json"
DEFAULT_JSON = ROOT / "docs" / "c-frontend-census.json"
DEFAULT_PAGE = ROOT / "docs" / "c-frontend-census.md"
PROFILE = ["-D_FORTIFY_SOURCE=0"]


def first_diagnostic(stderr):
    """Return a normalized first error/warning diagnostic, without paths."""
    lines = [line.strip() for line in stderr.splitlines() if line.strip()]
    line = next((x for x in lines if " error:" in x or x.startswith("error:")), None)
    if line is None:
        line = next((x for x in lines if " warning:" in x or x.startswith("warning:")), None)
    if line is None:
        return "clang rejected it without a diagnostic"
    if " error:" in line:
        msg = line.split(" error:", 1)[1].strip()
        return "error: " + msg
    if " warning:" in line:
        msg = line.split(" warning:", 1)[1].strip()
        return "warning: " + msg
    return re.sub(r"^.*?:\s*", "", line)


def diagnostic_class(detail):
    if detail.startswith("error: "):
        return detail[len("error: "):].split(":", 1)[0]
    if detail.startswith("warning: "):
        return "warning: " + detail[len("warning: "):].split(":", 1)[0]
    return detail


def run_clang(clang, mode, source):
    return subprocess.run(
        [clang, "-std=" + mode, *PROFILE, "-fsyntax-only", str(source)],
        capture_output=True, text=True,
    )


def source_for(item, roots):
    corpus = item.get("corpus")
    root = roots.get(corpus)
    if root is None:
        raise SystemExit("no source root for corpus %r" % corpus)
    path = root / item["name"]
    if not path.is_file():
        raise SystemExit("missing cached source for %s" % item["name"])
    return path


def census(survey, manifest, roots, clang):
    manifest_rows = {x["name"]: x for x in manifest.get("tests", [])}
    rejected = [x for x in survey.get("rows", []) if x.get("verdict") == "not-parsed"]
    rows = []
    for item in sorted(rejected, key=lambda x: (x.get("corpus", ""), x["name"])):
        rec = manifest_rows.get(item["name"], {})
        source = source_for({**item, **{"corpus": item.get("corpus")}}, roots)
        c23 = run_clang(clang, "c23", source)
        c17 = run_clang(clang, "c17", source)
        c23_rejected = c23.returncode != 0
        c23_detail = first_diagnostic(c23.stderr) if c23_rejected else ""
        c17_detail = "" if c17.returncode == 0 else first_diagnostic(c17.stderr)
        rows.append({
            "corpus": item.get("corpus", ""),
            "name": item["name"],
            "sha256": rec.get("sha256", item.get("sha256", "")),
            "c23": {"status": "rejected" if c23_rejected else "accepted_by_clang",
                    "diagnostic": c23_detail,
                    "class": diagnostic_class(c23_detail) if c23_rejected else "accepted_by_clang"},
            "c17": {"status": "accepted" if c17.returncode == 0 else "rejected",
                    "diagnostic": c17_detail,
                    "class": "accepted" if c17.returncode == 0 else diagnostic_class(c17_detail)},
        })
    c23_rejected = [x for x in rows if x["c23"]["status"] == "rejected"]
    accepted = [x for x in c23_rejected if x["c17"]["status"] == "accepted"]
    c23_classes = Counter(x["c23"]["class"] for x in c23_rejected)
    c17_classes = Counter(x["c17"]["class"] for x in rows if x["c17"]["status"] != "accepted")
    return {
        "schema": "c-frontend-census-0.1",
        "survey_schema": survey.get("schema"),
        "survey_commit": survey.get("measured_commit"),
        "survey_measured_at_utc": survey.get("measured_at_utc"),
        "frontend": {"name": "clang", "version": clang_version(clang),
                     "flags": PROFILE},
        "totals": {"survey_frontend_rows": len(rows),
                   "c23_rejected": len(c23_rejected),
                   "c23_accepted_by_clang": len(rows) - len(c23_rejected),
                   "c17_candidates": len(c23_rejected),
                   "c17_accepted": len(accepted),
                   "c17_rejected": len(c23_rejected) - len(accepted)},
        "c23_first_diagnostic_classes": [
            {"class": k, "files": v} for k, v in c23_classes.most_common()
        ],
        "c17_rejection_classes": [
            {"class": k, "files": v} for k, v in c17_classes.most_common()
        ],
        "c17_flip_set": [
            {"corpus": x["corpus"], "name": x["name"], "sha256": x["sha256"]}
            for x in accepted
        ],
        "rows": rows,
    }


def clang_version(clang):
    p = subprocess.run([clang, "--version"], capture_output=True, text=True)
    return (p.stdout.splitlines() or ["unknown"])[0]


def render(data):
    t = data["totals"]
    lines = [
        "# C frontend census: C23 rejects and C17 fallback",
        "",
        "This report reruns the pinned Clang on the 350 files rejected under C23.",
        "It uses Clang diagnostics and modes directly; it does not parse source text.",
        "",
        "- survey commit: `%s`" % data.get("survey_commit", ""),
        "- survey measured at: `%s`" % data.get("survey_measured_at_utc", ""),
        "- frontend: `%s`" % data["frontend"]["version"],
        "- profile flags: `%s`" % " ".join(data["frontend"]["flags"]),
        "- C23 rejected: **%d**" % t["c23_rejected"],
        "- C17 accepted: **%d**" % t["c17_accepted"],
        "- C17 still rejected: **%d**" % t["c17_rejected"],
        "",
        "## C23 first diagnostic classes",
        "",
        "| class | files |",
        "| --- | ---: |",
    ]
    lines += ["| `%s` | %d |" % (x["class"], x["files"])
              for x in data["c23_first_diagnostic_classes"]]
    lines += ["", "## C17 flip set", "",
              "These files parse under C17 with the same pinned profile and are the registered candidates for the next mode-aware extractor run.",
              "", "| corpus | file | sha256 |", "| --- | --- | --- |"]
    lines += ["| `%s` | `%s` | `%s` |" % (x["corpus"], x["name"], x["sha256"])
              for x in data["c17_flip_set"]]
    lines += ["", "## C17 remaining diagnostic classes", "",
              "| class | files |", "| --- | ---: |"]
    lines += ["| `%s` | %d |" % (x["class"], x["files"])
              for x in data["c17_rejection_classes"]]
    return "\n".join(lines) + "\n"


def self_test():
    assert first_diagnostic("/x/a.c:1:2: error: unknown type name 'x'\n") == "error: unknown type name 'x'"
    assert diagnostic_class("error: unknown type name 'x'") == "unknown type name 'x'"
    assert first_diagnostic("clang rejected it\n") == "clang rejected it without a diagnostic"
    print("c_frontend_census --self-test: ok")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--survey", default=str(DEFAULT_SURVEY))
    ap.add_argument("--manifest", required=False)
    ap.add_argument("--c1-root", required=False)
    ap.add_argument("--c2-root", required=False)
    ap.add_argument("--c3-root", required=False)
    ap.add_argument("--clang", default="clang")
    ap.add_argument("--json", default=str(DEFAULT_JSON))
    ap.add_argument("--page", default=str(DEFAULT_PAGE))
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        self_test(); return 0
    if not a.manifest or not all((a.c1_root, a.c2_root, a.c3_root)):
        ap.error("--manifest and all three --c*-root paths are required")
    survey = json.loads(Path(a.survey).read_text())
    manifest = json.loads(Path(a.manifest).read_text())
    roots = {
        "gcc.c-torture/execute": Path(a.c1_root),
        "c-testsuite/single-exec": Path(a.c2_root),
        "gcc.c23-run": Path(a.c3_root),
    }
    data = census(survey, manifest, roots, a.clang)
    page = render(data)
    if a.check:
        if json.loads(Path(a.json).read_text()) != data or Path(a.page).read_text() != page:
            print("c_frontend_census: artifacts are stale")
            return 1
        print("c_frontend_census: --check ok")
        return 0
    Path(a.json).write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
    Path(a.page).write_text(page)
    print("c_frontend_census: wrote %s and %s" % (a.json, a.page))
    print("c23 rejected=%d c17 accepted=%d c17 rejected=%d" % tuple(
        data["totals"][k] for k in ("c23_rejected", "c17_accepted", "c17_rejected")))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
