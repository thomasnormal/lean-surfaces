#!/usr/bin/env python3
"""Render the C torture survey from a runner log and its envelopes.

The survey consumes only the extractor's c-0.1 envelopes.  It never opens a
source file or reparses C text: the manifest supplies the pinned source hash,
the log supplies the dynamic verdict, and the envelope supplies the static
wall set.  ``--check`` is entirely offline and compares the committed JSON
with the page rendered from it.
"""

import argparse
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

from c_torture_score import parse


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_JSON = ROOT / "docs" / "c-survey.json"
DEFAULT_PAGE = ROOT / "docs" / "c-survey.md"


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def child_nodes(node):
    return [x for x in node.get("inner", []) if isinstance(x, dict)]


def callee_name(node):
    cur = node
    while isinstance(cur, dict) and cur.get("kind") in ("ImplicitCastExpr", "ParenExpr"):
        cur = cur.get("sub")
    return cur.get("name") if isinstance(cur, dict) else None


def portable_detail(detail):
    """Drop machine-specific cache prefixes from frontend diagnostics."""
    for marker in ("/src/", "/tests/single-exec/", "/gcc/testsuite/"):
        pos = detail.rfind(marker)
        if pos >= 0:
            return detail[pos + 1:]
    return detail


def dynamic_wall(verdict, detail):
    """Normalize the first runtime refusal into a rankable construct wall."""
    if verdict == "refused-unsupported":
        if detail.startswith("out of tier: "):
            return "unsupported:" + detail[len("out of tier: "):]
        if detail.startswith("castKind "):
            return "cast:" + detail.split("'", 2)[1]
        if detail.startswith("GNU case range"):
            return "unsupported:CaseStmt"
        if detail.startswith("unsequenced side effects"):
            return "unsequenced-effects"
        if detail.startswith("not an lvalue: "):
            return "unsupported:" + detail
        if detail.startswith("sizeof: no layout for operand type "):
            return "unsupported:" + detail
        if detail.startswith("not an integer type: "):
            return "unsupported:" + detail
        return "unsupported:" + detail.split(":", 1)[0]
    if verdict == "refused-libc":
        return "libc-call: " + detail if detail else "libc-call"
    if verdict == "refused-ub":
        return "undefined-behavior"
    if verdict == "timeout":
        return "timeout"
    if verdict == "not-ingested":
        return "ingestion"
    if verdict == "not-parsed":
        return "frontend"
    return None


def portable_manifest(value):
    """Copy a manifest while making cache paths logical rather than absolute."""
    if isinstance(value, dict):
        out = {}
        for key, child in value.items():
            if key == "cache":
                continue
            if key == "envelope" and isinstance(child, str):
                marker = "/env/"
                pos = child.rfind(marker)
                out[key] = child[pos + len(marker):] if pos >= 0 else Path(child).name
            elif key == "why" and isinstance(child, str):
                out[key] = portable_detail(child)
            else:
                out[key] = portable_manifest(child)
        return out
    if isinstance(value, list):
        return [portable_manifest(child) for child in value]
    return value


def effectful(node):
    if not isinstance(node, dict):
        return False
    kind = node.get("kind")
    if kind in ("CallExpr", "CompoundAssignOperator"):
        return True
    if kind == "UnaryOperator" and node.get("op") in ("++", "--"):
        return True
    if kind == "BinaryOperator" and node.get("op") == "=":
        return True
    return any(effectful(x) for x in child_nodes(node))


def static_walls(env):
    """Return the conservative wall set visible in one envelope."""
    nodes = list(walk(env.get("translation_unit", {})))
    definitions = {
        n.get("name") for n in nodes
        if n.get("kind") == "FunctionDecl" and n.get("body") is not None
    }
    walls = set()
    for n in nodes:
        kind = n.get("kind")
        if kind == "Unsupported":
            walls.add("unsupported:" + str(n.get("c_kind", "?")))
        elif kind == "StringLiteral":
            walls.add("string-literal")
        elif kind == "CallExpr":
            name = callee_name(n.get("callee"))
            if name not in ("abort", "exit") and name not in definitions:
                # Keep the generic fallback for an unresolved callee, but
                # preserve Clang's resolved external name when available so
                # the sole ranking prices one clause-sized library case at a
                # time (memcpy, strlen, vprintf, ...).
                walls.add("libc-call: " + name if name else "libc-call")
        elif kind in ("ImplicitCastExpr", "CStyleCastExpr"):
            cast = n.get("cast")
            if cast in ("IntegralToPointer", "PointerToIntegral", "FloatingCast",
                        "FloatingToIntegral", "IntegralToFloating"):
                walls.add("cast:" + cast)
        elif kind == "BinaryOperator":
            op = n.get("op")
            lhs, rhs = n.get("lhs"), n.get("rhs")
            if op not in ("&&", "||", ",", "=") and effectful(lhs) and effectful(rhs):
                walls.add("unsequenced-effects")
        for key in ("type", "compute_lhs_type", "compute_result_type"):
            ty = n.get(key)
            if isinstance(ty, str) and ("struct " in ty or "union " in ty or
                                        "double" in ty or "float" in ty or
                                        "_Complex" in ty or "[" in ty):
                walls.add("type-layout")
    return sorted(walls)


def load_manifest(path):
    data = json.loads(Path(path).read_text())
    # Cache paths are execution locations, not part of the frozen manifest's
    # identity. Hash only logical pins, source hashes and relative envelope
    # names so an outside cache (or a different machine) produces the same
    # survey provenance.
    identity = portable_manifest(data)
    raw = json.dumps(identity, sort_keys=True, separators=(",", ":")).encode()
    return data, hashlib.sha256(raw).hexdigest()


def build(manifest_path, log_path, commit=None, measured_at=None):
    manifest, manifest_hash = load_manifest(manifest_path)
    by_name = {x["name"]: x for x in manifest.get("tests", [])}
    rows_by_name = {name: (token, detail) for name, token, detail in parse(open(log_path))}
    rows = []
    for name in sorted(by_name):
        rec = by_name[name]
        token, detail = rows_by_name.get(name, ("runner-error", "missing log row"))
        detail = portable_detail(detail)
        env_path = rec.get("envelope")
        env = None
        if rec.get("status") == "parsed" and env_path:
            env = json.loads(Path(env_path).read_text())
        rows.append({
            "name": name,
            "corpus": rec.get("corpus", manifest.get("corpus", "gcc.c-torture/execute")),
            "sha256": rec.get("sha256"),
            "manifest_status": rec.get("status"),
            "verdict": token,
            "detail": detail,
            "static_walls": static_walls(env) if env else [],
            "dynamic_wall": dynamic_wall(token, detail),
        })
    counts = Counter(row["verdict"] for row in rows)
    by_corpus = {}
    for row in rows:
        by_corpus.setdefault(row["corpus"], Counter())[row["verdict"]] += 1
    walls = Counter()
    wall_files = {}
    for row in rows:
        for wall in row["static_walls"]:
            walls[wall] += 1
            wall_files.setdefault(wall, []).append(row["name"])
    ranking = []
    for wall, present in sorted(walls.items()):
        files = sorted(wall_files[wall])
        ranking.append({"wall": wall, "sole": 0, "present": present,
                        "files": files})
    # Calculate sole from each row's complete wall set (kept separate from
    # the counter loop so the definition is visible and easy to audit).
    for item in ranking:
        item["sole"] = sum(1 for row in rows
                            if item["wall"] in row["static_walls"] and
                            len(row["static_walls"]) == 1)
    ranking.sort(key=lambda x: (-x["sole"], -x["present"], x["wall"]))
    dynamic_files = {}
    for row in rows:
        wall = row.get("dynamic_wall")
        if wall:
            dynamic_files.setdefault(wall, []).append(row["name"])
    dynamic_ranking = []
    for wall, files in dynamic_files.items():
        dynamic_ranking.append({
            "wall": wall,
            "sole": sum(1 for row in rows if row.get("dynamic_wall") == wall),
            "present": len(files),
            "files": sorted(files),
        })
    dynamic_ranking.sort(key=lambda x: (-x["sole"], x["wall"]))
    out = {
        "schema": "c-survey-0.1",
        "corpus": manifest.get("corpus", "gcc.c-torture/execute"),
        "manifest_hash": manifest_hash,
        "pin": manifest.get("pin"),
        "total": len(rows),
        "counts": dict(sorted(counts.items())),
        "by_corpus": {k: dict(sorted(v.items())) for k, v in sorted(by_corpus.items())},
        "rows": rows,
        "wall_ranking": ranking,
        "dynamic_wall_ranking": dynamic_ranking,
    }
    if commit is not None:
        out["measured_commit"] = commit
    if measured_at is not None:
        out["measured_at_utc"] = measured_at
    return out


def render(data):
    counts = data.get("counts", {})
    matched = counts.get("passed", 0)
    lines = [
        "# C torture survey",
        "",
        "Generated from the pinned `%s` manifest." % data.get("corpus", "C"),
        "",
        "- verdicts: %d/%d MATCH (passed %d, failed %d, oracle %d)" %
        (matched, data.get("total", 0), counts.get("passed", 0),
         counts.get("failed", 0), counts.get("oracle", 0)),
        "- manifest SHA-256: `%s`" % data.get("manifest_hash", ""),
    ]
    if data.get("measured_commit"):
        lines.append("- measured commit: `%s`" % data["measured_commit"])
    if data.get("measured_at_utc"):
        lines.append("- measured at: `%s`" % data["measured_at_utc"])
    lines += ["", "## Verdict counts", "", "| verdict | files |", "| --- | ---: |"]
    for key, value in sorted(counts.items()):
        lines.append("| `%s` | %d |" % (key, value))
    if data.get("by_corpus"):
        lines += ["", "## Counts by corpus", "", "| corpus | verdict | files |",
                  "| --- | --- | ---: |"]
        for corpus, counts in sorted(data["by_corpus"].items()):
            for verdict, value in sorted(counts.items()):
                lines.append("| `%s` | `%s` | %d |" % (corpus, verdict, value))
    lines += ["", "## Static wall ranking", "",
              "`sole` counts files whose only static wall is the named wall; `present` counts all files containing it.",
              "", "| wall | sole | present | example files |", "| --- | ---: | ---: | --- |"]
    for item in data.get("wall_ranking", []):
        examples = ", ".join(item.get("files", [])[:5])
        lines.append("| `%s` | %d | %d | %s |" %
                     (item["wall"], item["sole"], item["present"], examples))
    lines += ["", "## Dynamic first-refusal ranking", "",
              "The run's first refusal, normalized by construct; `sole` counts rows whose first refusal is this wall.",
              "", "| wall | sole | present | example files |", "| --- | ---: | ---: | --- |"]
    for item in data.get("dynamic_wall_ranking", []):
        examples = ", ".join(item.get("files", [])[:5])
        lines.append("| `%s` | %d | %d | %s |" %
                     (item["wall"], item["sole"], item["present"], examples))
    return "\n".join(lines) + "\n"


def selftest():
    env = {
        "translation_unit": {
            "decls": [
                {"kind": "FunctionDecl", "name": "f",
                 "body": {"kind": "CompoundStmt"}},
                {"kind": "FunctionDecl", "name": "main",
                 "body": {"kind": "CompoundStmt", "body": [
                     {"kind": "BinaryOperator", "op": "=",
                      "lhs": {"kind": "DeclRefExpr"},
                      "rhs": {"kind": "CallExpr", "callee":
                              {"kind": "DeclRefExpr", "name": "f"}}}
                 ]}}
            ]
        }
    }
    walls = static_walls(env)
    if "assignment-call" in walls:
        print("c_survey --self-test: stale assignment wall", file=sys.stderr)
        return 1
    page = render({"counts": {"passed": 1}, "total": 1, "manifest_hash": "x",
                   "wall_ranking": [{"wall": "assignment-call", "sole": 1,
                                     "present": 1, "files": ["x.c"]}]})
    if "assignment-call" not in page or "sole" not in page:
        print("c_survey --self-test: render failed", file=sys.stderr)
        return 1
    m1 = {"cache": "/tmp/a", "tests": [{
        "envelope": "/tmp/a/env/x.json", "why": "/tmp/a/src/x.c:1:1: bad"
    }]}
    m2 = {"cache": "/scratch/b", "tests": [{
        "envelope": "/scratch/b/env/x.json", "why": "/scratch/b/src/x.c:1:1: bad"
    }]}
    if portable_manifest(m1) != portable_manifest(m2):
        print("c_survey --self-test: manifest hash retained a cache path", file=sys.stderr)
        return 1
    if portable_detail(m1["tests"][0]["why"]) != "src/x.c:1:1: bad":
        print("c_survey --self-test: diagnostic path was not normalized", file=sys.stderr)
        return 1
    if dynamic_wall("refused-unsupported", "out of tier: ChooseExpr") != "unsupported:ChooseExpr":
        print("c_survey --self-test: dynamic wall normalization failed", file=sys.stderr)
        return 1
    if dynamic_wall("refused-unsupported", "not an lvalue: StringLiteral") != \
            "unsupported:not an lvalue: StringLiteral":
        print("c_survey --self-test: lvalue wall lost its construct", file=sys.stderr)
        return 1
    print("c_survey --self-test: ok")
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest")
    ap.add_argument("--log")
    ap.add_argument("--json", default=str(DEFAULT_JSON))
    ap.add_argument("--page", default=str(DEFAULT_PAGE))
    ap.add_argument("--commit")
    ap.add_argument("--date")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        return selftest()
    jp, pp = Path(args.json), Path(args.page)
    if args.check:
        data = json.loads(jp.read_text())
        expected = render(data)
        if pp.read_text() != expected:
            print("c_survey: page is stale; regenerate from the committed JSON", file=sys.stderr)
            return 1
        print("c_survey: --check ok")
        return 0
    if not args.manifest or not args.log:
        ap.error("--manifest and --log are required unless --check or --self-test is used")
    data = build(args.manifest, args.log, args.commit, args.date)
    jp.write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
    pp.write_text(render(data))
    print("c_survey: wrote %s and %s" % (jp, pp))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
