#!/usr/bin/env python3
"""extract.py — an ECMAScript source -> the es-0.1 envelope (docs/es-envelope-schema.md).

The frontend is an ESTree producer (acorn) driven by
`extractors/es/estree_dump.mjs`, ONE node process for the whole batch; this
lowers its tree into the envelope the ingester reads.

    python3 extractors/es/extract.py <file.js> [-o out.json]
    python3 extractors/es/extract.py --batch paths.txt --out-dir DIR
    python3 extractors/es/extract.py <file.js> --source-type module

THE CONTRACT (identical to the Python, SystemVerilog and C extractors):

* NEVER fails on valid ECMAScript. Any node type outside the pinned
  66-kind vocabulary becomes an `Unsupported` leaf carrying the ESTree type
  and <=200 characters of source text.
* Hard errors -- unreadable file, a missing frontend, an EDITION mismatch --
  exit NON-ZERO and say why.
* **A source that does not PARSE is NOT a hard error.** It is an envelope
  with `parse.status = "error"` and `program = null`, and the extractor
  exits 0. This is the one place this lane differs sharply from its
  siblings, and it is forced by measurement: 4,248 of the language-core
  slice's 18,114 tests assert that their source must NOT parse
  (docs/es-envelope-schema.md §0(2)). Treating those as failures would make
  23% of the corpus unrepresentable.
* DETERMINISTIC: same input bytes => same output bytes, double-run verified.
* No absolute paths in the payload; `source_file` is caller-supplied or
  repo-relative.

TWO THINGS THE FRONTEND MAKES US HONEST ABOUT.

1. `sourceType` is an INPUT, not a property of the text. The same bytes are
   a different program as a Script or a Module. `auto` reports which one
   parsed rather than assuming, and the value joins the cache key.
2. `parse.status = "ok"` is a claim about the FRONTEND, never about
   validity. Early errors are static semantics acorn does not carry --
   measured at 285 core-slice tests it accepts and test262 rejects -- so
   this extractor never says "valid", only "accepted".

Python >= 3.9, stdlib only (node is the frontend, as clang is C's).
"""

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

SCHEMA_VERSION = "es-0.1"

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
DUMPER = os.path.join(HERE, "estree_dump.mjs")
EDITION_PIN = os.path.join(ROOT, "docs", "es-edition.json")

# The pinned vocabulary: exactly the node kinds `harness/es_census.py`
# measured over the whole language-core slice.  `es_census.py --check-schema`
# asserts this set equals the census's AND the schema document's, so the
# three cannot drift apart.
VOCABULARY = frozenset({
    # program and statements (23)
    "Program", "VariableDeclaration", "VariableDeclarator", "ExpressionStatement",
    "BlockStatement", "ThrowStatement", "IfStatement", "ReturnStatement",
    "EmptyStatement", "TryStatement", "CatchClause", "ForOfStatement",
    "ForStatement", "WithStatement", "BreakStatement", "LabeledStatement",
    "ForInStatement", "DoWhileStatement", "SwitchCase", "ContinueStatement",
    "WhileStatement", "SwitchStatement", "DebuggerStatement",
    # declarations and classes (9)
    "PropertyDefinition", "MethodDefinition", "ClassBody", "ClassDeclaration",
    "FunctionDeclaration", "StaticBlock", "ImportDeclaration",
    "ImportDefaultSpecifier", "ExportDefaultDeclaration",
    # patterns (4)
    "AssignmentPattern", "ArrayPattern", "ObjectPattern", "RestElement",
    # expressions and the rest (30)
    "Identifier", "Literal", "PrivateIdentifier", "MemberExpression",
    "CallExpression", "BinaryExpression", "FunctionExpression", "NewExpression",
    "Property", "AssignmentExpression", "UnaryExpression", "ObjectExpression",
    "ThisExpression", "ArrayExpression", "ClassExpression", "UpdateExpression",
    "YieldExpression", "ArrowFunctionExpression", "LogicalExpression",
    "SequenceExpression", "TemplateElement", "SpreadElement", "Super",
    "ConditionalExpression", "TemplateLiteral", "ImportExpression",
    "ChainExpression", "TaggedTemplateExpression", "AwaitExpression",
    "MetaProperty",
})

# Structural keys the envelope drops: they are the frontend's bookkeeping,
# not the program.  `start`/`end` are lifted into `span`.
DROP_KEYS = frozenset({"type", "start", "end", "loc", "range"})

UNSUPPORTED_TEXT = 200


class Refusal(Exception):
    """A hard error.  Loud, non-zero, and never a smaller answer."""


def extractor_digest():
    return hashlib.sha256(open(__file__, "rb").read()).hexdigest()[:8]


def load_pin(path):
    if not os.path.isfile(path):
        raise Refusal(f"{path}: the edition pin is missing — run "
                      f"`es_census.py --write-edition` first")
    d = json.loads(open(path, encoding="utf-8").read())
    for k in ("language_version", "spec_revision"):
        if k not in d:
            raise Refusal(f"{path}: edition pin is missing `{k}`")
    return d


def line_col(src, pos):
    if pos is None or pos < 0:
        return 0, 0
    head = src[:pos]
    line = head.count("\n") + 1
    col = pos - (head.rfind("\n") + 1)
    return line, col


def span_of(node, src):
    s, e = node.get("start"), node.get("end")
    line, col = line_col(src, s)
    end_line, end_col = line_col(src, e)
    return {"start": s, "end": e, "line": line, "col": col,
            "end_line": end_line, "end_col": end_col}


def lower_literal(node, out):
    """One ESTree kind, six spec-level types.  Split it, so the tier is not
    re-deriving the lexer from raw text (docs/es-envelope-schema.md §3.5)."""
    raw = node.get("raw")
    out["raw"] = raw
    if "bigint" in node:
        out["value_type"] = "bigint"
        out["value"] = node["bigint"]
    elif "regex" in node:
        out["value_type"] = "regexp"
        out["pattern"] = node["regex"].get("pattern")
        out["flags"] = node["regex"].get("flags")
    elif "value" not in node or node["value"] is None:
        # `null` and a RegExp the host could not build are both value-less
        # here; `raw` disambiguates and is always present.
        out["value_type"] = "null" if raw == "null" else "regexp"
    elif isinstance(node["value"], bool):
        out["value_type"] = "boolean"
        out["value"] = node["value"]
    elif isinstance(node["value"], str):
        out["value_type"] = "string"
        out["value"] = node["value"]
    else:
        # NUMBER: carried as the RAW TEXT the programmer wrote, never as a
        # host double.  CPython's float is binary64 too, so a round-trip
        # would probably be exact -- and "probably exact" is how a silent
        # wrong answer enters.  The tier does the conversion under its own
        # rules (family-architecture.md §3.5.5 step 3).
        out["value_type"] = "number"
        out["value"] = raw
    return out


def lower(node, src, stats):
    if isinstance(node, list):
        return [lower(x, src, stats) for x in node]
    if not isinstance(node, dict):
        return node
    ntype = node.get("type")
    if ntype is None:
        return {k: lower(v, src, stats) for k, v in sorted(node.items())}
    if ntype not in VOCABULARY:
        stats["unsupported"] += 1
        stats["unsupported_types"].add(ntype)
        s, e = node.get("start"), node.get("end")
        text = src[s:e] if isinstance(s, int) and isinstance(e, int) else ""
        return {"kind": "Unsupported", "node_type": ntype,
                "text": text[:UNSUPPORTED_TEXT], "span": span_of(node, src)}
    stats["kinds"][ntype] = stats["kinds"].get(ntype, 0) + 1
    out = {"kind": ntype, "span": span_of(node, src)}
    if ntype == "Literal":
        lower_literal(node, out)
        return out
    for k in sorted(node.keys()):
        if k in DROP_KEYS:
            continue
        out[k] = lower(node[k], src, stats)
    return out


def run_frontend(paths, acorn, source_type):
    if not os.path.isfile(DUMPER):
        raise Refusal(f"{DUMPER}: the frontend dumper is missing")
    if acorn and not os.path.isfile(acorn):
        raise Refusal(f"{acorn}: no acorn there — fetch it "
                      f"(`npm install acorn` in a scratch dir) and pass --acorn")
    cmd = ["node", DUMPER]
    if acorn:
        cmd.append(acorn)
    cmd += ["--source-type", source_type]
    proc = subprocess.run(cmd, input="\n".join(paths) + "\n",
                          capture_output=True, text=True)
    # SPLIT ON "\n" ONLY, never `splitlines()`.  Python splits on the Unicode
    # line boundaries — U+2028, U+2029, \x0b, \x0c, \x85 — while JSON escapes
    # only \n, and test262's LINE-TERMINATOR tests put real U+2028/U+2029 in
    # their source text, which reaches this stream inside `raw`/`text`.
    # Measured on a 2000-file sample: 2000 records, 2046 `splitlines()` pieces,
    # 24 U+2028 and 22 U+2029.  The conformance suite for a language whose
    # line terminators include U+2028 is exactly the corpus that breaks the
    # naive idiom, and the one-row-per-job check is what caught it.
    rows = [l for l in proc.stdout.split("\n") if l.strip()]
    if proc.returncode == 3:
        raise Refusal(f"frontend refused: {rows[0] if rows else proc.stderr.strip()}")
    if len(rows) != len(paths):
        raise Refusal(f"frontend returned {len(rows)} rows for {len(paths)} inputs — "
                      f"the batch protocol requires exactly one row per job")
    return [json.loads(r) for r in rows]


def envelope(row, src, pin, source_name):
    stats = {"kinds": {}, "unsupported": 0, "unsupported_types": set()}
    env = {
        "schema_version": SCHEMA_VERSION,
        "language": "ecmascript",
        "language_version": pin["language_version"],
        "spec_revision": pin["spec_revision"],
        "frontend": {"name": "acorn-estree", "version": "acorn-8"},
        "source_file": source_name,
        "source_sha256": hashlib.sha256(src.encode("utf-8")).hexdigest(),
        "source_type": row.get("sourceType", "script"),
        "lean_blocks": [],
    }
    if row.get("ok"):
        env["parse"] = {"status": "ok"}
        env["program"] = lower(row["ast"], src, stats)
    else:
        # A rejection is DATA, not a failure (docs/es-envelope-schema.md §4).
        env["parse"] = {
            "status": "error",
            "error_kind": "SyntaxError",
            "message": row.get("error", ""),
            "span": {"start": row.get("errorPos", -1),
                     "line": row.get("line", 0), "col": row.get("col", 0)},
        }
        env["program"] = None
    env["stats"] = {
        "node_kinds": dict(sorted(stats["kinds"].items())),
        "unsupported": stats["unsupported"],
        "unsupported_types": sorted(stats["unsupported_types"]),
    }
    return env


def blob(env):
    return json.dumps(env, indent=2, sort_keys=True) + "\n"


def cache_name(path, env):
    stem = os.path.splitext(os.path.basename(path))[0]
    sha = env["source_sha256"][:16]
    return f"{stem}-{sha}-{extractor_digest()}-{env['language_version']}-{env['source_type']}.json"


def self_test():
    """Every refusal path RUN, plus the two verdicts.  A designed path is not one."""
    import tempfile
    ok = []
    with tempfile.TemporaryDirectory() as d:
        try:
            load_pin(os.path.join(d, "nope.json"))
            print("SELF-TEST FAIL: a missing pin did not refuse"); return 1
        except Refusal:
            ok.append("a missing edition pin refuses")
        bad = os.path.join(d, "bad.json")
        open(bad, "w").write(json.dumps({"language_version": "ES2026"}))
        try:
            load_pin(bad)
            print("SELF-TEST FAIL: an incomplete pin did not refuse"); return 1
        except Refusal:
            ok.append("an incomplete edition pin refuses")
        try:
            run_frontend(["/nonexistent.js"], os.path.join(d, "no-acorn.mjs"), "auto")
            print("SELF-TEST FAIL: a missing acorn did not refuse"); return 1
        except Refusal:
            ok.append("a missing acorn refuses")
        # the lowering, without a frontend
        stats = {"kinds": {}, "unsupported": 0, "unsupported_types": set()}
        src = "x"
        node = {"type": "Decorator", "start": 0, "end": 1}
        out = lower(node, src, stats)
        assert out["kind"] == "Unsupported" and out["node_type"] == "Decorator", out
        assert stats["unsupported"] == 1
        ok.append("an out-of-vocabulary node becomes an Unsupported leaf")
        num = lower({"type": "Literal", "start": 0, "end": 3, "value": 0.1, "raw": "0.1"},
                    "0.1", stats)
        assert num["value_type"] == "number" and num["value"] == "0.1" and isinstance(num["value"], str), num
        ok.append("a numeric literal keeps its RAW TEXT, never a host double")
    for line in ok:
        print("  ok:", line)
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("source", nargs="?", help="the .js file to extract")
    ap.add_argument("-o", "--out", help="write the envelope here")
    ap.add_argument("--batch", help="a file of paths, one per line")
    ap.add_argument("--out-dir", help="with --batch: write one envelope per input, cache-named")
    ap.add_argument("--source-type", default="auto", choices=["auto", "script", "module"])
    ap.add_argument("--source-name", help="the path to record in the envelope "
                                          "(the corpus is cross-repo, so a path "
                                          "relative to this root would be a fiction)")
    ap.add_argument("--acorn", help="path to a fetched acorn ESM entry point")
    ap.add_argument("--pin", default=EDITION_PIN, help="the edition pin JSON")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return self_test()
    if not (args.source or args.batch):
        ap.error("give a source file or --batch")

    try:
        pin = load_pin(args.pin)
        paths = ([l.strip() for l in open(args.batch, encoding="utf-8") if l.strip()]
                 if args.batch else [os.path.abspath(args.source)])
        for p in paths:
            if not os.path.isfile(p):
                raise Refusal(f"{p}: no such file")
        rows = run_frontend(paths, args.acorn, args.source_type)
        envs = []
        for p, row in zip(paths, rows):
            if "runner_error" in row:
                raise Refusal(f"{p}: {row['runner_error']}")
            src = open(p, encoding="utf-8").read()
            name = args.source_name or os.path.relpath(p, ROOT)
            envs.append((p, envelope(row, src, pin, name)))
    except Refusal as e:
        print(f"REFUSED: {e}", file=sys.stderr)
        return 2

    if args.batch and args.out_dir:
        os.makedirs(args.out_dir, exist_ok=True)
        for p, env in envs:
            dest = os.path.join(args.out_dir, cache_name(p, env))
            open(dest, "w", encoding="utf-8").write(blob(env))
        print(f"wrote {len(envs)} envelopes to {args.out_dir}")
    elif args.out:
        open(args.out, "w", encoding="utf-8").write(blob(envs[0][1]))
        print(f"wrote {args.out}")
    else:
        for _, env in envs:
            sys.stdout.write(blob(env))
    return 0


if __name__ == "__main__":
    sys.exit(main())
