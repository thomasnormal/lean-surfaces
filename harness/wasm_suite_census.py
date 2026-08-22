#!/usr/bin/env python3
"""wasm_suite_census.py — census the WebAssembly spec's official `test/core` suite.

Run:
    python3 harness/wasm_suite_census.py <path-to-WebAssembly/spec> -o docs/wasm-suite-census.json
    python3 harness/wasm_suite_census.py <path-to-WebAssembly/spec> --compare docs/wasm-suite-census.json

The suite is the W3C WebAssembly CG's own `test/core` directory: `.wast`
scripts that are SELF-DESCRIBING — each carries its own expectation as an
`assert_*` command — so this census measures the ORACLE as well as the corpus.

Sibling of `harness/c_suite_census.py` (docs/c23-goal.md) and
`harness/c_construct_census.py` (docs/c-tier-charter.md), and it obeys the
same three laws:

  * REFUSE LOUDLY. A missing tree, a tree with no `.wast` files, or a file
    whose parentheses do not balance is an instrument fault and exits
    non-zero. An empty census is never a finding.
  * DETERMINISTIC. Output is sorted; a double run is byte-identical.
  * COMPARABLE. `--compare` diffs against a committed JSON so cross-repo
    staleness is mechanically detectable rather than merely possible.

The corpus is in ANOTHER repository and moves on its own schedule, so the
census records the pinned git revision it was taken at. It is deliberately
NOT wired into `tools/ci.sh`: the tree is not in this repository and not on a
stock runner, so a gate would be a permanent SKIP pretending to be a check.

Python >= 3.9, stdlib only.
"""

import argparse
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

SCHEMA = "wasm-suite-census-0.1"

# The `.wast` script commands, per the reference interpreter's own script
# grammar (interpreter/script/script.ml).  Assertions are listed separately
# because they are the ORACLE: each names the verdict the suite expects.
ASSERT_CMDS = [
    "assert_return",
    "assert_trap:trap",
    "assert_trap:uninstantiable",
    "assert_exhaustion",
    "assert_malformed",
    "assert_malformed_custom",
    "assert_invalid",
    "assert_invalid_custom",
    "assert_unlinkable",
    "assert_uninstantiable",
    "assert_exception",
    "assert_suspension",
]
ACTION_CMDS = ["invoke", "get"]
OTHER_CMDS = [
    "module", "component", "register", "input", "output", "script", "meta",
    "<annotation>", "<inline-module-field>",
]

# `test/core/*.wast` is the core suite; every SUBDIRECTORY is a merged-in
# proposal's own suite, shipped in the same tree but scoped to a feature the
# core spec at a given version may or may not have.
CORE_DIR = "test/core"


class Refusal(Exception):
    """A fault in the instrument's input. Never swallowed, never a finding."""


# ---------------------------------------------------------------- tokenizing


def strip_wast(text):
    """Blank out `;;` line comments, `(; ... ;)` block comments (nestable) and
    the CONTENTS of string literals, preserving byte offsets and newlines.

    Preserving offsets is what lets the command scanner report line numbers
    that point into the real file. Strings are blanked rather than removed
    because `.wast` string literals routinely contain parentheses and
    semicolons -- `(data "\\28;)")` is a real shape -- and a scanner that read
    them as syntax would mis-nest."""
    out = list(text)
    i, n = 0, len(text)
    depth = 0  # block-comment nesting
    while i < n:
        c = text[i]
        if depth > 0:
            if text.startswith("(;", i):
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if text.startswith(";)", i):
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if c != "\n":
                out[i] = " "
            i += 1
            continue
        if text.startswith("(;", i):
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if text.startswith(";;", i):
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if c == '"':
            i += 1
            while i < n:
                if text[i] == "\\" and i + 1 < n:
                    out[i] = out[i + 1] = " "
                    i += 2
                    continue
                if text[i] == '"':
                    break
                if text[i] != "\n":
                    out[i] = " "
                i += 1
            if i >= n:
                raise Refusal("unterminated string literal")
            i += 1
            continue
        i += 1
    if depth != 0:
        raise Refusal("unterminated block comment")
    return "".join(out)


HEAD_RE = re.compile(r"[A-Za-z0-9_.:=+\-*/\\^~<>!?@#$%&|'`]+")


def top_level_commands(stripped):
    """Yield (head, start_offset, end_offset) for every top-level s-expression."""
    depth = 0
    start = None
    for i, c in enumerate(stripped):
        if c == "(":
            if depth == 0:
                start = i
            depth += 1
        elif c == ")":
            if depth == 0:
                raise Refusal(f"unbalanced ')' at offset {i}")
            depth -= 1
            if depth == 0:
                m = HEAD_RE.search(stripped, start + 1, i)
                head = m.group(0) if m else ""
                yield head, start, i + 1
                start = None
    if depth != 0:
        raise Refusal("unbalanced '(' -- file does not close")


# ------------------------------------------------------------------ counting

# Fold-instruction and module-field heads that are NOT wasm instructions.
NON_INSTR_HEADS = {
    "module", "func", "param", "result", "local", "type", "import", "export",
    "table", "memory", "global", "elem", "data", "start", "mut", "offset",
    "item", "field", "struct", "array", "sub", "rec", "tag", "func_ref",
    "extern_ref", "any_ref", "eq_ref", "i31_ref", "struct_ref", "array_ref",
    "none_ref", "nofunc_ref", "noextern_ref", "exn_ref", "noexn_ref",
    "cont", "shared", "declare", "then", "do", "catch", "catch_all",
}
# The keywords a WAT type/valtype position can hold; counted separately.
VALTYPES = {
    "i32", "i64", "f32", "f64", "v128", "funcref", "externref", "anyref",
    "eqref", "i31ref", "structref", "arrayref", "nullref", "nullfuncref",
    "nullexternref", "exnref", "nullexnref",
}

INSTR_RE = re.compile(r"(?<![\w.$])([a-z][a-z0-9_]*(?:\.[a-z0-9_]+)*)(?![\w.$])")


ARG_RE = re.compile(r"\(\s*([A-Za-z_][A-Za-z0-9_.]*)")

# Module fields that may appear at TOP LEVEL under the text format's
# "inline module" abbreviation -- a whole file of fields is one module whose
# `(module …)` wrapper is elided (test/core/inline-module.wast).
MODULE_FIELD_HEADS = {
    "func", "memory", "table", "global", "type", "import", "export",
    "elem", "data", "start", "tag", "rec",
}


def classify_assert_trap(body):
    """`assert_trap` is OVERLOADED in the text format.

    parser.mly has BOTH
        (assert_trap <script_instance> <string>)  ->  AssertUninstantiable
        (assert_trap <action>          <string>)  ->  AssertTrap
    so the same surface keyword denotes two distinct semantic obligations:
    a module whose INSTANTIATION traps, versus an action that traps. There is
    no `assert_uninstantiable` keyword in the lexer at all. Keying a verdict
    system on the keyword would conflate them, so the census splits by the
    shape of the first argument."""
    m = ARG_RE.search(body, 1)
    if not m:
        return "malformed"
    return "uninstantiable" if m.group(1) == "module" else "trap"


def census_file(path, root):
    text = path.read_text(encoding="utf-8", errors="strict")
    stripped = strip_wast(text)
    rel = str(path.relative_to(root))
    cmds = Counter()
    module_forms = Counter()
    n_lines = text.count("\n") + (0 if text.endswith("\n") or not text else 1)
    for head, s, e in top_level_commands(stripped):
        body = stripped[s:e]
        if head.startswith("@"):
            # A `(@id …)` ANNOTATION is a LEXICAL construct (lexer.mll:823-829),
            # recorded out of band and legal anywhere -- including where a
            # command goes. It is not a script command.
            cmds["<annotation>"] += 1
            continue
        if head in MODULE_FIELD_HEADS:
            cmds["<inline-module-field>"] += 1
            continue
        if head == "assert_trap":
            cmds["assert_trap:" + classify_assert_trap(body)] += 1
            continue
        cmds[head] += 1
        if head == "module":
            if re.search(r"\bbinary\b", body[:200]):
                module_forms["binary"] += 1
            elif re.search(r"\bquote\b", body[:200]):
                module_forms["quote"] += 1
            else:
                module_forms["text"] += 1
    # Instruction vocabulary: every dotted-or-bare lowercase keyword that is
    # not a module field head or a valtype. Approximate BY DESIGN -- reported
    # as `keyword_vocab`, never as "instructions used".
    vocab = Counter()
    for m in INSTR_RE.finditer(stripped):
        w = m.group(1)
        if w in NON_INSTR_HEADS or w in VALTYPES:
            continue
        vocab[w] += 1
    # Per-file license evidence -- the c-testsuite trap check (docs/c23-goal.md
    # §2). Anything that looks like a copyright line or an SPDX tag.
    lic = []
    for ln in text.splitlines()[:40]:
        if re.search(r"copyright|SPDX-License|\blicen[sc]e\b", ln, re.I):
            lic.append(ln.strip())
    return {
        "path": rel,
        "lines": n_lines,
        "bytes": len(text.encode("utf-8")),
        "commands": dict(sorted(cmds.items())),
        "module_forms": dict(sorted(module_forms.items())),
        "license_lines": lic,
        "keyword_vocab": dict(sorted(vocab.items())),
    }


def git_rev(root):
    try:
        r = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "HEAD"],
            capture_output=True, text=True, timeout=30,
        )
        if r.returncode == 0:
            return r.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        pass
    return None


def git_describe(root):
    try:
        r = subprocess.run(
            ["git", "-C", str(root), "describe", "--tags", "--always"],
            capture_output=True, text=True, timeout=30,
        )
        if r.returncode == 0:
            return r.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        pass
    return None


def census(root):
    root = Path(root).resolve()
    if not root.is_dir():
        raise Refusal(f"not a directory: {root}")
    core = root / "test" / "core"
    if not core.is_dir():
        raise Refusal(f"no test/core under {root} -- is this the WebAssembly/spec tree?")
    files = sorted(core.rglob("*.wast"), key=lambda p: str(p))
    if not files:
        raise Refusal(f"zero .wast files under {core} -- an empty census is an instrument fault")

    rows = [census_file(p, root) for p in files]

    by_dir = {}
    for r in rows:
        d = str(Path(r["path"]).parent)
        b = by_dir.setdefault(d, {"files": 0, "lines": 0, "asserts": 0, "modules": 0})
        b["files"] += 1
        b["lines"] += r["lines"]
        b["asserts"] += sum(v for k, v in r["commands"].items() if k.startswith("assert_"))
        b["modules"] += r["commands"].get("module", 0)

    all_cmds = Counter()
    all_forms = Counter()
    all_vocab = Counter()
    for r in rows:
        all_cmds.update(r["commands"])
        all_forms.update(r["module_forms"])
        all_vocab.update(r["keyword_vocab"])

    asserts = {k: v for k, v in sorted(all_cmds.items()) if k.startswith("assert_")}
    unknown = sorted(k for k in all_cmds if k not in ASSERT_CMDS + ACTION_CMDS + OTHER_CMDS)

    licensed = [r["path"] for r in rows if r["license_lines"]]

    # The core suite is `test/core/*.wast`; each SUBDIRECTORY is a merged
    # proposal's own suite. The split is the version question in corpus form.
    def bucket(pred):
        sel = [r for r in rows if pred(r)]
        c, v = Counter(), Counter()
        for r in sel:
            c.update(r["commands"])
            v.update(r["keyword_vocab"])
        return {
            "files": len(sel),
            "lines": sum(r["lines"] for r in sel),
            "commands": sum(c.values()),
            "assertions": sum(x for k, x in c.items() if k.startswith("assert_")),
            "modules": c.get("module", 0),
            "distinct_keywords": len(v),
            "by_assert": {k: x for k, x in sorted(c.items()) if k.startswith("assert_")},
        }

    flat = bucket(lambda r: str(Path(r["path"]).parent) == CORE_DIR)
    prop = bucket(lambda r: str(Path(r["path"]).parent) != CORE_DIR)
    core_vocab = Counter()
    for r in rows:
        if str(Path(r["path"]).parent) == CORE_DIR:
            core_vocab.update(r["keyword_vocab"])

    return {
        "schema": SCHEMA,
        "corpus": "WebAssembly/spec test/core",
        "revision": git_rev(root),
        "describe": git_describe(root),
        "totals": {
            "wast_files": len(rows),
            "lines": sum(r["lines"] for r in rows),
            "bytes": sum(r["bytes"] for r in rows),
            "commands": sum(sum(r["commands"].values()) for r in rows),
            "assertions": sum(asserts.values()),
            "modules": all_cmds.get("module", 0),
            "distinct_keywords": len(all_vocab),
        },
        "assertions": asserts,
        "actions": {k: all_cmds.get(k, 0) for k in ACTION_CMDS if all_cmds.get(k)},
        "other_commands": {k: all_cmds.get(k, 0) for k in OTHER_CMDS if all_cmds.get(k)},
        "unknown_command_heads": unknown,
        "module_forms": dict(sorted(all_forms.items())),
        "core_flat": flat,
        "proposal_subdirs": prop,
        "core_flat_keyword_vocab": dict(sorted(core_vocab.items(), key=lambda kv: (-kv[1], kv[0]))),
        "by_directory": dict(sorted(by_dir.items())),
        "files_with_license_lines": sorted(licensed),
        "keyword_vocab": dict(sorted(all_vocab.items(), key=lambda kv: (-kv[1], kv[0]))),
        "files": rows,
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("spec_root", help="path to a WebAssembly/spec checkout")
    ap.add_argument("-o", "--out", help="write JSON here")
    ap.add_argument("--compare", help="diff against a previously written JSON")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    try:
        data = census(args.spec_root)
    except Refusal as e:
        print(f"REFUSED: {e}", file=sys.stderr)
        return 2
    except (OSError, UnicodeDecodeError) as e:
        print(f"REFUSED: {e}", file=sys.stderr)
        return 2

    blob = json.dumps(data, indent=2, sort_keys=False) + "\n"

    if args.out:
        Path(args.out).write_text(blob, encoding="utf-8")

    if args.compare:
        old = json.loads(Path(args.compare).read_text(encoding="utf-8"))
        drift = 0
        print(f"revision  {old.get('revision')} -> {data.get('revision')}")
        for k in sorted(set(old["totals"]) | set(data["totals"])):
            a, b = old["totals"].get(k), data["totals"].get(k)
            if a != b:
                print(f"  {k:24s} {a} -> {b}")
                drift += 1
        oa, na = set(old["assertions"]), set(data["assertions"])
        if oa - na:
            print(f"  assertions DROPPED: {sorted(oa - na)}")
            drift += 1
        if na - oa:
            print(f"  assertions ADDED:   {sorted(na - oa)}")
            drift += 1
        ov, nv = set(old["keyword_vocab"]), set(data["keyword_vocab"])
        if ov - nv:
            print(f"  keywords DROPPED ({len(ov - nv)}): {sorted(ov - nv)[:20]}")
            drift += 1
        if nv - ov:
            print(f"  keywords ADDED   ({len(nv - ov)}): {sorted(nv - ov)[:20]}")
            drift += 1
        if not drift:
            print("no drift")
        return 0

    if not args.quiet:
        t = data["totals"]
        print(f"{data['corpus']} @ {data['describe']} ({data['revision']})")
        print(f"  {t['wast_files']} .wast files, {t['lines']} lines, "
              f"{t['commands']} top-level commands, {t['assertions']} assertions, "
              f"{t['modules']} modules, {t['distinct_keywords']} distinct keywords")
        for k, v in data["assertions"].items():
            print(f"    {k:26s} {v}")
        for k, v in data["actions"].items():
            print(f"    {k:26s} {v}")
        print(f"  module forms: {data['module_forms']}")
        for name in ("core_flat", "proposal_subdirs"):
            b = data[name]
            print(f"  {name:18s} files={b['files']:4d} lines={b['lines']:7d} "
                  f"cmds={b['commands']:6d} asserts={b['assertions']:6d} "
                  f"modules={b['modules']:5d} keywords={b['distinct_keywords']}")
        if data["unknown_command_heads"]:
            print(f"  UNKNOWN heads: {data['unknown_command_heads']}")
        print(f"  files carrying a license/copyright line: "
              f"{len(data['files_with_license_lines'])} of {t['wast_files']}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
