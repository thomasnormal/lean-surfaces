#!/usr/bin/env python3
"""wasm_sorry_census.py — census the LIVE proof obligations in a Lean tree.

Run:
    python3 harness/wasm_sorry_census.py <file-or-dir>... -o docs/wasm-sorry-census.json
    python3 harness/wasm_sorry_census.py <dir> --compare docs/wasm-sorry-census.json
    python3 harness/wasm_sorry_census.py <file> --show          # print each obligation

WHY THIS EXISTS.  `docs/wasm-charter.md` §8.1 reported "13 sorry" in the
SpecTec→Lean backend's proof lane, from a textual grep.  A textual grep
counts `sorry` inside `--` comments, and this instrument was written because
that number decides a milestone: Thomas ruled the SOUNDNESS path on the
strength of it.

The rule this instrument enforces: **a commented-out `sorry` is not a proof
obligation.**  It is a note about work someone was thinking about.  Counting
it inflates the obligation ledger, and an inflated ledger is the kind of
wrong fact this repository does not ship.

So the census strips Lean 4 comments (`--` to end of line, nestable
`/- … -/`) and string/char literals BEFORE looking for the token, exactly as
`harness/wasm_suite_census.py` strips `.wast` comments before scanning for
commands, and for the same reason: a scanner that reads commentary as syntax
produces a plausible wrong table.

It reports BOTH numbers — the raw grep count and the live count — because
the DELTA is the finding, not either number alone.

Refusal law, unchanged from its siblings: a missing path, a tree with no
`.lean` files, or an unterminated comment/string is an instrument fault and
exits non-zero.  An empty census is never a finding.

Python >= 3.9, stdlib only.
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

SCHEMA = "wasm-sorry-census-0.1"

# Tokens that stand for an unproved obligation in Lean 4.
OBLIGATION_TOKENS = ["sorry", "sorryAx", "admit"]

# Keywords that open a top-level declaration.  `sorry` is attributed to the
# nearest preceding one at indentation 0.
DECL_KWS = [
    "theorem", "lemma", "def", "abbrev", "example", "instance", "inductive",
    "structure", "class", "opaque", "axiom", "partial def", "unsafe def",
]
# Modifiers that may precede the keyword on the same line.
MODIFIERS = r"(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+|nonrec\s+|scoped\s+|local\s+)*"
DECL_RE = re.compile(r"^" + MODIFIERS + r"(" + "|".join(DECL_KWS) + r")\b[ \t]*([^\s:({\[]*)")

RAW_RE = re.compile(r"(?<![A-Za-z0-9_'!?])(" + "|".join(OBLIGATION_TOKENS) + r")(?![A-Za-z0-9_'!?])")


class Refusal(Exception):
    """A fault in the instrument's input. Never swallowed, never a finding."""


def strip_lean(text, path="<input>"):
    """Blank Lean 4 comments and literal contents, PRESERVING byte offsets.

    Offsets are preserved so line numbers reported against the stripped text
    point into the real file.  Nestable `/- … -/` is handled properly (Lean
    nests them); `--` runs to end of line; `"…"` honours backslash escapes.

    Doc comments `/-- … -/` are comments too and are stripped: a `sorry` in a
    docstring is prose."""
    out = list(text)
    i, n = 0, len(text)
    depth = 0
    while i < n:
        c = text[i]
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if text.startswith("-/", i):
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if c != "\n":
                out[i] = " "
            i += 1
            continue
        if text.startswith("/-", i):
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if c == '"':
            out[i] = " "
            i += 1
            while i < n:
                if text[i] == "\\" and i + 1 < n:
                    out[i] = out[i + 1] = " "
                    i += 2
                    continue
                if text[i] == '"':
                    out[i] = " "
                    i += 1
                    break
                if text[i] != "\n":
                    out[i] = " "
                i += 1
            else:
                raise Refusal(f"{path}: unterminated string literal")
            continue
        i += 1
    if depth != 0:
        raise Refusal(f"{path}: unterminated block comment (depth {depth})")
    return "".join(out)


def line_of(text, off):
    return text.count("\n", 0, off) + 1


def enclosing_decl(lines, lineno):
    """Nearest preceding top-level declaration for a 1-based line number."""
    for i in range(lineno - 1, -1, -1):
        m = DECL_RE.match(lines[i])
        if m:
            return {"kind": m.group(1), "name": m.group(2) or "<anonymous>", "line": i + 1}
    return None


def census_file(path, root=None):
    text = path.read_text(encoding="utf-8", errors="strict")
    stripped = strip_lean(text, str(path))
    lines = text.splitlines()
    rel = str(path.relative_to(root)) if root else str(path)

    raw = [(m.group(1), line_of(text, m.start())) for m in RAW_RE.finditer(text)]
    live = [(m.group(1), line_of(text, m.start())) for m in RAW_RE.finditer(stripped)]
    live_lines = {ln for _, ln in live}

    obligations = []
    for tok, ln in live:
        d = enclosing_decl(lines, ln)
        obligations.append({
            "token": tok,
            "line": ln,
            "decl_kind": d["kind"] if d else None,
            "decl_name": d["name"] if d else None,
            "decl_line": d["line"] if d else None,
            "text": lines[ln - 1].strip()[:160] if ln - 1 < len(lines) else "",
        })

    commented = [{"token": t, "line": l, "text": lines[l - 1].strip()[:160]}
                 for t, l in raw if l not in live_lines]

    return {
        "path": rel,
        "lines": len(lines),
        "raw_count": len(raw),
        "live_count": len(live),
        "commented_out": len(commented),
        "obligations": obligations,
        "commented_sites": commented,
    }


def git_rev(root):
    try:
        r = subprocess.run(["git", "-C", str(root), "rev-parse", "HEAD"],
                           capture_output=True, text=True, timeout=30)
        if r.returncode == 0:
            return r.stdout.strip()
    except (OSError, subprocess.SubprocessError):
        pass
    return None


def census(paths):
    files = []
    root = None
    for p in paths:
        p = Path(p).resolve()
        if p.is_dir():
            root = root or p
            files.extend(sorted(p.rglob("*.lean"), key=str))
        elif p.is_file():
            files.append(p)
        else:
            raise Refusal(f"no such path: {p}")
    if not files:
        raise Refusal("zero .lean files found -- an empty census is an instrument fault")

    rows = [census_file(f, root if root and str(f).startswith(str(root)) else None) for f in files]
    with_ob = [r for r in rows if r["live_count"]]

    return {
        "schema": SCHEMA,
        "revision": git_rev(root or files[0].parent),
        "totals": {
            "files_scanned": len(rows),
            "files_with_obligations": len(with_ob),
            "raw_count": sum(r["raw_count"] for r in rows),
            "live_count": sum(r["live_count"] for r in rows),
            "commented_out": sum(r["commented_out"] for r in rows),
        },
        "files": [r for r in rows if r["raw_count"]],
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("paths", nargs="+")
    ap.add_argument("-o", "--out")
    ap.add_argument("--compare")
    ap.add_argument("--show", action="store_true", help="print every live obligation")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    try:
        data = census(args.paths)
    except Refusal as e:
        print(f"REFUSED: {e}", file=sys.stderr)
        return 2
    except (OSError, UnicodeDecodeError) as e:
        print(f"REFUSED: {e}", file=sys.stderr)
        return 2

    if args.out:
        Path(args.out).write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")

    if args.compare:
        old = json.loads(Path(args.compare).read_text(encoding="utf-8"))
        drift = 0
        for k in sorted(set(old["totals"]) | set(data["totals"])):
            a, b = old["totals"].get(k), data["totals"].get(k)
            if a != b:
                print(f"  {k:24s} {a} -> {b}")
                drift += 1
        print("no drift" if not drift else f"{drift} total(s) drifted")
        return 0

    if not args.quiet:
        t = data["totals"]
        print(f"{t['files_scanned']} .lean files, {t['files_with_obligations']} carry obligations")
        print(f"  raw grep count : {t['raw_count']}")
        print(f"  LIVE count     : {t['live_count']}")
        print(f"  commented out  : {t['commented_out']}"
              f"  <-- counted by grep, NOT an obligation")
        for r in data["files"]:
            print(f"    {r['live_count']:4d} live / {r['raw_count']:4d} raw   {r['path']}")
        if args.show:
            for r in data["files"]:
                if not r["obligations"]:
                    continue
                print(f"\n=== {r['path']} ===")
                for o in r["obligations"]:
                    print(f"  L{o['line']:<6d} {o['decl_kind'] or '?'} {o['decl_name']} "
                          f"(decl at L{o['decl_line']})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
