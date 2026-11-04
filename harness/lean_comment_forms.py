#!/usr/bin/env python3
"""Two comment-FORM checks over the Lean tree. Each cost the analog lane real
tenure time on 2026-08-24, and neither is caught by anything else we run.

A comment is not syntactically inert.

CHECK 1 -- DANGLING DOC COMMENT.  A doc comment is GRAMMAR: it opens
`declModifiers`, and the parser then REQUIRES a declaration.  Anything else
after it is a parse error reported one token later, which is why the message
(`unexpected token 'X'; expected 'lemma'`) names the innocent token X and not
the doc comment that caused it.

THE FAMILY IS "A TOKEN IN A DECLARATION SLOT", and this lane hit it three
times on one landing, at a cost of three tenures:
  1. a doc comment marking a declaration's ABSENCE -- it occupies the slot it
     is trying to say is empty;
  2. the same, followed by a second doc comment;
  3. a doc comment followed by `set_option ... in`, which is a command
     COMBINATOR, not a declaration.  The correct order is `set_option ... in`
     FIRST, then the docstring, then the declaration -- as seven sites on
     master already do.
So this check does not blacklist a few bad followers; it WHITELISTS the
declaration starters and modifiers, and flags everything else.

THE FAMILY'S GENERAL RULE, stated after the seventh instance (SV, 2026-08-24,
a doc comment attached to a `#guard`):

    `/--` binds to the next DECLARATION; `/-!` stands alone;
    `#guard` / `#eval` / `#print` / `#check` are COMMANDS, not declarations.

A command is not a declaration, so a doc comment cannot attach to one -- and
the scanner could not see this case at all, because its token reader accepted
only `[A-Za-z0-9_]` and a `#` therefore read as the EMPTY token, which is in
no blacklist.  The clause the gate lacks is exactly the incident it will not
catch.

`#guard_msgs` IS LEGAL AND IS 42 SITES ON MASTER: it takes `in` and attaches
to what follows, so a docstring before it is fine.  `#guard` is a PREFIX of
`#guard_msgs`, so this must match WHOLE TOKENS -- a prefix test would report
all 42 legal sites and red-light the tree.  (Measured, both numbers, before
the rule was added.)

CHECK 2 -- UNBALANCED BLOCK COMMENT.  Lean block comments NEST.  A comment
that mentions comment delimiters -- an opener quoted as an example, even
inside backticks -- raises the nesting depth and never lowers it, so the
comment swallows the rest of the file.  The fix for check 1 introduced exactly
this and was caught by a depth count before it reached the queue.

BOTH SCANNERS SKIP STRING LITERALS, and that is not incidental.  Go and
SystemVerilog both have a `--` operator, and both tiers name it inside error
strings, which reads to a naive scanner as a doc-comment opener.  A first draft
reported `LeanModels/Go/Stmt.lean` and `LeanModels/Sv/Param.lean` as defective
when both were clean -- so the two tiers most likely to trip this check are the
two whose languages contain the token.

Usage: python3 harness/lean_comment_forms.py [root | --self-test]
Exit: 0 clean, 1 defect found, 3 instrument error.
"""

from __future__ import annotations

import pathlib
import sys

# A doc comment opens `declModifiers`, and the parser then requires something
# it can attach to.  A WHITELIST of "declarations" is UNSOUND here and the tree
# says so: docstrings legally attach to STRUCTURE FIELDS (`val : Int`),
# INDUCTIVE CONSTRUCTORS (`| nil ...`), and `#guard_msgs in` expected-output
# blocks -- none of which are declarations.  A first draft whitelisted
# declaration keywords and accused 60+ known-green sites.
#
# So this is a BLACKLIST of followers that can NEVER be attached to: commands
# that open their own syntactic scope, and comment/EOF.  It is sound (no false
# positives) and it catches all three defects this lane actually shipped.
ILLEGAL_FOLLOWERS = (
    "set_option",   # a command COMBINATOR -- must come BEFORE the docstring
    "open", "namespace", "section", "end", "import", "variable", "universe",
    # COMMANDS, not declarations.  Whole-token matching keeps `#guard_msgs`
    # (42 legal sites) out of `#guard`'s reach.
    "#guard", "#eval", "#print", "#check",
)

def _skip_string(text: str, i: int) -> int:
    """Advance past a string literal starting at `text[i] == '\"'`."""
    i += 1
    n = len(text)
    while i < n:
        if text[i] == "\\":
            i += 2
            continue
        if text[i] == '"':
            return i + 1
        i += 1
    return i


def scan_file(text: str) -> tuple[list[tuple[int, str]], int, list[int]]:
    """Return (orphan doc comments, final nesting depth, unclosed opener lines)."""
    orphans: list[tuple[int, str]] = []
    opens: list[int] = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if depth == 0 and text[i] == '"':
            i = _skip_string(text, i)
            continue
        if text.startswith("/-", i):
            is_doc = text.startswith("/--", i) and not text.startswith("/---", i)
            start_line = text.count("\n", 0, i) + 1
            block_depth = 0
            j = i
            while j < n:
                if text.startswith("/-", j):
                    block_depth += 1
                    j += 2
                elif text.startswith("-/", j):
                    block_depth -= 1
                    j += 2
                    if block_depth == 0:
                        break
                else:
                    j += 1
            if block_depth != 0:
                opens.append(start_line)
                depth = block_depth
                break
            if is_doc:
                k = j
                while k < n and text[k] in " \t\r\n":
                    k += 1
                rest = text[k : k + 60]
                m = k
                # A LEADING `#` IS PART OF THE TOKEN.  Without this the reader
                # stopped dead on `#`, produced the empty string, and every
                # command follower was invisible to the blacklist.  Only `#`
                # is added: `|` (inductive constructor), `@[...]` (attribute)
                # and `(` still read as the empty token and stay legal.
                if m < n and text[m] == "#":
                    m += 1
                while m < n and (text[m].isalnum() or text[m] == "_"):
                    m += 1
                token = text[k:m]
                dangling = (
                    k >= n                       # end of file
                    or rest.startswith("/-")     # another comment
                    or token in ILLEGAL_FOLLOWERS
                )
                if dangling:
                    orphans.append((start_line, rest.split("\n")[0] or "<end of file>"))
            i = j
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
            continue
        i += 1
    return orphans, depth, opens


# THE REGRESSION SET EXTENDS, IT DOES NOT REPLACE.  Every shape the tree
# already relies on stays here beside the new one, because a rule added to a
# scanner is only as safe as the legal shapes it was checked against -- and
# `#guard_msgs` alone is 42 sites.
_CASES: list[tuple[str, str, int]] = [
    # -- the new clause: a command in a declaration slot (SV, seventh instance)
    ("doc + #guard is a defect",        '/-- d -/\n#guard 1 = 1\n', 1),
    ("doc + #eval is a defect",         '/-- d -/\n#eval 1\n', 1),
    ("doc + #print is a defect",        '/-- d -/\n#print axioms f\n', 1),
    ("doc + #check is a defect",        '/-- d -/\n#check f\n', 1),
    # -- and the prefix it must NOT reach
    ("doc + #guard_msgs is LEGAL",      '/-- d -/\n#guard_msgs in\ndef f := 1\n', 0),
    # -- the shapes the tree already relies on
    ("doc + def is legal",              '/-- d -/\ndef f := 1\n', 0),
    ("doc + theorem is legal",          '/-- d -/\ntheorem t : True := trivial\n', 0),
    ("doc + structure field is legal",  '/-- d -/\n  val : Int\n', 0),
    ("doc + constructor is legal",      '/-- d -/\n  | nil : L\n', 0),
    ("doc + attribute is legal",        '/-- d -/\n@[simp] theorem t : True := trivial\n', 0),
    ("/-! stands alone",                '/-! a module comment -/\n#guard 1 = 1\n', 0),
    # -- the followers that were already illegal
    ("doc + set_option is a defect",    '/-- d -/\nset_option x true in\ndef f := 1\n', 1),
    ("doc + open is a defect",          '/-- d -/\nopen Nat\n', 1),
    ("doc + namespace is a defect",     '/-- d -/\nnamespace N\n', 1),
    ("doc at end of file is a defect",  '/-- d -/\n', 1),
    # ONE orphan, not two: the FIRST comment dangles, the second attaches to
    # `def`.  The expectation was written as 2 and the scanner corrected it.
    ("doc + another comment is a defect", '/-- d -/\n/-- e -/\ndef f := 1\n', 1),
    # -- the string-literal control: Go and SV name `--` inside error strings
    ("`--` in a string is not a comment", 'def f := "a -- b"\n/-- d -/\ndef g := 1\n', 0),
    ("a quoted `/--` does not open one",  'def f := "/-- not a doc -/"\ndef g := 1\n', 0),
]


def self_test() -> int:
    ok = bad = 0
    for name, text, want in _CASES:
        orphans, depth, _opens = scan_file(text)
        got = len(orphans)
        if got == want and depth == 0:
            ok += 1
            print(f"  ok   {name}")
        else:
            bad += 1
            print(f"  FAIL {name}: got {got} orphan(s) depth {depth}, want {want} depth 0")
    print(f"self-test: {ok} ok, {bad} failed")
    return 1 if bad else 0


def main() -> int:
    if len(sys.argv) > 1 and sys.argv[1] == "--self-test":
        return self_test()
    root = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else ".")
    if not root.is_dir():
        print(f"lean_comment_forms: no such directory: {root}", file=sys.stderr)
        return 3
    files = [f for f in sorted(root.rglob("*.lean")) if ".lake" not in f.parts]
    if not files:
        print(f"lean_comment_forms: no .lean files under {root}", file=sys.stderr)
        return 3
    defects = 0
    for path in files:
        try:
            text = path.read_text(encoding="utf-8")
        except OSError as error:
            print(f"lean_comment_forms: cannot read {path}: {error}", file=sys.stderr)
            return 3
        orphans, depth, opens = scan_file(text)
        shown = path.relative_to(root)
        for line, rest in orphans:
            defects += 1
            print(f"ORPHAN DOC COMMENT {shown}:{line} -- followed by {rest[:40]!r}, "
                  f"not a declaration")
        if depth != 0:
            defects += 1
            print(f"UNBALANCED BLOCK COMMENT {shown}:{opens[0] if opens else '?'} -- "
                  f"opener never closed; it swallows the rest of the file")
    print(f"lean_comment_forms: {len(files)} .lean files, {defects} defect(s)")
    return 1 if defects else 0


if __name__ == "__main__":
    raise SystemExit(main())
