#!/usr/bin/env python3
"""docs_check.py — assert that doc-embedded code blocks match the tree.

Run from anywhere: python3 tools/docs_check.py
Scans README.md, AGENTS.md, and docs/**/*.md. Exit 0 when every checked
block matches; exit 1 listing every drifted or broken block. Python >= 3.9,
stdlib only.

THE MARKER CONVENTION (normative for doc writers)
-------------------------------------------------
A fenced code block is checked against the tree iff it carries a path
marker, in one of two forms:

1. First-line comment marker (the house style, used by the tutorials,
   how-tos, reference, and AGENTS.md): the block's FIRST line is a comment
   whose first token is a repo-root-relative path, optionally followed by a
   free-form (conventionally parenthesized) annotation:

       # Examples/tut_01/tut_01.py
       -- Examples/tri/spec.lean (excerpt)
       -- Examples/sum_to/sum_to.py (lean block; builds via Examples/sum_to/SumTo.lean)

   `#` markers for hash-comment blocks (python), `--` markers for Lean
   blocks. The marker line itself is doc-only and excluded from matching.

2. Preceding HTML comment, for languages without comment syntax (JSON):
   the line immediately before the opening fence is

       <!-- docs-check: harness/cases.json -->

   and the whole block body is matched.

EXEMPT blocks — deliberately not in the tree — have a first-line comment
beginning `(illustrative` (e.g. `-- (illustrative — broken)`), or the word
"illustrative" in the marker annotation. They are skipped and counted.

UNMARKED blocks (command transcripts, quoted error output, goal states,
normative design sketches in DESIGN.md / spec-surface.md gallery) are not
checked. Any block a reader is meant to type should be marked.

MATCHING RULE
-------------
Every non-marker line of the block must appear, IN ORDER, among the target
file's lines (a subsequence match, so annotated excerpts with elided
docstrings still pin every quoted line). Comparison is exact after
stripping trailing whitespace. Lines that are exactly `...` or `…` are
elision markers and are skipped. When the target is a `.py` file, a line
additionally matches its `# lean[`-block form: `# <line>` (`#` for an
empty line) — so Lean blocks quoted unprefixed check against the prefixed
source. A marker whose path does not exist is an error.

This is the doc third of the full check triad:
    lake build && python3 tools/docs_check.py && python3 harness/diff_test.py
"""

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# A first-line comment token is treated as a path marker when it looks like
# a repo path: contains a slash, or ends in a source-file extension.
PATH_EXTS = (".py", ".lean", ".json", ".md", ".sv", ".toml")
HTML_MARKER_RE = re.compile(r"<!--\s*docs-check:\s*(\S+)\s*-->")
ELISION_LINES = {"...", "…"}


def looks_like_path(token):
    if "/" in token:
        return True
    return token.endswith(PATH_EXTS)


def doc_files(paths):
    if paths:
        return [Path(p).resolve() for p in paths]
    files = [REPO / "README.md", REPO / "AGENTS.md"]
    files += sorted((REPO / "docs").rglob("*.md"))
    return [f for f in files if f.is_file()]


class Block(object):
    def __init__(self, doc, fence_line, lang, body, preceding):
        self.doc = doc            # Path of the markdown file
        self.fence_line = fence_line  # 1-based line of the opening fence
        self.lang = lang
        self.body = body          # list of content lines (fence indent stripped)
        self.preceding = preceding  # the line just before the fence, or ""


def parse_blocks(doc):
    lines = doc.read_text(encoding="utf-8").split("\n")
    blocks = []
    in_block = False
    indent = ""
    lang = ""
    body = []
    fence_line = 0
    preceding = ""
    for i, raw in enumerate(lines):
        stripped = raw.strip()
        if not in_block:
            if stripped.startswith("```"):
                in_block = True
                indent = raw[: len(raw) - len(raw.lstrip())]
                lang = stripped[3:].strip()
                body = []
                fence_line = i + 1
                preceding = lines[i - 1] if i > 0 else ""
        else:
            if stripped == "```":
                in_block = False
                blocks.append(Block(doc, fence_line, lang, body, preceding))
            else:
                content = raw
                if indent and content.startswith(indent):
                    content = content[len(indent):]
                body.append(content)
    return blocks


def classify(block):
    """Return ("checked", path, content) | ("illustrative",) | ("unmarked",)
    | ("broken", message)."""
    m = HTML_MARKER_RE.search(block.preceding or "")
    if m:
        path = m.group(1)
        target = REPO / path
        if not target.is_file():
            return ("broken", "marker path does not exist: %s" % path)
        return ("checked", path, list(block.body))

    if not block.body:
        return ("unmarked",)
    first = block.body[0].strip()
    rest = None
    for leader in ("-- ", "# "):
        if first.startswith(leader):
            rest = first[len(leader):].strip()
            break
    if rest is None:
        return ("unmarked",)
    if rest.startswith("(illustrative"):
        return ("illustrative",)
    token = rest.split()[0] if rest.split() else ""
    if not looks_like_path(token):
        return ("unmarked",)
    annotation = rest[len(token):]
    if "illustrative" in annotation:
        return ("illustrative",)
    target = REPO / token
    if not target.is_file():
        return ("broken", "marker path does not exist: %s" % token)
    return ("checked", token, list(block.body[1:]))


def line_matches(doc_line, file_line, target_is_py):
    if doc_line == file_line:
        return True
    if target_is_py:
        prefixed = ("# " + doc_line).rstrip() if doc_line else "#"
        if prefixed == file_line:
            return True
    return False


def check_block(path, content):
    """Subsequence-match content against the target file.
    Return None on success, else the first doc line that failed."""
    target = (REPO / path)
    file_lines = [l.rstrip() for l in
                  target.read_text(encoding="utf-8").split("\n")]
    is_py = path.endswith(".py")
    idx = 0
    for raw in content:
        doc_line = raw.rstrip()
        if doc_line.strip() in ELISION_LINES:
            continue
        while idx < len(file_lines) and not line_matches(doc_line,
                                                         file_lines[idx],
                                                         is_py):
            idx += 1
        if idx == len(file_lines):
            return doc_line
        idx += 1
    return None


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Check doc-embedded code blocks against the repo tree.")
    ap.add_argument("paths", nargs="*",
                    help="markdown files to check (default: README.md, "
                         "AGENTS.md, docs/**/*.md)")
    ap.add_argument("--list-unmarked", action="store_true",
                    help="also list blocks that carry no marker")
    args = ap.parse_args(argv)

    n_checked = n_ok = n_illustrative = n_unmarked = 0
    failures = []
    unmarked = []
    for doc in doc_files(args.paths):
        rel = doc.relative_to(REPO) if str(doc).startswith(str(REPO)) else doc
        for block in parse_blocks(doc):
            kind = classify(block)
            if kind[0] == "illustrative":
                n_illustrative += 1
            elif kind[0] == "unmarked":
                n_unmarked += 1
                unmarked.append("%s:%d (%s)" % (rel, block.fence_line,
                                                block.lang or "plain"))
            elif kind[0] == "broken":
                n_checked += 1
                failures.append("BROKEN %s:%d — %s"
                                % (rel, block.fence_line, kind[1]))
            else:
                n_checked += 1
                bad = check_block(kind[1], kind[2])
                if bad is None:
                    n_ok += 1
                else:
                    failures.append(
                        "DRIFT %s:%d -> %s\n  line not found in target "
                        "(in order): %r"
                        % (rel, block.fence_line, kind[1], bad))

    print("docs_check: %d marked blocks (%d ok), %d illustrative-exempt, "
          "%d unmarked (not checked)"
          % (n_checked, n_ok, n_illustrative, n_unmarked))
    if args.list_unmarked and unmarked:
        print("unmarked blocks:")
        for u in unmarked:
            print("  " + u)
    if failures:
        print("\n%d block(s) drifted or broken:" % len(failures))
        for f in failures:
            print(f)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
