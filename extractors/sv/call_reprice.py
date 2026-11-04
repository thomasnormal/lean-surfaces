#!/usr/bin/env python3
"""Reprice files blocked solely by ``ExpressionStatement:CallExpression``.

This is a read-only companion to ``census.py``.  It runs the extractor
in-process without writing envelopes beside corpus sources, keeps only files
whose complete Unsupported set is the call-statement wall, and groups the
unsupported statements by their leading call spelling.  File counts overlap
when a file contains several call spellings.
"""

import argparse
import collections
import json
import pathlib
import re
import sys

from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

REPO = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "extractors" / "sv"))
import extract  # noqa: E402

INCLUDE_RE = re.compile(r'^\s*`include\s*(?:["<`])', re.M)
CALL_HEAD_RE = re.compile(r'^(\$?[A-Za-z_][A-Za-z0-9_$]*)')


def walk(node):
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def call_shape(text):
    """Return a stable source-shape label for one unsupported call statement."""
    source = text.strip()
    if source.startswith("void'("):
        return "void-cast callable"
    if "." in source.split("(", 1)[0]:
        return "member method call"
    match = CALL_HEAD_RE.match(source)
    return match.group(1) if match else "unclassified call"


def one_file(path):
    data = path.read_bytes()
    if INCLUDE_RE.search(data.decode("utf-8", errors="replace")):
        return "skip_include", []
    text = data.decode("utf-8")
    tree = SyntaxTree.fromText(text, name=path.as_posix())
    comp = Compilation()
    comp.addSyntaxTree(tree)
    extract._SOURCE_BYTES = data
    envelope = extract.convert_design(tree.sourceManager, comp)
    unsupported = [node for node in walk(envelope)
                   if node.get("kind") == "Unsupported"]
    kinds = {node.get("sv_kind") for node in unsupported}
    if kinds == {"ExpressionStatement:CallExpression"}:
        return "call_only", [call_shape(node.get("text", ""))
                              for node in unsupported]
    return "other", []


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped SV corpus tests directory")
    args = parser.parse_args(argv)
    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    categories = collections.Counter()
    category_files = collections.defaultdict(set)
    call_files = 0
    call_instances = 0
    skipped = 0
    errors = 0
    for path in files:
        try:
            status, shapes = one_file(path)
        except Exception as exc:  # keep the measurement loud and complete
            print(f"error: {path}: {exc}", file=sys.stderr)
            errors += 1
            continue
        if status == "skip_include":
            skipped += 1
        elif status == "call_only":
            call_files += 1
            call_instances += len(shapes)
            categories.update(shapes)
            for shape in set(shapes):
                category_files[shape].add(path.as_posix())
    result = {
        "corpus_files": len(files),
        "call_only_files": call_files,
        "call_instances": call_instances,
        "include_skips": skipped,
        "errors": errors,
        "calls": {
            shape: {"instances": categories[shape],
                    "files": len(category_files[shape])}
            for shape in sorted(categories)
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
