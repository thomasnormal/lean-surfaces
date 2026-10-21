#!/usr/bin/env python3
"""Reprice nonblocking intra-assignment publication/context refusals.

Blocking intra-assignment controls already use the retained continuation path.
This read-only companion measures the residual nonblocking forms, whose future
publication is a scheduler rule rather than a sleeping process shortcut.
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
WALL = "IntraAssignment:publication-or-context"


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def control_shape(text):
    """Classify the visible nonblocking timing spelling."""
    source = text.lower()
    if re.search(r"<=\s*#\s*0\b", source):
        return "nonblocking #0"
    if re.search(r"<=\s*#", source):
        return "nonblocking delay"
    if re.search(r"<=\s*@", source):
        return "nonblocking event"
    return "nonblocking repeat/context"


def one_file(path):
    """Return ``(status, control shapes)`` for one corpus source."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    tree = SyntaxTree.fromText(text, name=path.as_posix())
    compilation = Compilation()
    compilation.addSyntaxTree(tree)
    extract._SOURCE_BYTES = data
    envelope = extract.convert_design(tree.sourceManager, compilation)
    unsupported = [node for node in walk(envelope)
                   if node.get("kind") == "Unsupported"]
    kinds = {node.get("sv_kind") for node in unsupported}
    if kinds != {WALL}:
        return "other", []
    return "publication_only", [control_shape(node.get("text", ""))
                                 for node in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    publication_files = 0
    publication_instances = 0
    shapes = collections.Counter()
    shape_files = collections.defaultdict(set)
    skipped = 0
    errors = 0

    for path in files:
        try:
            status, source_shapes = one_file(path)
        except Exception as exc:  # keep the measurement loud and complete
            print(f"error: {path}: {exc}", file=sys.stderr)
            errors += 1
            continue
        if status == "skip_include":
            skipped += 1
        elif status == "publication_only":
            publication_files += 1
            publication_instances += len(source_shapes)
            for shape in source_shapes:
                shapes[shape] += 1
                shape_files[shape].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "publication_only_files": publication_files,
        "publication_instances": publication_instances,
        "include_skips": skipped,
        "errors": errors,
        "shapes": {
            shape: {"instances": shapes[shape],
                    "files": len(shape_files[shape])}
            for shape in sorted(shapes)
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
