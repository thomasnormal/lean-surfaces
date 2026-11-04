#!/usr/bin/env python3
"""Reprice files blocked solely by ``InvalidStatement``.

``InvalidStatement`` is a frontend recovery marker, not one IEEE statement
family.  This read-only companion to ``census.py`` runs extraction in process,
keeps only files whose complete Unsupported set is that marker, and reports
the stable source-span shapes that the frontend exposed.  It never treats a
recovered block as executable code.
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


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def invalid_shape(text):
    """Classify a recovery span without claiming that its text is valid."""
    source = text.strip()
    if not source:
        return "empty frontend span"
    if source.startswith("begin"):
        return "bad begin/block recovery"
    if source.startswith("$my_vpi_task"):
        return "VPI system-task token"
    return "other bad statement"


def one_file(path):
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
    if kinds != {"InvalidStatement"}:
        return "other", []
    return "invalid_only", [invalid_shape(node.get("text", ""))
                             for node in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    shapes = collections.Counter()
    files_by_shape = collections.defaultdict(set)
    invalid_files = 0
    instances = 0
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
        elif status == "invalid_only":
            invalid_files += 1
            instances += len(source_shapes)
            shapes.update(source_shapes)
            for shape in set(source_shapes):
                files_by_shape[shape].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "invalid_only_files": invalid_files,
        "invalid_instances": instances,
        "include_skips": skipped,
        "errors": errors,
        "shapes": {
            shape: {"instances": shapes[shape],
                    "files": len(files_by_shape[shape])}
            for shape in sorted(shapes)
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
