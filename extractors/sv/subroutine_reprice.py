#!/usr/bin/env python3
"""Reprice files blocked solely by ``SubroutineSymbol:Subroutine``.

This read-only companion to ``census.py`` runs the extractor in process, keeps
only files whose complete Unsupported set is the subroutine wall, and groups
the actual unsupported declaration text into functions, tasks and DPI
imports.  File counts overlap when a source has several declarations.
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


def subroutine_shape(text):
    """Classify one unsupported subroutine declaration without guessing use."""
    source = text.strip()
    lower = source.lower()
    if lower.startswith("import "):
        return "DPI import"
    if re.match(r"(?:automatic\s+|static\s+|pure\s+|context\s+)*task\b",
                lower):
        return "task declaration"
    if re.match(r"(?:automatic\s+|static\s+|pure\s+|context\s+)*function\b",
                lower):
        return "function declaration"
    if re.search(r"\btask\b", lower):
        return "task declaration"
    if re.search(r"\bfunction\b", lower):
        return "function declaration"
    return "other subroutine"


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
    if kinds != {"SubroutineSymbol:Subroutine"}:
        return "other", []
    return "subroutine_only", [subroutine_shape(node.get("text", ""))
                                for node in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    shapes = collections.Counter()
    files_by_shape = collections.defaultdict(set)
    subroutine_files = 0
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
        elif status == "subroutine_only":
            subroutine_files += 1
            instances += len(source_shapes)
            shapes.update(source_shapes)
            for shape in set(source_shapes):
                files_by_shape[shape].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "subroutine_only_files": subroutine_files,
        "subroutine_instances": instances,
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
