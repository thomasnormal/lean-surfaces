#!/usr/bin/env python3
"""Reprice files blocked solely by a ``fork ... join*`` block.

Fork/join is a process-control boundary.  This read-only instrument groups the
three frontend markers by IEEE join flavor while preserving their scheduler
meaning; it never lowers a fork into a sequential block.
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
JOIN_KINDS = {
    "BlockStatement:JoinAll",
    "BlockStatement:JoinAny",
    "BlockStatement:JoinNone",
}


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def join_flavor(sv_kind, text=""):
    """Map a frontend marker (or a fallback source span) to a join flavor."""
    exact = {
        "BlockStatement:JoinAll": "join",
        "BlockStatement:JoinAny": "join_any",
        "BlockStatement:JoinNone": "join_none",
    }
    if sv_kind in exact:
        return exact[sv_kind]
    source = text.lower()
    if re.search(r"\bjoin_none\b", source):
        return "join_none"
    if re.search(r"\bjoin_any\b", source):
        return "join_any"
    if re.search(r"\bjoin\b", source):
        return "join"
    return "other fork/join"


def one_file(path):
    """Return ``(status, join flavors)`` for one corpus source."""
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
    if not kinds or not kinds <= JOIN_KINDS:
        return "other", []
    return "join_only", [join_flavor(node.get("sv_kind"), node.get("text", ""))
                          for node in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    join_files = 0
    join_instances = 0
    flavors = collections.Counter()
    flavor_files = collections.defaultdict(set)
    skipped = 0
    errors = 0

    for path in files:
        try:
            status, source_flavors = one_file(path)
        except Exception as exc:  # keep the measurement loud and complete
            print(f"error: {path}: {exc}", file=sys.stderr)
            errors += 1
            continue
        if status == "skip_include":
            skipped += 1
        elif status == "join_only":
            join_files += 1
            join_instances += len(source_flavors)
            for flavor in source_flavors:
                flavors[flavor] += 1
                flavor_files[flavor].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "join_only_files": join_files,
        "join_instances": join_instances,
        "include_skips": skipped,
        "errors": errors,
        "flavors": {
            flavor: {"instances": flavors[flavor],
                     "files": len(flavor_files[flavor])}
            for flavor in sorted(flavors)
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
