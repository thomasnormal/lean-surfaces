#!/usr/bin/env python3
"""Reprice files blocked solely by ``ProceduralBlockSymbol:AlwaysLatch``.

``always_latch`` is an automatically activated process with inferred
sensitivity and latch-hold behavior.  This read-only instrument reports the
source shapes in the sole files; it never rewrites the process as an ordinary
``always`` or chooses a sensitivity list.
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
WALL = "ProceduralBlockSymbol:AlwaysLatch"


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def _without_comments(text):
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    return re.sub(r"//[^\n]*", " ", text)


def _latch_bodies(source):
    """Return rough source slices for each ``always_latch`` body.

    The repricer is telemetry, not a parser.  A block body is balanced by its
    ``begin``/``end`` tokens; a one-line body ends at its first semicolon.
    This is sufficient to distinguish an explicit event control in the latch
    body from event controls belonging to another process in the same file.
    """
    bodies = []
    for match in re.finditer(r"\balways_latch\b", source):
        tail = source[match.end():]
        start = len(tail) - len(tail.lstrip())
        tail = tail[start:]
        if re.match(r"begin\b", tail):
            depth = 0
            end = None
            for token in re.finditer(r"\bbegin\b|\bend\b", tail):
                if token.group() == "begin":
                    depth += 1
                else:
                    depth -= 1
                    if depth == 0:
                        end = token.end()
                        break
            bodies.append(tail[:end] if end is not None else tail)
        else:
            semi = tail.find(";")
            bodies.append(tail if semi < 0 else tail[:semi + 1])
    return bodies


def latch_features(text):
    """Return overlapping source-shape labels for one sole row."""
    source = _without_comments(text)
    labels = []
    bodies = _latch_bodies(source)
    if bodies and not any(re.search(r"@\s*\(", body) for body in bodies):
        labels.append("inferred-sensitivity")
    if "<=" in source:
        labels.append("nonblocking-assignment")
    if re.search(r"\bq1\b", source) and re.search(r"\bq2\b", source):
        labels.append("multiple-outputs")
    if re.search(r"\bif\s*\([^)]*\)\s*begin\s*if\s*\(", source,
                 re.S):
        labels.append("nested-enables")
    if any(re.search(r"\bfork\b", body) for body in bodies):
        labels.append("fork-forbidden-diagnostic")
    if any(re.search(r"@\s*\(", body) for body in bodies):
        labels.append("timing-control-diagnostic")
    if "`pragma protect" in source.lower():
        labels.append("protected-region")
    if re.search(r"\balways_comb\b|\balways_ff\b|\balways\s*#", source):
        labels.append("mixed-or-timed-processes")
    return tuple(dict.fromkeys(labels))


def one_file(path):
    """Return ``(status, feature tuples)`` for one source."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\balways_latch\b", text):
        return "other", []
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
    return "latch_only", [latch_features(text) for _ in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    latch_files = 0
    latch_instances = 0
    features = collections.Counter()
    feature_files = collections.defaultdict(set)
    skipped = 0
    errors = 0

    for path in files:
        try:
            status, feature_sets = one_file(path)
        except Exception as exc:  # keep the measurement loud and complete
            print(f"error: {path}: {exc}", file=sys.stderr)
            errors += 1
            continue
        if status == "skip_include":
            skipped += 1
        elif status == "latch_only":
            latch_files += 1
            latch_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "latch_only_files": latch_files,
        "latch_instances": latch_instances,
        "include_skips": skipped,
        "errors": errors,
        "features": {
            feature: {"instances": features[feature],
                      "files": len(feature_files[feature])}
            for feature in sorted(features)
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
