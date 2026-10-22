#!/usr/bin/env python3
"""Reprice files blocked solely by ``ContinuousAssignSymbol:delay``.

A delayed continuous assignment schedules its own driver output.  This
read-only instrument reports delay syntax and publication scenarios while
leaving the scheduler-facing delayed driver loud.
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
WALL = "ContinuousAssignSymbol:delay"


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


def continuous_assign_delay_features(text, context="", path=""):
    """Return overlapping source-shape labels for one delay span."""
    raw = context or ""
    source = _without_comments(raw)
    lower = raw.lower()
    labels = ["delayed-assign"]

    # Match delay controls on the assign statement itself, avoiding # delays
    # in initial procedural statements.
    assign_lines = re.findall(r"\bassign\b[^;\n]*", source, flags=re.I)
    specs = re.findall(r"#\s*\(([^)]*)\)", "\n".join(assign_lines))
    if any(spec.count(",") >= 1 for spec in specs):
        labels.append("rise-fall")
    if any(spec.count(",") >= 2 for spec in specs):
        labels.append("three-delays")
    if any(spec.count(":") >= 2 for spec in specs):
        labels.append("min-typ-max")

    if re.search(r"inertial|cancel|deschedul|reschedul|pending event",
                 lower):
        labels.append("inertial")
    if re.search(r"\b4'hz\b|\b[0-9]+'[bodh]z\b|turn.?off delay",
                 lower):
        labels.append("z-transition")
    if re.search(r"\b(?:wire|logic|reg)\s*\[[^\]]+\]", source,
                 flags=re.I):
        labels.append("vector")
    if re.search(r"initial[- ]x|default x|initial state.*x|still x",
                 lower):
        labels.append("initial-x")
    if re.search(r"strength|strong[01]", lower):
        labels.append("strength-before-delay")
    if "/chapter-37/" in path.replace("\\", "/"):
        labels.append("type-example")
    return tuple(dict.fromkeys(labels))


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\bassign\b[^;\n]*#", text, re.I):
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
    return "continuous_assign_delay_only", [
        continuous_assign_delay_features(node.get("text", ""), text,
                                         path.as_posix())
        for node in unsupported
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    delay_files = 0
    delay_instances = 0
    features = collections.Counter()
    feature_files = collections.defaultdict(set)
    skipped = 0
    errors = 0

    for path in files:
        try:
            status, feature_sets = one_file(path)
        except Exception as exc:
            print(f"error: {path}: {exc}", file=sys.stderr)
            errors += 1
            continue
        if status == "skip_include":
            skipped += 1
        elif status == "continuous_assign_delay_only":
            delay_files += 1
            delay_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "continuous_assign_delay_only_files": delay_files,
        "continuous_assign_delay_instances": delay_instances,
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
