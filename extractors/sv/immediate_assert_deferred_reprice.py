#!/usr/bin/env python3
"""Reprice files blocked solely by ``ImmediateAssertion:deferred``.

Deferred immediate assertions sample in a later scheduler region: ``#0``
reports in Observed and ``final`` reports at end of simulation.  This
read-only companion measures those source shapes while leaving the region,
re-evaluation and action-call contract loud.
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
WALL = "ImmediateAssertion:deferred"


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


def deferred_features(statement, source):
    """Return overlapping labels for one deferred assertion statement."""
    text = _without_comments(statement.strip())
    source = _without_comments(source)
    labels = ["deferred-assertion"]
    match = re.search(r"\b(assert|assume|cover)\b", text, re.I)
    if match:
        labels.append(match.group(1).lower())
    if re.search(r"\bfinal\b", text, re.I):
        labels.extend(("final", "postponed-region"))
    if re.search(r"#\s*0", text):
        labels.extend(("hash0", "observed-region"))
    if re.search(r"\b(?:assert|assume|cover)\b[^;]*\b(?:begin|end)\b",
                 text, re.I):
        labels.append("block-action")
    if re.search(r"\$[A-Za-z_$][\w$]*\s*\(", text):
        labels.append("single-system-call-action")
    if "else" not in text.lower() and re.search(r"\)\s*;\s*$", text):
        labels.append("null-action")
    if re.search(r"\balways_comb\b", source, re.I):
        labels.append("always-comb-context")
    elif re.search(r"\balways\b", source, re.I):
        labels.append("always-context")
    if re.search(r"\bfunction\b", source, re.I):
        labels.append("function-context")
    if re.search(r"\bpragma\s+protect\b", source, re.I):
        labels.append("protected-region")
    if not re.search(r"\balways(?:_comb)?\b|\binitial\b|\bfunction\b",
                     source, re.I):
        labels.append("static-module-context")
    return tuple(labels)


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\b(?:assert|assume|cover)\b", text, re.I):
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
    lines = text.splitlines()
    features = []
    for node in unsupported:
        span = node.get("span") or {}
        line = max(1, int(span.get("line", 1)))
        statement = lines[line - 1] if line <= len(lines) else node.get("text", "")
        features.append(deferred_features(statement, text))
    return "deferred_only", features


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    deferred_files = 0
    deferred_instances = 0
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
        elif status == "deferred_only":
            deferred_files += 1
            deferred_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "deferred_only_files": deferred_files,
        "deferred_instances": deferred_instances,
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
