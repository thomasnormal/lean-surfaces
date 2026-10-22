#!/usr/bin/env python3
"""Reprice files blocked solely by ``ConditionalStatement:Unique``.

Unique-if keeps the first true branch while checking every condition for a
uniqueness violation.  A no-match violation, deferred Observed-region report,
and flushing on a process reschedule all need state outside the ordinary
conditional envelope.  This read-only instrument reports those source shapes
without erasing the qualifier or choosing a branch.
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
WALL = "ConditionalStatement:Unique"


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
    """Remove comments before source-shape matching."""
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    return re.sub(r"//[^\n]*", " ", text)


def unique_if_features(statement, source, source_name=""):
    """Return overlapping labels recovered from one unique-if span."""
    text = _without_comments(statement.strip())
    whole = _without_comments(source)
    name = source_name.lower()
    labels = ["unique-if", "first-match"]

    # A chain has an ordinary first-match path, but all named conditions still
    # have to be observed for the uniqueness check.
    if re.search(r"\belse\s+if\b", text, re.I):
        labels.append("condition-chain")
    if (len(re.findall(r"[<>]", text)) >= 2
            or "||" in text
            or re.search(r"\b(?:multiple|more than one|both)\b[^\n;]*(?:true|match)",
                         whole, re.I)):
        labels.append("multiple-true")
    if re.search(r"\bno[- ]match|matches?\s+none|all[- ]false|no\s+condition\s+is\s+true",
                 whole, re.I):
        labels.append("no-match")
    # An explicit final else covers the no-match case.  `else if` alone is not
    # counted as an explicit fallback.
    final_else = r"\belse(?!\s+if\b)\s+(?:begin\b|[^;{}\n]+;)"
    if re.search(final_else, text, re.I):
        labels.append("explicit-else")
    if len(re.findall(r"\bunique\s+if\b", whole, re.I)) > 1:
        labels.append("nested-unique-if")
    if re.search(r"\balways_comb\b", whole, re.I):
        labels.append("always-comb-context")
    elif re.search(r"\balways\b", whole, re.I):
        labels.append("always-context")
    if re.search(r"\bfor\s*\(", whole, re.I):
        labels.append("loop-context")
    if re.search(r"\belse\s+unique(?:0|\s+if)?\b", whole, re.I):
        labels.append("invalid-after-else")
    # A chain without a final fallback has a distinct no-match violation.  The
    # invalid-after-else diagnostic is a parser boundary, not that runtime
    # condition, so keep the two labels separate.
    if ("invalid-after-else" not in labels
            and not re.search(final_else, text, re.I)):
        labels.append("no-match")
    # These reports are scheduler observations whose intent is encoded in the
    # corpus fixture name; no comment text is consulted.
    if "observed-region" in name or "deferred-to-observed" in name:
        labels.append("observed-region-report")
    if "flush-on-event-control-resume" in name:
        labels.append("flush-on-event-resume")
    if ("flushed-on-reschedule" in name or "glitch-immunity" in name):
        labels.append("flush-on-reschedule")
    return tuple(labels)


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\bunique\s+if\b", text, re.I):
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
    return "unique_if_only", [
        unique_if_features(node.get("text", ""), text, path.name)
        for node in unsupported
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    unique_files = 0
    unique_instances = 0
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
        elif status == "unique_if_only":
            unique_files += 1
            unique_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "unique_if_only_files": unique_files,
        "unique_if_instances": unique_instances,
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
