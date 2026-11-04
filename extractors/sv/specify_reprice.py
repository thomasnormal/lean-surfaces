#!/usr/bin/env python3
"""Reprice files blocked solely by ``SpecifyBlockSymbol:SpecifyBlock``.

Specify blocks describe module path delays and timing checks.  This read-only
instrument reports the source shapes while leaving path propagation, timing
monitoring and notifier scheduling loud.
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
WALL = "SpecifyBlockSymbol:SpecifyBlock"


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
    """Remove comments before classifying the retained specify span."""
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    return re.sub(r"//[^\n]*", " ", text)


def specify_features(text):
    """Return overlapping IEEE specify-shape labels for one span."""
    source = _without_comments(text).lower()
    patterns = (
        ("module-path", r"=>|\*>") ,
        ("timing-check", r"\$(?:setup|hold|setuphold|recovery|removal|recrem|skew|timeskew|fullskew|period|width|nochange)\b"),
        ("edge-sensitive", r"\b(?:posedge|negedge|edge)\b"),
        ("conditional-path", r"\bif\s*\("),
        ("ifnone", r"\bifnone\b"),
        ("polarity", r"[+-]:\s*"),
        ("state-dependent", r"\([^;\n]*:\s*[^;\n]*\)"),
        ("tuple-delay", r"=\s*\([^;\n,]+\s*,\s*[^;\n]+\)"),
        ("scalar-delay", r"(?<![>])=(?!>|\s*\()[^;\n]+;"),
        ("notifier", r"\bnotifier\b"),
        ("select", r"\[[^\]]+\]"),
        ("invalid-assertion", r"\bassert\s+property\b"),
        ("invalid-system-task", r"\$(?:display|finish|fatal)\b"),
        ("illegal-edge-spec", r"\bedge\[[^\]]+\]"),
    )
    return tuple(label for label, pattern in patterns
                 if re.search(pattern, source))


def one_file(path):
    """Return ``(status, specify feature tuples)`` for one source."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\bspecify\b", text, re.I):
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
    return "specify_only", [specify_features(node.get("text", ""))
                             for node in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    specify_files = 0
    specify_instances = 0
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
        elif status == "specify_only":
            specify_files += 1
            specify_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "specify_only_files": specify_files,
        "specify_instances": specify_instances,
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
