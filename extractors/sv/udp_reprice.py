#!/usr/bin/env python3
"""Reprice files blocked solely by ``PrimitiveSymbol`` (UDP declarations).

User-defined primitives have declaration, state-table and diagnostic rules
that are separate from built-in primitive instances.  This read-only
instrument reports the rejected table shapes without constructing a UDP
truth-table evaluator or a continuous driver.
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
WALL = "PrimitiveSymbol"


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


def udp_features(text):
    """Return overlapping table/declaration shapes for one rejected UDP."""
    source = _without_comments(text)
    labels = []
    outputs = re.findall(r"\boutput\b", source, re.I)
    if len(outputs) > 1 or re.search(r"\binout\b", source, re.I) \
            or re.search(r"\binput\s*\[", source, re.I):
        labels.append("port-shape-diagnostic")
    if (not re.search(r"\boutput\s+\w+\s*;\s*reg\b", source, re.I)
            and re.search(r"\btable\b[\s\S]*:\s*\?\s*:", source,
                          re.I)):
        labels.append("combinational-current-state-field")
    if re.search(r"^\s*x\s+x\s*:[^\n;]*\b[01]\b", source,
                 re.I | re.M):
        labels.append("all-x-input-non-x-output")
    if re.search(r"^\s*r\s+1\s*:[^\n]*\n\s*r\s+1\s*:", source,
                 re.I | re.M):
        labels.append("duplicate-input-different-output")
    if re.search(r"\([01]+\)\s*\([01]+\)", source):
        labels.append("multiple-transitions")
    if re.search(r"^\s*\([01]{2,}\)\s*:\s*\?\s*:", source,
                 re.M):
        labels.append("missing-input-field")
    if re.search(r"^\s*z\s*:", source, re.I | re.M):
        labels.append("z-table-symbol")
    if re.search(r"\binitial\s+\w+\s*=\s*1'bz\b", source, re.I):
        labels.append("invalid-init-value")
    return tuple(dict.fromkeys(labels))


def one_file(path):
    """Return ``(status, feature tuples)`` for one source."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\bprimitive\b", text, re.I):
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
    return "udp_only", [udp_features(text) for _ in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    udp_files = 0
    udp_instances = 0
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
        elif status == "udp_only":
            udp_files += 1
            udp_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "udp_only_files": udp_files,
        "udp_instances": udp_instances,
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
