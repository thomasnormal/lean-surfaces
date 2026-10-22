#!/usr/bin/env python3
"""Reprice files blocked solely by ``NetSymbol:Interconnect``.

An ``interconnect`` declaration describes a resolved connection whose net
type is supplied by the connected ports and nets.  This read-only companion
measures declaration, delay, diagnostic and array shapes while leaving
hierarchical connectivity and per-bit resolution outside the legacy
envelope.
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
WALL = "NetSymbol:Interconnect"


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


def _declaration_text(source, span):
    """Return the declaration containing an unsupported symbol span."""
    lines = source.splitlines()
    index = max(0, int(span.get("line", 1)) - 1)
    start = index
    while start > 0 and "interconnect" not in lines[start].lower():
        start -= 1
    end = index
    while end + 1 < len(lines) and ";" not in lines[end]:
        end += 1
    return " ".join(lines[start:end + 1])


def interconnect_features(declaration, source):
    """Return overlapping source-shape labels for one declaration."""
    raw_source = source
    declaration = _without_comments(declaration)
    source = _without_comments(source)
    labels = ["interconnect-declaration"]

    if re.search(r"\binterconnect\b[^;]*=", declaration, re.I):
        labels.append("declaration-assignment")
    if re.search(r"\binterconnect\b\s*#", declaration, re.I):
        labels.append("delay-specification")
    if re.search(r"#\s*\([^)]*,", declaration, re.I):
        labels.append("multiple-delay-values")
    if re.search(
            r"\binterconnect\s+(?:signed\s+)?"
            r"(?:logic|bit|reg|integer|time|byte|shortint|int|longint|"
            r"real|realtime|string)\b", declaration, re.I):
        labels.append("explicit-data-type")
    if re.search(
            r"\binterconnect\s*\(\s*"
            r"(?:supply|strong|pull|weak|highz|small|medium|large)\b",
            declaration, re.I):
        labels.append("drive-or-charge-strength")

    # A dimension before the first declarator name is packed; one after a
    # name is unpacked.  The patterns intentionally stay source-level: the
    # instrument does not elaborate ranges or infer a runtime array shape.
    if re.search(
            r"\binterconnect\b\s*(?:#\s*(?:\([^)]*\)|[^\s;]+)\s*)?"
            r"(?:\([^)]*\)\s*)?\[[^]]+\]\s*[A-Za-z_$][\w$]*",
            declaration, re.I):
        labels.append("packed-dimension")
    if ("explicit-data-type" not in labels and re.search(
            r"\binterconnect\b[^;]*\b[A-Za-z_$][\w$]*\s*\[[^]]+\]",
            declaration, re.I)):
        labels.append("unpacked-dimension")

    if re.search(r"different\s+bits|per[- ]bit|net\s+types", raw_source,
                 re.I):
        labels.append("per-bit-net-resolution")
    if re.search(r":type:\s*compile_error\b", raw_source, re.I):
        labels.append("compile-error-shape")
    return tuple(labels)


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\binterconnect\b", text, re.I):
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
    return "interconnect_only", [
        interconnect_features(
            _declaration_text(text, node.get("span", {})), text)
        for node in unsupported
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    interconnect_files = 0
    interconnect_instances = 0
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
        elif status == "interconnect_only":
            interconnect_files += 1
            interconnect_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "interconnect_only_files": interconnect_files,
        "interconnect_instances": interconnect_instances,
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
