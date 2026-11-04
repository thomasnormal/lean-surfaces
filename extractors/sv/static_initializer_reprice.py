#!/usr/bin/env python3
"""Reprice files blocked solely by ``StaticLocal:initializer``.

The procedural-lifetime tier already admits closed pure static initializers.
This read-only companion measures the remaining runtime-dependent, effectful
and elaboration-sensitive shapes without evaluating an initializer or choosing
an initialization order.
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
WALL = "StaticLocal:initializer"


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


def _initializer_text(source, span):
    """Return the source line or declaration containing an unsupported span."""
    lines = source.splitlines()
    index = max(0, int(span.get("line", 1)) - 1)
    start = index
    while start > 0 and "=" not in lines[start] and ";" not in lines[start]:
        start -= 1
    end = index
    while end + 1 < len(lines) and ";" not in lines[end]:
        end += 1
    return " ".join(lines[start:end + 1])


def static_initializer_features(initializer, source):
    """Return overlapping source-shape labels for one static initializer."""
    raw_source = source
    initializer = _without_comments(initializer)
    source = _without_comments(source)
    labels = ["static-initializer"]

    if re.search(r"\$urandom(?:_range)?\b|std::randomize\b", initializer,
                 re.I):
        labels.append("random-or-randomize")
    if re.search(r"\$[A-Za-z_$][\w$]*\b", initializer):
        labels.append("system-function")
    if re.search(r"`[A-Za-z_$][\w$]*", raw_source):
        labels.append("macro-expansion")
    if re.search(r"\b(?:import|export)\b|\b\w+::\w+\b", raw_source,
                 re.I):
        labels.append("package-or-qualified-read")
    if re.search(r"\b(?:shortint|int|longint|byte|integer|time|bit|logic)\s*'",
                 initializer, re.I) or re.search(
                     r"\$cast\s*\(|\b[A-Za-z_$][\w$]*\s*'\s*\(",
                     initializer):
        labels.append("type-or-size-cast")
    if re.search(r"\b(?:real|realtime)\b|\d+\.\d+", initializer, re.I):
        labels.append("real-conversion")
    if re.search(r"<<<|>>>|(?<!<)<<(?!=)|(?<!>)>>(?!>)", initializer):
        labels.append("shift-expression")
    if re.search(r"\*\*", initializer):
        labels.append("power-expression")
    if re.search(r"(?<![&])&(?![&])|(?<![|])\|(?![|])", initializer):
        labels.append("bitwise-expression")
    if "?" in initializer:
        labels.append("conditional-expression")
    if re.search(r"\b(?:T|b_t|s_t)\s*'\s*\{", initializer):
        labels.append("aggregate-assignment-pattern")
    if re.search(r"\b[a-zA-Z_$][\w$]*\b", initializer):
        # This is intentionally a source-shape observation, not a name
        # resolver.  The envelope's closed-initializer test cannot admit such
        # reads when they depend on procedural or package storage.
        labels.append("nonliteral-source")
    if re.search(r"\b(?:x|value|a|b|n|v|s|l|c|clk|word_t)\b", initializer):
        labels.append("runtime-dependent-read")
    return tuple(labels)


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\bStaticLocal\b|static\s+local", text, re.I):
        # The marker is produced by elaboration, so source prefiltering is
        # necessarily approximate; this branch only avoids most frontend
        # work and the envelope remains authoritative below.
        if not re.search(r"\b(?:initial|always|begin)\b", text, re.I):
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
    return "static_initializer_only", [
        static_initializer_features(
            _initializer_text(text, node.get("span", {})), text)
        for node in unsupported
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    static_files = 0
    static_instances = 0
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
        elif status == "static_initializer_only":
            static_files += 1
            static_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "static_initializer_only_files": static_files,
        "static_initializer_instances": static_instances,
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
