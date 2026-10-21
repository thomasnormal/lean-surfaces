#!/usr/bin/env python3
"""Reprice files blocked solely by ``ClassType:ClassType``.

``ClassType:ClassType`` is the envelope's marker for a class declared inside
 a module (the top-level declaration marker is ``ClassType``).  This
 read-only instrument keeps the exact sole-wall census and reports only
 source-span shapes.  It does not lower a class, resolve an object handle, or
 infer method, randomization, or coverage semantics.
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
WALL = "ClassType:ClassType"


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def class_header_shape(text):
    """Classify the visible header of one nested class span."""
    source = text.strip().lower()
    if re.search(r"\binterface\s+class\b", source):
        return "interface class"
    if re.search(r"\bvirtual\s+class\b", source):
        return "virtual class"
    if re.search(r"\bclass\s+[^;{}]+\bextends\b", source):
        return "class extends"
    if re.search(r"\bclass\b", source):
        return "class"
    return "other class span"


def class_features(text):
    """Return overlapping source-feature labels for one class span."""
    source = text.lower()
    patterns = (
        ("methods", r"\b(?:function|task)\b"),
        ("constraints", r"\bconstraint\b"),
        ("random-fields", r"\brandc?\b"),
        ("virtual-interface", r"\b(?:virtual|interface)\b"),
        ("extends", r"\bextends\b"),
        ("covergroups", r"\bcovergroup\b"),
    )
    return tuple(label for label, pattern in patterns
                 if re.search(pattern, source))


def one_file(path):
    """Return ``(status, class spans)`` for one corpus source."""
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
    if kinds != {WALL}:
        return "other", []
    spans = []
    for node in unsupported:
        source = node.get("text", "")
        spans.append({"header": class_header_shape(source),
                      "features": class_features(source)})
    return "class_use_only", spans


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    class_files = 0
    class_instances = 0
    headers = collections.Counter()
    header_files = collections.defaultdict(set)
    features = collections.Counter()
    feature_files = collections.defaultdict(set)
    skipped = 0
    errors = 0

    for path in files:
        try:
            status, spans = one_file(path)
        except Exception as exc:  # keep the measurement loud and complete
            print(f"error: {path}: {exc}", file=sys.stderr)
            errors += 1
            continue
        if status == "skip_include":
            skipped += 1
        elif status == "class_use_only":
            class_files += 1
            class_instances += len(spans)
            for span in spans:
                header = span["header"]
                headers[header] += 1
                header_files[header].add(path.as_posix())
                for feature in span["features"]:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "class_use_only_files": class_files,
        "class_use_instances": class_instances,
        "include_skips": skipped,
        "errors": errors,
        "headers": {
            key: {"instances": headers[key],
                  "files": len(header_files[key])}
            for key in sorted(headers)
        },
        "features": {
            key: {"instances": features[key],
                  "files": len(feature_files[key])}
            for key in sorted(features)
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
