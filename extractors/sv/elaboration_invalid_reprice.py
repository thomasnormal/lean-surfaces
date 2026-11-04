#!/usr/bin/env python3
"""Reprice files blocked solely by ``Elaboration:invalid-compilation``.

The marker is a design-level diagnostic boundary.  The read-only instrument
reports the elaboration shapes that caused the frontend to reject a lowered
generate/parameter design; it never salvages the elaborated prefix or changes
the generated scope.
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
WALL = "Elaboration:invalid-compilation"


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


def elaboration_features(text):
    """Return overlapping source-shape labels for one rejected design.

    The labels describe the IEEE rule being exercised, rather than a slang
    diagnostic spelling.  They are deliberately lexical: the instrument is
    telemetry over source files and does not try to re-elaborate a rejected
    design.
    """
    source = _without_comments(text)
    lower = source.lower()
    labels = []

    # The generated-scope name rule applies even to inactive and zero-entry
    # constructs.  The corpus metadata records these as redefinition errors.
    if re.search(r"^\s*:diagnostic_match:\s*redefinition\b", text,
                 re.I | re.M):
        labels.append("generate-scope-name-conflict")

    # A mismatched optional end label is a distinct §9.3.4 diagnostic.
    if re.search(r"\bend\s*:\s*\w+", lower) and re.search(
            r"\bbegin\s*:\s*\w+", lower):
        labels.append("generate-end-label-mismatch")

    # Conditional compilation is elaboration input, but is not a generate
    # scope.  Keep it visible as its own diagnostic shape.
    if re.search(r"`ifndef\s*\(", lower):
        labels.append("macro-conditional-expression")

    # A genvar is only legal in a loop-generate scheme.  These two fixtures
    # use it in a case/if generate expression instead.
    if re.search(r"\bgenvar\s+\w+", lower) and (
            re.search(r"\bcase\s*\(\s*\w+", lower)
            or re.search(r"\bif\s*\(\s*\w+\s*(?:==|!=|\))", lower)):
        labels.append("genvar-outside-loop-scheme")

    # Port declarations are not members of a generate block.
    if re.search(r"\binput\s+(?:logic|wire|reg|bit|[a-zA-Z_]\w*)", lower):
        labels.append("generate-port-declaration")

    generate_count = len(re.findall(r"\bgenerate\b", lower))
    endgenerate_count = len(re.findall(r"\bendgenerate\b", lower))
    if generate_count >= 2:
        labels.append("nested-generate-region")
    elif generate_count and endgenerate_count == 0:
        labels.append("generate-region-delimiter")

    # Generate schemes require a constant expression; the two rows use a
    # runtime signal in the condition (one with an explicit generate region,
    # one with the implicit form).
    if re.search(r"non[- ]constant|runtime_var|\bdyn\b", lower):
        labels.append("nonconstant-generate-scheme")

    if not labels:
        labels.append("other-elaboration-diagnostic")
    return tuple(dict.fromkeys(labels))


def one_file(path):
    """Return ``(status, feature tuples)`` for one source."""
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
    return "invalid_only", [elaboration_features(text) for _ in unsupported]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    invalid_files = 0
    invalid_instances = 0
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
        elif status == "invalid_only":
            invalid_files += 1
            invalid_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "invalid_only_files": invalid_files,
        "invalid_instances": invalid_instances,
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
