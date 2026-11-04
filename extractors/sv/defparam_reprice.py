#!/usr/bin/env python3
"""Reprice files blocked solely by ``DefParamSymbol:DefParam``.

``defparam`` changes a parameter during hierarchy elaboration.  This
read-only instrument reports target-path and override shapes while leaving
hierarchical binding, precedence and generate ordering loud.
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
WALL = "DefParamSymbol:DefParam"


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


def _normal(text):
    return re.sub(r"\s+", "", text).lower()


def _defparam_entries(source):
    """Return ``(target, rhs)`` entries from source defparam statements."""
    entries = []
    for match in re.finditer(r"\bdefparam\b(?P<body>.*?);", source,
                             flags=re.I | re.S):
        body = match.group("body")
        for item in body.split(","):
            if "=" not in item:
                continue
            target, rhs = item.split("=", 1)
            target = _normal(target)
            if target:
                entries.append((target, rhs.strip()))
    return entries


def defparam_features(text, context="", path=""):
    """Return overlapping source-shape labels for one defparam span."""
    statement = text.strip()
    raw_context = context or ""
    source = _without_comments(raw_context)
    lower_context = raw_context.lower()
    labels = []
    if "=" not in statement:
        return ()
    lhs, rhs = statement.split("=", 1)
    target = _normal(lhs)
    rhs = rhs.strip().rstrip(";")

    if "." in lhs:
        labels.append("hierarchical-target")
    if lhs.count(".") >= 2:
        labels.append("deep-path")
    if "[" in lhs:
        labels.append("array-element")

    entries = _defparam_entries(source)
    same_target = [entry for entry in entries if entry[0] == target]
    if len(same_target) >= 2:
        labels.append("last-wins")
    for match in re.finditer(r"\bdefparam\b(?P<body>.*?);", source,
                             flags=re.I | re.S):
        body = match.group("body")
        if "," not in body:
            continue
        for item in body.split(","):
            if "=" not in item:
                continue
            item_target, item_rhs = item.split("=", 1)
            if (_normal(item_target) == target
                    and _normal(item_rhs.rstrip(";"))
                    == _normal(rhs)):
                labels.append("multi-params")
                break
        if "multi-params" in labels:
            break

    # A parameter reference is an identifier left after removing ordinary
    # numeric literals.  The caller keeps the expression itself opaque.
    rhs_without_numbers = re.sub(r"\d+'[s]?[bodh]?[0-9a-fxz?_]+", " ", rhs,
                                 flags=re.I)
    rhs_without_numbers = re.sub(r"\b\d+(?:\.\d+)?\b", " ",
                                 rhs_without_numbers)
    if re.search(r"[A-Za-z_$]", rhs_without_numbers):
        labels.append("rhs-parameter")
    if re.search(r"[+*/%-]", rhs):
        labels.append("rhs-arithmetic")

    # These labels identify the explicit precedence/order scenarios named by
    # the source contract.  They do not infer an elaboration result.
    if re.search(r"conflicts.*instance\s+param|wins\s+over\s+instance|"
                 r"take\s+precedence\s+over\s+module\s+instantiation",
                 lower_context, re.S):
        labels.append("instance-precedence")
    if re.search(r"before\s+generate|generate\s+construct|"
                 r"re-evaluat(?:e|es|ed).*generate|elaboration algorithm",
                 lower_context, re.S):
        labels.append("generate-order")
    if re.search(r":type:\s*compile_error\b|cannot\s+target|\billegal\b",
                 lower_context, re.S):
        labels.append("diagnostic")
    if "/chapter-37/" in path.replace("\\", "/"):
        labels.append("type-example")
    if re.search(r"dependence|recomput(?:e|es|ed)", lower_context):
        labels.append("dependent-parameter")

    return tuple(dict.fromkeys(labels))


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\bdefparam\b", text, re.I):
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
    return "defparam_only", [
        defparam_features(node.get("text", ""), text, path.as_posix())
        for node in unsupported
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    defparam_files = 0
    defparam_instances = 0
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
        elif status == "defparam_only":
            defparam_files += 1
            defparam_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "defparam_only_files": defparam_files,
        "defparam_instances": defparam_instances,
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
