#!/usr/bin/env python3
"""Reprice files blocked solely by ``NetSymbol:delay``.

Net delays publish value transitions through the scheduler after rise, fall
and turn-off selection.  This read-only instrument reports declaration and
transition shapes while leaving delayed publication loud.
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
WALL = "NetSymbol:delay"
NET_KINDS = r"wire|tri|wand|wor|uwire|trireg|tri0|tri1"


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


def _target_names(text):
    lhs = text.split("=", 1)[0]
    return tuple(re.findall(r"\\[^\s;=]+|[A-Za-z_$][\w$]*", lhs))


def net_delay_features(text, context="", path=""):
    """Return overlapping source-shape labels for one delayed-net span."""
    raw = context or ""
    source = _without_comments(raw)
    lower_raw = raw.lower()
    labels = ["net-delay"]

    names = _target_names(text)
    # A declaration delay is also the delay of a declaration-time continuous
    # assignment only when the target itself is followed by ``=``.  A bare
    # delayed net with a later ``assign`` is a net delay alone.
    declaration_assignment = False
    for name in names:
        escaped = re.escape(name.lstrip("\\"))
        if re.search(r"\b(?:" + NET_KINDS + r")\b[^;\n]*\b"
                     + escaped + r"\b\s*=", source, re.I):
            declaration_assignment = True
            break
    if declaration_assignment:
        labels.append("continuous-assign-delay")

    delay_specs = re.findall(r"#\s*\(([^)]*)\)", source)
    if any(spec.count(",") >= 1 for spec in delay_specs):
        labels.append("rise-fall")
    if any(spec.count(",") >= 2 for spec in delay_specs):
        labels.append("turnoff")
    if any(spec.count(":") >= 2 for spec in delay_specs):
        labels.append("min-typ-max")
    if re.search(r"\b(?:" + NET_KINDS + r")\b\s*\[[^\]]+\][^;\n]*#",
                 source, re.I):
        labels.append("vector")

    if re.search(r"inertial|cancel|deschedul|reschedul|not retroactive",
                 lower_raw):
        labels.append("inertial")
    if re.search(r"\b(?:[A-Za-z_$][\w$]*)\s*=\s*[^;\n]*'b[01xz]",
                 source, re.I):
        # This catches source transitions to z in the concrete fixtures while
        # avoiding prose that merely mentions a turn-off transition.
        if re.search(r"=\s*\d*'b[01]?z\b", source, re.I):
            labels.append("z-transition")
    if ("/chapter-10/10.3.3--ca-decl-delay" in path
            or "net-delay-vs-ca-delay-in-decl" in path):
        labels.append("ca-vs-net")
    if "/chapter-37/" in path:
        labels.append("type-example")

    return tuple(dict.fromkeys(labels))


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\b(?:wire|tri|wand|wor|uwire|trireg)\b[^;\n]*#",
                     text, re.I):
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
    return "net_delay_only", [
        net_delay_features(node.get("text", ""), text, path.as_posix())
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
        elif status == "net_delay_only":
            delay_files += 1
            delay_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "net_delay_only_files": delay_files,
        "net_delay_instances": delay_instances,
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
