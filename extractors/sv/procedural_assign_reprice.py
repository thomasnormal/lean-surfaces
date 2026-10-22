#!/usr/bin/env python3
"""Reprice files blocked solely by ``ProceduralAssignStatement``.

Procedural continuous assignments and force/release statements install
stateful drivers.  This read-only instrument reports the source shapes in
the sole-wall files; it never lowers a driver to an ordinary assignment or
changes the scheduler-facing envelope.
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
WALL = "ProceduralAssignStatement"


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


def _source_code(text):
    """Remove comments and corpus metadata before syntax-only checks."""
    source = _without_comments(text)
    return re.sub(r"^\s*:(?:name|description|tags|type|diagnostic_match):.*$",
                  " ", source, flags=re.M | re.I)


def _target_names(statement):
    """Return identifier bases in the LHS of an assign/force statement."""
    lhs = statement.split("=", 1)[0]
    lhs = re.sub(r"^\s*(?:assign|force)\b", "", lhs, flags=re.I)
    names = re.findall(r"\\[^\s;=]+|[A-Za-z_$][\w$]*", lhs)
    return tuple(name.rstrip("]") for name in names)


def _is_literal_rhs(rhs):
    # Strip the integral literal forms before looking for identifiers or
    # operators.  The remaining identifier/operator inventory is the useful
    # distinction for this repricer: a literal RHS has no source dependency.
    rhs = re.sub(r"\d+'[s]?[bodh]?[0-9a-fxz?_]+", " ", rhs,
                 flags=re.I)
    rhs = re.sub(r"\b\d+\b", " ", rhs)
    return not re.search(r"[A-Za-z_$]|[+*/%&|^~?:]", rhs)


def procedural_assign_features(text, context=""):
    """Return overlapping source-shape labels for one unsupported span.

    ``context`` is the complete source file when available.  The statement
    text supplies the target/RHS shape; context supplies declaration kind and
    the explicit compile-error or sensitivity notes used by the corpus.
    """
    statement = text.strip()
    raw_context = context or ""
    source = _source_code(raw_context)
    lower = statement.lower()
    lower_source = raw_context.lower()
    labels = []

    if re.match(r"assign\b", lower):
        labels.append("assign")
    if re.match(r"force\b", lower):
        labels.append("force")

    lhs, _, rhs = statement.partition("=")
    if "{" in lhs:
        labels.append("concat-lhs")
    if "[" in lhs:
        labels.append("select-lhs")
    if rhs and not _is_literal_rhs(rhs.rstrip(";")):
        labels.append("rhs-expression")

    names = _target_names(statement)
    for name in names:
        escaped = re.escape(name.lstrip("\\"))
        if re.search(r"\b(?:wire|tri|wand|wor|uwire|trireg)\b[^;\n]*\b"
                     + escaped + r"\b", source, re.I):
            labels.append("net-target")
            break
    for name in names:
        escaped = re.escape(name.lstrip("\\"))
        if re.search(r"\b(?:logic|reg|bit|integer|byte|shortint|int|longint)\b"
                     r"[^;\n]*\b" + escaped + r"\b", source, re.I):
            labels.append("variable-target")
            break

    # These labels describe explicit corpus scenarios.  Keep the source
    # wording in the input rather than inferring a driver graph from it.
    if re.search(r"\b(?:reevaluat\w*|sensitiv\w*|track(?:s|ing)? source|source changes)\b",
                 lower_source):
        labels.append("rhs-reevaluation")
    if re.search(r"\b(?:overrid\w*|priority|ignored|stuck)\b", lower_source):
        labels.append("priority-override")
    if re.search(r"\b(?:replac|deassign first|new assign)\b", lower_source):
        labels.append("replace-active")
    if re.search(r":type:\s*compile_error\b|\bmixed assignment\b",
                 lower_source):
        labels.append("mixed-assignment-diagnostic")
    if re.search(r"\balways\s*@", source, re.I):
        labels.append("event-sensitive")
    if re.search(r"^\s*initial[ \t]+(?:assign|force)\b",
                 source, re.M | re.I):
        labels.append("type-example")

    # A context label may match several spans in one file.  Preserve the
    # order above while making each span's feature tuple stable and unique.
    return tuple(dict.fromkeys(labels))


def one_file(path):
    """Return ``(status, feature tuples)`` for one source file."""
    data = path.read_bytes()
    text = data.decode("utf-8")
    if INCLUDE_RE.search(text):
        return "skip_include", []
    if not re.search(r"\b(?:assign|deassign|force|release)\b", text, re.I):
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
    return "procedural_assign_only", [
        procedural_assign_features(node.get("text", ""), text)
        for node in unsupported
    ]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    assign_files = 0
    assign_instances = 0
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
        elif status == "procedural_assign_only":
            assign_files += 1
            assign_instances += len(feature_sets)
            for feature_set in feature_sets:
                for feature in feature_set:
                    features[feature] += 1
                    feature_files[feature].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "procedural_assign_only_files": assign_files,
        "procedural_assign_instances": assign_instances,
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
