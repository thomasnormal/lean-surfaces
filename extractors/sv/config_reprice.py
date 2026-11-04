#!/usr/bin/env python3
"""Reprice files blocked solely by ``ConfigBlockSymbol``.

Configurations are elaboration-time design elements.  This read-only
instrument keeps the extractor's sole-wall census, then inspects each config
declaration's syntax so the residual is reported as IEEE clause shapes rather
than as a generic frontend class.  It never resolves a library or changes the
envelope produced by the extractor.
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


def walk(node):
    """Walk an envelope value, yielding dictionary nodes."""
    if isinstance(node, dict):
        yield node
        for value in node.values():
            yield from walk(value)
    elif isinstance(node, list):
        for value in node:
            yield from walk(value)


def _short_kind(value):
    """Use stable syntax class names without the pyslang suffix."""
    name = type(value).__name__
    return name[:-6] if name.endswith("Syntax") else name


def clause_kind(clause):
    """Classify a config rule's binding clause."""
    if clause is None:
        return "missing"
    kind = _short_kind(clause)
    if kind == "ConfigLiblist":
        return "liblist"
    if kind == "ConfigUseClause":
        return "use"
    return kind


def config_shape(has_design, localparam_count, rules):
    """Return a compact, source-independent configuration shape.

    ``rules`` is a sequence of ``(rule-kind, clause-kind)`` pairs.  Keeping
    this helper pure makes the classifier tests independent of pyslang's
    syntax object lifetime.
    """
    parts = ["design" if has_design else "no-design"]
    if localparam_count:
        parts.append("localparam")
    for rule_kind, binding_kind in rules:
        parts.append("%s-%s" % (rule_kind, binding_kind))
    return "+".join(parts)


def describe_config(config):
    """Extract clause telemetry from one ``ConfigDeclarationSyntax``."""
    rules = []
    for rule in getattr(config, "rules", ()):  # malformed configs may omit it
        kind = _short_kind(rule)
        if kind == "DefaultConfigRule":
            binding = getattr(rule, "liblist", None)
            rules.append(("default", clause_kind(binding)))
        elif kind in ("CellConfigRule", "InstanceConfigRule"):
            binding = getattr(rule, "ruleClause", None)
            rules.append((kind[:-10].lower(), clause_kind(binding)))
        else:
            rules.append((kind.lower(), "unknown"))
    top_cells = list(getattr(config, "topCells", ()) or ())
    localparams = list(getattr(config, "localparams", ()) or ())
    return {
        "shape": config_shape(bool(top_cells), len(localparams), rules),
        "has_design": bool(top_cells),
        "top_cells": len(top_cells),
        "localparams": len(localparams),
        "rules": rules,
    }


def one_file(path):
    """Return ``(status, config descriptions)`` for one corpus source."""
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
    if kinds != {"ConfigBlockSymbol"}:
        return "other", []

    configs = []
    for unit in compilation.getCompilationUnits():
        for member in unit:
            if str(getattr(member, "kind", "")) == "SymbolKind.ConfigBlock":
                configs.append(describe_config(member.syntax))
    return "config_only", configs


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", required=True, type=pathlib.Path,
                        help="chapter-scoped sv-tests-2 tests directory")
    args = parser.parse_args(argv)

    files = sorted(args.corpus.glob("chapter-*/*.sv"))
    config_files = 0
    config_blocks = 0
    multi_config_files = 0
    design = collections.Counter()
    localparams = 0
    rules = collections.Counter()
    rule_files = collections.defaultdict(set)
    skipped = 0
    errors = 0

    for path in files:
        try:
            status, configs = one_file(path)
        except Exception as exc:  # keep the measurement loud and complete
            print(f"error: {path}: {exc}", file=sys.stderr)
            errors += 1
            continue
        if status == "skip_include":
            skipped += 1
        elif status == "config_only":
            config_files += 1
            config_blocks += len(configs)
            if len(configs) > 1:
                multi_config_files += 1
            for config in configs:
                design["present" if config["has_design"] else "absent"] += 1
                design["top_cells"] += config["top_cells"]
                localparams += config["localparams"]
                for rule_kind, binding_kind in config["rules"]:
                    key = f"{rule_kind}/{binding_kind}"
                    rules[key] += 1
                    rule_files[key].add(path.as_posix())

    result = {
        "corpus_files": len(files),
        "config_only_files": config_files,
        "config_blocks": config_blocks,
        "multi_config_files": multi_config_files,
        "design": dict(sorted(design.items())),
        "localparam_declarations": localparams,
        "include_skips": skipped,
        "errors": errors,
        "rules": {
            key: {"instances": rules[key],
                  "files": len(rule_files[key])}
            for key in sorted(rules)
        },
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
