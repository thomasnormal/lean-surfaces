#!/usr/bin/env python3
"""Reprice files blocked solely by ``ElabSystemTaskSymbol:ElabSystemTask``."""
import argparse, collections, json, pathlib, re, sys
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree
REPO = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "extractors" / "sv"))
import extract  # noqa: E402
INCLUDE_RE = re.compile(r'^\s*`include\s*(?:["<`])', re.M)
WALL = "ElabSystemTaskSymbol:ElabSystemTask"
def walk(node):
    if isinstance(node, dict):
        yield node
        for value in node.values(): yield from walk(value)
    elif isinstance(node, list):
        for value in node: yield from walk(value)
def elab_task_features(text):
    source = re.sub(r"//[^\n]*|/\*.*?\*/", " ", text, flags=re.S).lower()
    labels = []
    if "$info" in source: labels.append("info")
    if "$warning" in source: labels.append("warning")
    if "$error" in source: labels.append("error")
    return tuple(labels or ("other-elaboration-task",))
def one_file(path):
    data = path.read_bytes(); text = data.decode("utf-8")
    if INCLUDE_RE.search(text): return "skip_include", []
    tree = SyntaxTree.fromText(text, name=path.as_posix()); compilation = Compilation(); compilation.addSyntaxTree(tree)
    extract._SOURCE_BYTES = data; envelope = extract.convert_design(tree.sourceManager, compilation)
    unsupported = [n for n in walk(envelope) if n.get("kind") == "Unsupported"]
    if {n.get("sv_kind") for n in unsupported} != {WALL}: return "other", []
    return "elab_task_only", [elab_task_features(text) for _ in unsupported]
def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument("--corpus", required=True, type=pathlib.Path); args = parser.parse_args(argv)
    paths = sorted(args.corpus.glob("chapter-*/*.sv")); files = spans = skips = errors = 0; features = collections.Counter(); feature_files = collections.defaultdict(set)
    for path in paths:
        try: status, sets = one_file(path)
        except Exception as exc: print(f"error: {path}: {exc}", file=sys.stderr); errors += 1; continue
        if status == "skip_include": skips += 1
        elif status == "elab_task_only":
            files += 1; spans += len(sets)
            for ss in sets:
                for feature in ss: features[feature] += 1; feature_files[feature].add(path.as_posix())
    print(json.dumps({"corpus_files": len(paths), "elab_task_only_files": files, "elab_task_spans": spans, "include_skips": skips, "errors": errors, "features": {f: {"spans": features[f], "files": len(feature_files[f])} for f in sorted(features)}}, indent=2, sort_keys=True)); return 1 if errors else 0
if __name__ == "__main__": raise SystemExit(main())
