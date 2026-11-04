#!/usr/bin/env python3
"""Reprice files blocked solely by ``NamedValueExpression:2state``."""
import argparse, collections, json, pathlib, re, sys
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree
REPO=pathlib.Path(__file__).resolve().parents[2]; sys.path.insert(0,str(REPO/'extractors'/'sv')); import extract  # noqa: E402
INCLUDE_RE=re.compile(r'^\s*`include\s*(?:["<`])',re.M); WALL='NamedValueExpression:2state'
def walk(n):
    if isinstance(n,dict):
        yield n
        for v in n.values(): yield from walk(v)
    elif isinstance(n,list):
        for v in n: yield from walk(v)
def namedvalue_features(text):
    source=re.sub(r'//[^\n]*|/\*.*?\*/',' ',text,flags=re.S).lower(); labels=[]
    if re.search(r'\bforeach\s*\(',source): labels.append('fixed-array-foreach')
    if re.search(r'\btypedef\s+int\s+\w+\s*\[[^;]+\]',source) and re.search(r'\{[^}]*\}',source): labels.append('unpacked-array-concatenation')
    if re.search(r"\b\w+\s*=\s*'\s*\{",source): labels.append('array-literal-context')
    if re.search(r"\{\s*\d+\s*:",source): labels.append('indexed-array-pattern')
    return tuple(labels or ('other-two-state-name',))
def one_file(path):
    data=path.read_bytes(); text=data.decode()
    if INCLUDE_RE.search(text): return 'skip_include',[]
    tree=SyntaxTree.fromText(text,name=path.as_posix()); c=Compilation(); c.addSyntaxTree(tree); extract._SOURCE_BYTES=data; e=extract.convert_design(tree.sourceManager,c)
    u=[n for n in walk(e) if n.get('kind')=='Unsupported']
    if {n.get('sv_kind') for n in u}!={WALL}: return 'other',[]
    return 'namedvalue_only',[namedvalue_features(text) for _ in u]
def main(argv=None):
    p=argparse.ArgumentParser();p.add_argument('--corpus',required=True,type=pathlib.Path);a=p.parse_args(argv);paths=sorted(a.corpus.glob('chapter-*/*.sv'));files=spans=skips=errors=0;fs=collections.Counter();ff=collections.defaultdict(set)
    for path in paths:
        try: status,sets=one_file(path)
        except Exception as exc: print(f'error: {path}: {exc}',file=sys.stderr);errors+=1;continue
        if status=='skip_include':skips+=1
        elif status=='namedvalue_only':
            files+=1;spans+=len(sets)
            for ss in sets:
                for f in ss:fs[f]+=1;ff[f].add(path.as_posix())
    print(json.dumps({'corpus_files':len(paths),'namedvalue_only_files':files,'namedvalue_spans':spans,'include_skips':skips,'errors':errors,'features':{f:{'spans':fs[f],'files':len(ff[f])} for f in sorted(fs)}},indent=2,sort_keys=True));return 1 if errors else 0
if __name__=='__main__':raise SystemExit(main())
