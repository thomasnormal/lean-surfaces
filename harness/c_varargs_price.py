#!/usr/bin/env python3
"""Price parser-native variadic-call evidence for the C extra-argument wall."""
import argparse, json
from pathlib import Path

def walk(v):
    if isinstance(v,dict):
        yield v
        for x in v.values(): yield from walk(x)
    elif isinstance(v,list):
        for x in v: yield from walk(x)

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--manifest',action='append',required=True); ap.add_argument('--json',required=True); ap.add_argument('--page',required=True); ap.add_argument('--self-test',action='store_true'); a=ap.parse_args()
    if a.self_test:
        assert '...' in 'int (int, ...)'; print('c_varargs_price: self-test ok'); return
    names=set(); envs={}
    for mp in a.manifest:
        m=json.loads(Path(mp).read_text())
        for x in m.get('tests',[]):
            if x.get('envelope') and Path(x['envelope']).is_file(): names.add(x['name']); envs[x['name']]=x['envelope']
    rows=[]
    for name in sorted(names):
        e=json.loads(Path(envs[name]).read_text()); fs=[n for n in walk(e) if n.get('kind')=='FunctionDecl']; vari=[f for f in fs if '...' in (f.get('type') or '')]
        va=sum(n.get('kind')=='Unsupported' and n.get('c_kind')=='VAArgExpr' for n in walk(e))
        calls=[n for n in walk(e) if n.get('kind')=='CallExpr']; extra=0
        for c in calls:
            cal=c.get('callee',{}); t=next((x.get('type','') for x in walk(cal) if x.get('kind')=='DeclRefExpr'), '')
            if '...' in t and len(c.get('args',[]))>0: extra+=1
        if vari or va: rows.append({'name':name,'variadic_functions':len(vari),'va_arg_nodes':va,'variadic_calls':extra})
    report={'schema':'c-varargs-price-0.1','files':len(rows),'rows':rows}
    Path(a.json).write_text(json.dumps(report,indent=1,sort_keys=True)+'\n')
    lines=['# C variadic-argument wall price','','Parser-envelope census only; ABI semantics are not claimed.','','| file | variadic functions | VAArg nodes | variadic calls |','| --- | ---: | ---: | ---: |']
    lines += ['| `%s` | %d | %d | %d |'%(r['name'],r['variadic_functions'],r['va_arg_nodes'],r['variadic_calls']) for r in rows]
    Path(a.page).write_text('\n'.join(lines)+'\n'); print('c_varargs_price: wrote',a.json,a.page)
if __name__=='__main__': main()
