#!/usr/bin/env python3
"""Price parser-native function-effect summaries for the C unsequenced wall."""
import argparse, json
from pathlib import Path

def walk(v):
    if isinstance(v, dict):
        yield v
        for x in v.values(): yield from walk(x)
    elif isinstance(v, list):
        for x in v: yield from walk(x)

def effect(fn):
    nodes = list(walk(fn.get("body")))
    calls = sum(n.get("kind") == "CallExpr" for n in nodes)
    writes = sum(n.get("kind") == "CompoundAssignOperator" or
                 (n.get("kind") == "BinaryOperator" and n.get("op") in
                  ("=", "+=", "-=", "*=", "/=", "%=", "<<=", ">>=", "&=", "|=", "^="))
                 for n in nodes)
    increments = sum(n.get("kind") == "UnaryOperator" and n.get("op") in ("++", "--")
                     for n in nodes)
    return {"calls": calls, "writes": writes, "increments": increments,
            "conservative_pure_shape": calls == 0 and writes == 0 and increments == 0}

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--survey", default="docs/c-survey.json")
    ap.add_argument("--manifest", action="append", required=True)
    ap.add_argument("--json", required=True)
    ap.add_argument("--page", required=True)
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    if a.self_test:
        assert effect({"body": {"kind": "CompoundStmt", "body": []}})["conservative_pure_shape"]
        assert not effect({"body": {"kind": "CompoundStmt", "body": [{"kind": "CallExpr"}]}})["conservative_pure_shape"]
        print("c_effect_summary_price: self-test ok"); return 0
    survey = json.loads(Path(a.survey).read_text())
    rows = next(x for x in survey["dynamic_wall_ranking"] if x["wall"] == "unsequenced-effects")["files"]
    items = {}
    for mp in a.manifest:
        m=json.loads(Path(mp).read_text())
        for x in m.get("tests",[]):
            if x["name"] in rows and x.get("envelope") and Path(x["envelope"]).is_file(): items[x["name"]]=x["envelope"]
    out=[]
    for name in rows:
        env=json.loads(Path(items[name]).read_text()) if name in items else {}
        f=[n for n in walk(env) if n.get("kind")=="FunctionDecl" and n.get("body") is not None]
        out.append({"name":name,"functions":[{"name":x.get("name"),**effect(x)} for x in f]})
    report={"schema":"c-effect-summary-price-0.1","wall":"unsequenced-effects","files":len(out),"rows":out}
    Path(a.json).write_text(json.dumps(report,indent=1,sort_keys=True)+"\n")
    lines=["# C unsequenced-effect summary price","", "Parser-envelope census only; no purity theorem is claimed.","", "| file | functions | conservative pure shapes |", "| --- | ---: | ---: |"]
    for r in out:
        lines.append("| `%s` | %d | %d |"%(r["name"],len(r["functions"]),sum(x["conservative_pure_shape"] for x in r["functions"])))
    Path(a.page).write_text("\n".join(lines)+"\n")
    print("c_effect_summary_price: wrote",a.json,a.page)

if __name__ == "__main__": main()
