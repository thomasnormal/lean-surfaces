#!/usr/bin/env python3
"""py_version_delta.py — the Python tier's VERSION delta, measured two ways.

The Python tier is reference-interpreter-EXTRACTED (docs/family-architecture.md
§4.1), so its version delta is not a document diff: it is what the interpreter
does differently. Two surfaces, because they answer different questions.

  --grammar   the `ast` module's own node classes and `_fields`, per version.
              Answers "what must the EXTRACTOR cover?"
  --scripts   the whole-program corpus (harness/scripts.json) executed under
              each interpreter, observable = stdout plus the final error line.
              Answers "what does the MODEL have to say differently?"

Run from the repo root. Every interpreter it cannot find is reported and
skipped LOUDLY; a row it cannot run is an ERROR row with a reason, never a
silently dropped one. Output is deterministic: a re-run is byte-identical.

    python3 harness/py_version_delta.py --grammar --scripts

The fuller closed-function instrument (all 1394 cases.json calls, with the
exception-MESSAGE comparison the harness itself does not make) is recorded in
docs/backlog.md; this file is the cheap standing check.
"""
import argparse
import json
import pathlib
import subprocess
import sys

REPO = pathlib.Path(__file__).resolve().parent.parent
DEFAULT_VERSIONS = ["3.9", "3.11", "3.12", "3.14"]
# Pre-3.8 deprecated aliases; they are not grammar, and counting them makes the
# 3.12 removal look like a language change when it is a spring-clean.
ALIASES = {"Num", "Str", "Bytes", "NameConstant", "Ellipsis", "_ast_Ellipsis"}
SORTS = ["stmt", "expr", "operator", "unaryop", "cmpop", "boolop",
         "excepthandler", "mod", "pattern", "type_param"]

DUMP = r"""
import ast, json, sys
nodes, sorts = {}, {}
for name in dir(ast):
    obj = getattr(ast, name)
    if isinstance(obj, type) and issubclass(obj, ast.AST) and obj is not ast.AST:
        nodes[name] = list(getattr(obj, "_fields", ()))
for base in %r:
    b = getattr(ast, base, None)
    sorts[base] = None if b is None else sorted(
        n for n in dir(ast)
        if isinstance(getattr(ast, n), type) and issubclass(getattr(ast, n), b)
        and getattr(ast, n) is not b)
json.dump({"version": "%%d.%%d.%%d" %% sys.version_info[:3],
           "nodes": nodes, "sorts": sorts}, sys.stdout, sort_keys=True)
""" % (SORTS,)


def interp(v):
    for cand in (f"python{v}", f"/opt/homebrew/bin/python{v}", f"/usr/bin/python{v}"):
        try:
            subprocess.run([cand, "-c", ""], capture_output=True, timeout=30, check=True)
            return cand
        except Exception:
            continue
    return None


def resolve(versions):
    found, missing = {}, []
    for v in versions:
        p = interp(v)
        (found.__setitem__(v, p) if p else missing.append(v))
    if missing:
        print(f"py_version_delta: interpreters NOT FOUND and skipped: {', '.join(missing)}",
              file=sys.stderr)
    if not found:
        sys.exit("py_version_delta: no interpreter found at all — refusing")
    return found


def grammar(found):
    g = {}
    for v, exe in found.items():
        p = subprocess.run([exe, "-c", DUMP], capture_output=True, text=True, timeout=120)
        if p.returncode != 0:
            sys.exit(f"py_version_delta: ast dump failed on {v}: {p.stderr.strip()[:300]}")
        g[v] = json.loads(p.stdout)
    out = {"per_version": {}, "steps": {}}
    for v, d in g.items():
        real = {k: f for k, f in d["nodes"].items() if k not in ALIASES}
        out["per_version"][v] = {
            "runtime": d["version"],
            "node_classes_all": len(d["nodes"]),
            "node_classes_excl_aliases": len(real),
            "sorts": {s: (len([x for x in (d["sorts"][s] or []) if x not in ALIASES])
                          if d["sorts"][s] is not None else None) for s in SORTS},
        }
    vs = list(found)
    for a, b in zip(vs, vs[1:]):
        na = {k: f for k, f in g[a]["nodes"].items() if k not in ALIASES}
        nb = {k: f for k, f in g[b]["nodes"].items() if k not in ALIASES}
        common = sorted(set(na) & set(nb))
        out["steps"][f"{a}->{b}"] = {
            "added": sorted(set(nb) - set(na)),
            "removed": sorted(set(na) - set(nb)),
            "fields_changed": {k: {"from": na[k], "to": nb[k]}
                               for k in common if na[k] != nb[k]},
            "identical_fields": sum(1 for k in common if na[k] == nb[k]),
            "common": len(common),
        }
    return out


def scripts(found):
    rows = json.loads((REPO / "harness/scripts.json").read_text())
    res, errors = {}, []
    for r in rows:
        f = REPO / r["file"]
        if not f.is_file():
            errors.append({"file": r["file"], "why": "missing"})
            continue
        obs = {}
        for v, exe in found.items():
            try:
                p = subprocess.run([exe, str(f)], capture_output=True, text=True,
                                   timeout=60, cwd=REPO)
                tail = p.stderr.strip().splitlines()[-1] if p.stderr.strip() else ""
                obs[v] = p.stdout + ("\n!!" + tail if tail else "")
            except subprocess.TimeoutExpired:
                obs[v] = None
                errors.append({"file": r["file"], "version": v, "why": "timeout 60s"})
        res[r["file"]] = obs
    vs = list(found)
    base = vs[0]
    out = {"rows": len(res), "base": base, "errors": errors, "deltas": {}, "same_as_base": {}}
    for v in vs[1:]:
        same = [f for f, o in res.items() if o.get(v) is not None and o[v] == o[base]]
        out["same_as_base"][v] = {"same": len(same), "of": len(res)}
        out["deltas"][v] = [
            {"file": f,
             # The distinction the architecture turns on: a changed VALUE is a
             # semantic change; changed error TEXT is a rendering change.
             "kind": ("error-text" if "!!" in (o[base] or "") or "!!" in (o[v] or "")
                      else "value/stdout"),
             "base_tail": ((o[base] or "").strip().splitlines() or [""])[-1][:200],
             "other_tail": ((o[v] or "").strip().splitlines() or [""])[-1][:200]}
            for f, o in sorted(res.items())
            if o.get(v) is not None and o[v] != o[base]]
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--grammar", action="store_true")
    ap.add_argument("--scripts", action="store_true")
    ap.add_argument("--versions", nargs="*", default=DEFAULT_VERSIONS)
    ap.add_argument("-o", "--out")
    a = ap.parse_args()
    if not (a.grammar or a.scripts):
        a.grammar = a.scripts = True
    found = resolve(a.versions)
    out = {"instrument": "harness/py_version_delta.py", "interpreters": found}
    if a.grammar:
        out["grammar"] = grammar(found)
    if a.scripts:
        out["scripts"] = scripts(found)
    text = json.dumps(out, indent=2, sort_keys=True) + "\n"
    if a.out:
        pathlib.Path(a.out).write_text(text)
    if a.grammar:
        pv = out["grammar"]["per_version"]
        print("grammar, node classes excluding deprecated aliases:")
        for v in found:
            s = pv[v]["sorts"]
            print(f"  {v}: {pv[v]['node_classes_excl_aliases']:4d} classes   "
                  f"stmt {s['stmt']}  expr {s['expr']}  "
                  f"operator {s['operator']}  unaryop {s['unaryop']}  "
                  f"cmpop {s['cmpop']}  boolop {s['boolop']}")
        for step, d in out["grammar"]["steps"].items():
            print(f"  {step}: +{len(d['added'])} -{len(d['removed'])} "
                  f"fields-changed {len(d['fields_changed'])} "
                  f"({d['identical_fields']}/{d['common']} identical)")
    if a.scripts:
        s = out["scripts"]
        print(f"scripts: {s['rows']} rows, base {s['base']}, {len(s['errors'])} error rows")
        for v, d in s["same_as_base"].items():
            print(f"  {s['base']} == {v}: {d['same']}/{d['of']}")
            for row in s["deltas"][v]:
                print(f"     [{row['kind']}] {row['file']}")


if __name__ == "__main__":
    main()
