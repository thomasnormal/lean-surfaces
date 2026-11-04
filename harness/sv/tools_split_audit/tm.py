#!/usr/bin/env python3.12
"""tm.py CASE...  : run one audit case through slang / Icarus / Verilator / Yosys(+netlist sim); writes
results/<case>.json and work/<case>/{tb.sv,...}. The Xcelium column is filled by xc.py (batched)."""
import json, os, re, subprocess, sys, shutil, glob
WT = os.environ["WT"]
sys.path.insert(0, f"{WT}/harness/sv")
from gen_tb2 import generate_tb2
import pyslang
from pyslang.syntax import SyntaxTree
from pyslang.ast import Compilation

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.environ.get("AUDIT_DIR") or os.path.join(HERE, "out")
T_RUN = 40

def sh(cmd, cwd, timeout=T_RUN):
    try:
        p = subprocess.run(cmd, cwd=cwd, shell=isinstance(cmd, str), capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout, p.stderr, False
    except subprocess.TimeoutExpired as e:
        return -9, (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or ""), \
               (e.stderr or b"").decode() if isinstance(e.stderr, bytes) else (e.stderr or ""), True

def cyc(text):
    return [l.strip() for l in text.splitlines() if l.startswith("CYCLE ")]

def noncyc(out, err):
    l = [x for x in (out + "\n" + err).splitlines() if x.strip() and not x.startswith("CYCLE ") and "$finish" not in x]
    return " / ".join(l)[:300]

def ports_of(files, top):
    comp = Compilation()
    for f in files:
        comp.addSyntaxTree(SyntaxTree.fromFile(f))
    ports = []
    for inst in comp.getRoot().topInstances:
        if inst.name != top:
            continue
        for p in inst.body.portList:
            d = str(p.direction).split(".")[-1]
            ports.append((p.name, {"In": "in", "Out": "out", "InOut": "inout"}.get(d, d), p.type.bitWidth))
    return ports

def slang_params(files, top, params):
    """elaborated parameter values of every instance, as slang computes them"""
    from pyslang.ast import CompilationOptions, SymbolKind
    out = {}
    try:
        opts = CompilationOptions()
        opts.topModules = {top}
        if params: opts.paramOverrides = [f"{k}={v}" for k, v in params.items()]
        comp = Compilation(pyslang.Bag([opts]))
        for f in files: comp.addSyntaxTree(SyntaxTree.fromFile(f))
        def walk(inst, path):
            for m in inst.body:
                if m.kind == SymbolKind.Parameter:
                    out[path + "." + m.name] = f"{m.type} {m.value}"
                elif m.kind == SymbolKind.Instance:
                    walk(m, path + "." + m.name)
                elif m.kind == SymbolKind.GenerateBlock:
                    pass
        for inst in comp.getRoot().topInstances:
            if inst.name == top: walk(inst, inst.name)
    except Exception as e:
        out["error"] = repr(e)
    return out

def run_case(cid):
    cd = os.path.join(DATA, "cases", cid)
    case = json.load(open(os.path.join(cd, "case.json")))
    wd = os.path.join(DATA, "work", cid)
    shutil.rmtree(wd, ignore_errors=True); os.makedirs(wd)
    files = sorted(os.path.join(cd, f) for f in os.listdir(cd) if f.endswith(".sv"))
    for f in files: shutil.copy(f, wd)
    dut = [os.path.join(wd, os.path.basename(f)) for f in files]
    top = case["top"]
    res = {"case": cid, "claim": case.get("claim"), "row": case.get("row"), "ls_sv_refusal": case.get("refusal")}
    # slang (real driver, incl. analysis)
    params = case.get("params") or {}
    gargs = [a for k, v in params.items() for a in ("-G", f"{k}={v}")]
    rc, out, err, to = sh(["python3.12", os.path.join(HERE, "slangdiag.py"), "--top", top, *gargs, *(case.get("slang_args", [])), *dut], wd)
    txt = (out + err)
    errs = [l for l in txt.splitlines() if re.search(r": error:", l)]
    warns = [l for l in txt.splitlines() if re.search(r": warning:", l)]
    res["slang"] = {"rc": rc, "errors": [re.sub(r"^.*/work/[^/]+/", "", l) for l in errs], "warnings": [re.sub(r"^.*/work/[^/]+/", "", l) for l in warns]}
    res["slang"]["params"] = slang_params(dut, top, params)
    # ports + testbench
    try:
        ports = ports_of(dut, top)
        c = dict(case); c.setdefault("clock", "clk")
        tb = generate_tb2(top, ports, c)
        open(os.path.join(wd, "tb.sv"), "w").write(tb)
        res["ports"] = ports
    except Exception as e:
        res["tb_error"] = repr(e)
        json.dump(res, open(os.path.join(DATA, "results", cid + ".json"), "w"), indent=1)
        return res
    # Icarus
    rc, out, err, to = sh(f"iverilog -g2012 -s tb -o ivl.vvp tb.sv {' '.join(os.path.basename(d) for d in dut)}", wd)
    if rc != 0:
        res["icarus"] = {"status": "compile-error", "msg": (err + out).strip()[:400]}
    else:
        rc, out, err, to = sh("vvp ivl.vvp", wd, timeout=20)
        res["icarus"] = {"status": "timeout" if to else "ok", "cycles": cyc(out), "msg": noncyc(out, err)}
    # Verilator is 2-state: x/z stimulus digits become 0 (a tb with 1'bx literals is mis-simulated by it)
    c3 = dict(c)
    c3["stimulus"] = [{k: re.sub("[xzXZ]", "0", v) for k, v in e.items()} for e in c["stimulus"]]
    open(os.path.join(wd, "tb_v.sv"), "w").write(generate_tb2(top, ports, c3))
    res["verilator_stimulus_2state"] = c3["stimulus"] != c["stimulus"]
    rc, out, err, to = sh(f"verilator --binary --timing -Wno-fatal -Wno-lint --top-module tb -Mdir vobj tb_v.sv {' '.join(os.path.basename(d) for d in dut)}", wd, timeout=120)
    vw = sorted(set(re.findall(r"%(Warning|Error)-([A-Z0-9_]+)", out + err)))
    if rc != 0:
        res["verilator"] = {"status": "compile-error", "msg": "\n".join(l for l in (out + err).splitlines() if l.startswith("%Error"))[:500], "diags": [f"{a}-{b}" for a, b in vw]}
    else:
        rc2, out2, err2, to2 = sh("./vobj/Vtb", wd, timeout=20)
        res["verilator"] = {"status": "timeout" if to2 else "ok", "cycles": cyc(out2), "diags": [f"{a}-{b}" for a, b in vw], "msg": noncyc(out2, err2)}
    # Yosys: frontend + synth netlist, simulated in Icarus with the same tb
    chp = "".join(f"; chparam -set {k} {v} {top}" for k, v in params.items())
    ys = f"read_verilog -sv {' '.join(os.path.basename(d) for d in dut)}{chp}; hierarchy -check -top {top}; proc; flatten; opt_clean; synth -flatten -top {top}; write_verilog -noattr net.v"
    rc, out, err, to = sh(["yosys", "-l", "yosys.log", "-p", ys], wd, timeout=60)
    log = open(os.path.join(wd, "yosys.log")).read() if os.path.exists(os.path.join(wd, "yosys.log")) else (out + err)
    ywarn = sorted(set(re.sub(r"\s+", " ", m)[:160] for m in re.findall(r"Warning: ([^\n]*)", log)))
    yerr = [l for l in (log.splitlines()) if l.startswith("ERROR")]
    if rc != 0 or not os.path.exists(os.path.join(wd, "net.v")):
        res["yosys"] = {"status": "error" if not to else "timeout", "msg": ("\n".join(yerr) or log[-400:])[:500], "warnings": ywarn}
    else:
        c2 = dict(c); c2["params"] = {}
        open(os.path.join(wd, "tb_net.sv"), "w").write(generate_tb2(top, ports, c2))
        rc, out, err, to2 = sh(f"iverilog -g2012 -s tb -o net.vvp tb_net.sv net.v", wd)
        if rc != 0:
            res["yosys"] = {"status": "ok-netlist-unsimulatable", "warnings": ywarn, "msg": (err + out)[:300]}
        else:
            rc, out, err, to3 = sh("vvp net.vvp", wd, timeout=20)
            res["yosys"] = {"status": "ok" if not to3 else "netlist-sim-timeout", "cycles": cyc(out), "warnings": ywarn}
    json.dump(res, open(os.path.join(DATA, "results", cid + ".json"), "w"), indent=1)
    return res

if __name__ == "__main__":
    os.makedirs(os.path.join(DATA, "results"), exist_ok=True)
    ids = sys.argv[1:] or sorted(os.listdir(os.path.join(DATA, "cases")))
    for cid in ids:
        r = run_case(cid)
        print(cid, "slang:", ("ERR" if r["slang"]["errors"] else "ok"), "icarus:", r.get("icarus", {}).get("status"),
              "verilator:", r.get("verilator", {}).get("status"), "yosys:", r.get("yosys", {}).get("status"), flush=True)
