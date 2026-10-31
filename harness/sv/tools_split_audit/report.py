#!/usr/bin/env python3
"""report.py : the per-case appendix of docs/sv-tools-split-audit.md, generated from results/*.json,
ext_all.json (extractor), fs_all.json (svGolf fourstate), lean_all.json (run2, when present)."""
import json, os, re, sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import matrix
HERE = matrix.HERE
DATA = matrix.DATA
ext = json.load(open(os.path.join(DATA, "ext_all.json"))) if os.path.exists(os.path.join(DATA, "ext_all.json")) else {}
fs = json.load(open(os.path.join(DATA, "fs_all.json"))) if os.path.exists(os.path.join(DATA, "fs_all.json")) else {}
lean = json.load(open(os.path.join(DATA, "lean_all.json"))) if os.path.exists(os.path.join(DATA, "lean_all.json")) else {}
GROUPS = [
 ("Section A: the frontend rejects", ["a_st_invalid", "a_st_invalid2", "a_ex_invalid", "a_ex_op_invalid", "a_hi_uninst", "a_hi_uninst_gen", "a_drv_mix_plain", "a_drv_input_assign", "a_drv_input_proc", "a_drv_input_inst"]),
 ("le-driver-procs / le-driver-mixed", ["drv_pw_lit", "drv_pw_gv", "drv_pw_par_k0", "drv_pw_ff", "drv_mix_k0", "drv_pw_plain_always", "two_plain", "two_plain_ac", "init_comb_proc"]),
 ("pr-init-var", ["vg_initc", "vg_initf", "vg_initq", "vh_initcomb", "pr_init_fpga", "pr_init_comb_plain", "init_whole"]),
 ("hi-init-driver", ["vg_init", "vh_init", "vg_initn", "pi_in_init", "pi_in_init2", "pi_in_top", "pi_in_net"]),
 ("dc-port-init / dc-port-explicit", ["dc_port_net_init", "dc_port_net_init2", "pi_explicit"]),
 ("lit-string / lit-string-hex", ["lit_str_a", "lit_str_v", "lit_str_f", "lit_str_n", "lit_str_x41", "lit_str_x4", "hex_guard", "lit_str_o101", "lit_str_nonlatin", "lit_str_nonlatin2"]),
 ("hi-override-context", ["fold_ovr", "fold_ovrw_n1", "fold_ovrw_n24", "fold_uwovr", "fold_uwovr_n0", "fold_sho_n1", "fold_sho_n40"]),
 ("le-portconn-context-width", ["ctx_pq", "ctx_const40"]),
 ("gu-self-read", ["rbw_comb", "rbw_held", "rbw_bits", "rbw_cond", "rbw_case_item", "rbw_dyn", "rbw_part", "rbw_nested", "rbw_child"]),
 ("gu-alias-read", ["acg_alias_assign", "acg_alias_port", "acg_alias_chain", "acg_alias_not", "acg_alias_bits", "acg_alias_hier", "acg_alias_thru", "acg_alias_wr", "acg_alias_copy"]),
 ("gu-comb-loop / pr-always-nocontrol", ["loop_osc", "loop_osc2", "loop_mux", "loop_fn", "loop_sr", "loop_comb_block", "loop_lat_if", "loop_lat_if_b", "alw_nocontrol", "alw_nocontrol_ff"]),
]
def slangcell(r):
    e = r["slang"]["errors"]
    if not e: return "ok" + (" (warn)" if r["slang"]["warnings"] else "")
    m = re.search(r"error: (.*?)( \[-W[^\]]*\])?$", e[0]); return "ERROR: " + (m.group(1)[:60] if m else e[0][:60])
out = []
w = out.append
for title, ids in GROUPS:
    w(f"### {title}")
    w("")
    w("| case | slang | Icarus | Verilator | Yosys | Xcelium | ls-sv extractor | fourstate | run2 |")
    w("|---|---|---|---|---|---|---|---|---|")
    traces = []
    for cid in ids:
        r, case, x = matrix.load(cid)
        c = matrix.row(cid)
        letters = {}
        def cellv(v):
            if v in ("ok", "REJECT", "HANG", "-", "timeout", "netlist-sim-timeout") or v.startswith("ok("): return {"REJECT": "reject", "HANG": "hangs"}.get(v, v)
            letters.setdefault(v, chr(ord("A") + len(letters))); return letters[v]
        cells = [cellv(c[t]) for t in ("icarus", "verilator", "yosys", "xcelium")]
        e = ext.get(cid, {}); eu = ", ".join(f"`{k}`" for k in (e.get("unsupported") or [])) or ("-" if e.get("unsupported") == [] else "?")
        f = fs.get(cid, {}); fv = {True: "pass", False: "REJECT", None: "?"}.get(f.get("passed"), "?")
        lv = lean.get(cid, "")
        w(f"| `{cid}` | {slangcell(r)} | " + " | ".join(cells) + f" | {eu} | {fv} | {lv} |")
        if letters:
            traces.append(f"* `{cid}`: " + "; ".join(f"**{l}** = `{v[:240]}`" for v, l in letters.items()))
    w("")
    if traces:
        w("Traces (one value per stimulus cycle; a letter names one distinct trace of the case):")
        w("")
        out.extend(traces)
        w("")
print("\n".join(out))
