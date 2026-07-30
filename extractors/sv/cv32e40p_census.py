#!/usr/bin/env python3.12
"""CV32E40P program scoreboard census (phase 1: symbolic extraction).

Runs `extract.py --top <module>` (in-process) over every RTL module of an
OpenHW cv32e40p checkout — each module compiled together with the three
`rtl/include` packages (multi-file compilation for NAME RESOLUTION only) —
and additionally runs the unchanged single-file M0 mode over the same
files as the *baseline*. Per file it tallies:

  * total envelope node count, split into represented-concrete /
    represented-SYMBOLIC (the new phase-1 class: ParameterDecl, LocalParam,
    ParamRef, GenvarRef, GenerateFor, GenerateIf, EnumType, EnumRef,
    TypeRef, SysCall, Import) / Unsupported;
  * every `Unsupported` node's `sv_kind` (the phase-2+ work queue) and the
    semantic TIER each class belongs to (T-select/T-case/T-reset/T-ops/
    T-hier/T-struct; T-array is a cross-cutting state-shape annotation).

It regenerates three marker-delimited sections of the scoreboard markdown
(`docs/cv32e40p-coverage.md`): the per-file table, the global blocker
before/after table, and the tier ladder.

Usage (from the repo root):

    python3.12 extractors/sv/cv32e40p_census.py <cv32e40p-checkout> \
        [--out-json docs/cv32e40p-census.json] \
        [--out-md docs/cv32e40p-coverage.md]

Deterministic: files processed in sorted order; envelopes produced by the
same conversion the CLI uses; all counters serialized with sorted keys —
a double run produces byte-identical JSON and markdown.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import extract  # noqa: E402

PKG_FILES = (
    "rtl/include/cv32e40p_pkg.sv",
    "rtl/include/cv32e40p_apu_core_pkg.sv",
    "rtl/include/cv32e40p_fpu_pkg.sv",
)

# The full symbolic-mode vocabulary (for the vocabulary-use summary).
SYMBOLIC_KINDS = (
    "ParameterDecl", "LocalParam", "ParamRef", "GenvarRef", "GenerateFor",
    "GenerateIf", "EnumType", "EnumRef", "TypeRef", "SysCall", "Int",
    "Fill", "Resize", "PackedType", "Import",
)

# The NEW node class introduced by phase 1 (params/generates/enums/
# syscalls/typerefs/imports). Int/Fill/PackedType/Resize are shared with
# the concrete vocabulary and count as represented-concrete even when
# their bounds carry ParamRef children (the children are counted here).
SYMBOLIC_CLASS = (
    "ParameterDecl", "LocalParam", "ParamRef", "GenvarRef", "GenerateFor",
    "GenerateIf", "EnumType", "EnumRef", "TypeRef", "SysCall", "Import",
)

# Residual Unsupported class -> semantic tier (phase-2+ Lean workload).
TIER_OF = {
    "ElementSelectExpression": "T-select",
    "RangeSelectExpression": "T-select",
    "AssignmentExpression:target": "T-select",
    "ReplicationExpression": "T-select",
    "CaseStatement": "T-case",
    "TimedStatement:EventListControl": "T-reset",
    "ProceduralBlockSymbol:AlwaysLatch": "T-reset",
    "CallExpression": "T-ops",
    "ConversionExpression:width": "T-ops",
    "ConversionExpression:Explicit": "T-ops",
    "UnaryExpression:BitwiseOr": "T-ops",
    "BinaryExpression:LogicalShiftLeft": "T-ops",
    "BinaryExpression:ArithmeticShiftRight": "T-ops",
    "BinaryExpression:Multiply": "T-ops",
    "VariableSymbol:2state": "T-ops",
    "UninstantiatedDefSymbol:UninstantiatedDef": "T-hier",
    "MemberAccessExpression": "T-struct",
    "TypeAliasType:TypeAlias": "T-struct",
    "VariableSymbol:type": "T-struct",
    "InvalidExpression": "vendor",
    "ContinuousAssignSymbol:InvalidExpression": "vendor",
}
TIER_LADDER = ("T-select", "T-reset", "T-case", "T-ops", "T-hier",
               "T-struct")

# Short labels for blocker classes in the markdown table.
SHORT = {
    "AssignmentExpression:target": "lhs-select",
    "ElementSelectExpression": "bit-index",
    "RangeSelectExpression": "part-select",
    "ReplicationExpression": "replication",
    "CaseStatement": "case",
    "TimedStatement:EventListControl": "event-list",
    "UninstantiatedDefSymbol:UninstantiatedDef": "instance",
    "CallExpression": "$signed-call",
    "ConversionExpression:width": "width-conv",
    "ConversionExpression:Explicit": "explicit-cast",
    "UnaryExpression:BitwiseOr": "reduce-or",
    "BinaryExpression:LogicalShiftLeft": "shl",
    "BinaryExpression:ArithmeticShiftRight": "ashr",
    "BinaryExpression:Multiply": "mul",
    "VariableSymbol:2state": "2state-var",
    "VariableSymbol:type": "var-type",
    "MemberAccessExpression": "struct-field",
    "TypeAliasType:TypeAlias": "type-alias",
    "ProceduralBlockSymbol:AlwaysLatch": "always_latch",
    "InvalidExpression": "vendor-invalid",
    "ContinuousAssignSymbol:InvalidExpression": "vendor-invalid-assign",
}

# Files skipped-with-reason (still censused; excluded from the provable
# residual because their unresolved names need the vendored FPU tree).
SKIP_REASON = {
    "rtl/cv32e40p_fp_wrapper.sv":
        "needs vendored fpnew tree (rtl/vendor/pulp_platform_fpnew): "
        "fpnew_pkg types/instances do not resolve; envelope still emitted, "
        "its Invalid* nodes are name-resolution artifacts, not vocabulary "
        "gaps",
}

# Cross-cutting state-shape tier: files whose architectural state is a
# word-array (memory), needing array-state semantics on the Lean side in
# addition to the blocker-derived tiers.
ARRAY_FILES = {
    "rtl/cv32e40p_fifo.sv",
    "rtl/cv32e40p_register_file_ff.sv",
    "rtl/cv32e40p_register_file_latch.sv",
    "rtl/cv32e40p_hwloop_regs.sv",
    "rtl/cv32e40p_cs_registers.sv",
}

# Spec sketch one-liners. **jewel** marks specs that become
# forall-parameter theorems (the program's crown jewels). "contract-only"
# = no file-local functional spec; the file's truth is its interface
# contract inside the core-level composition (phase 3+).
SPEC_SKETCH = {
    "rtl/cv32e40p_aligner.sv":
        "aligner FSM: reconstructs the 32-bit instruction stream from "
        "16-bit-granular fetches — concrete functional spec",
    "rtl/cv32e40p_alu.sv":
        "per-op functional spec at W=32 (shifts, compare, min/max, "
        "shuffle, bit-manip); div/rem delegated to alu_div — concrete",
    "rtl/cv32e40p_alu_div.sv":
        "**forall C_WIDTH** serial div/rem transaction: after the "
        "handshake, quotient/remainder of the operands — **jewel**",
    "rtl/cv32e40p_apu_disp.sv":
        "dispatcher: no lost/duplicated APU transactions, hazard flags "
        "sound — invariant spec",
    "rtl/cv32e40p_compressed_decoder.sv":
        "RVC expansion function: each 16-bit instruction maps to its "
        "32-bit equivalent, illegal iff outside the table — concrete",
    "rtl/cv32e40p_controller.sv":
        "pipeline control FSM — contract-only, no file-local spec",
    "rtl/cv32e40p_core.sv":
        "hierarchical composition — contract-only (wiring, needs T-hier)",
    "rtl/cv32e40p_cs_registers.sv":
        "per-CSR read/write semantics; hwloop CSR family **forall "
        "N_HWLP** — partial jewel",
    "rtl/cv32e40p_decoder.sv":
        "decode table: each instruction class maps to its documented "
        "control bundle; illegal-instruction soundness — concrete",
    "rtl/cv32e40p_ex_stage.sv":
        "EX-stage mux + writeback arbitration — contract-only",
    "rtl/cv32e40p_ff_one.sv":
        "**forall LEN**: first_one_o = index of lowest set bit; "
        "no_ones_o iff input = 0 — **jewel**",
    "rtl/cv32e40p_fifo.sv":
        "**forall DEPTH/WIDTH/FALL_THROUGH**: order-preserving bounded "
        "queue (push/pop trace equality) — **jewel**",
    "rtl/cv32e40p_fp_wrapper.sv":
        "SKIPPED: " + SKIP_REASON["rtl/cv32e40p_fp_wrapper.sv"],
    "rtl/cv32e40p_hwloop_regs.sv":
        "**forall N_REGS**: loop {start,end,cnt} write/read; counter "
        "decrement exact — **jewel**",
    "rtl/cv32e40p_id_stage.sv":
        "decode/issue stage — contract-only, no file-local spec",
    "rtl/cv32e40p_if_stage.sv":
        "fetch stage — contract-only, no file-local spec",
    "rtl/cv32e40p_int_controller.sv":
        "highest-priority pending&enabled irq selection over the 32 "
        "lines — concrete",
    "rtl/cv32e40p_load_store_unit.sv":
        "misaligned-access split + sign/zero-extension of rdata — "
        "concrete data-path spec; OBI handshake contract",
    "rtl/cv32e40p_mult.sv":
        "signed/unsigned 32x32 multiply + dot-product/MAC — concrete",
    "rtl/cv32e40p_obi_interface.sv":
        "**forall TRANS_STABLE**: OBI address-phase stability + "
        "request/response pairing — **jewel** (protocol)",
    "rtl/cv32e40p_popcnt.sv":
        "popcount = sum of bits via adder tree at W=32 — concrete "
        "(generate-tree induction)",
    "rtl/cv32e40p_prefetch_buffer.sv":
        "controller+FIFO composition — contract-only (needs T-hier)",
    "rtl/cv32e40p_prefetch_controller.sv":
        "**forall DEPTH**: outstanding-transaction counter invariant; "
        "fetch FIFO never overflows — **jewel**",
    "rtl/cv32e40p_register_file_ff.sv":
        "**forall ADDR_WIDTH/DATA_WIDTH**: read-after-write register "
        "file, x0 hardwired to 0 — **jewel**",
    "rtl/cv32e40p_register_file_latch.sv":
        "same regfile contract as _ff (equivalence corollary) — "
        "**jewel**",
    "rtl/cv32e40p_sleep_unit.sv":
        "clock-gate handshake: core clock off only when quiescent — "
        "contract",
    "rtl/cv32e40p_top.sv":
        "top-level composition — contract-only (needs T-hier)",
}

# Disposition notes for baseline blocker classes absorbed by the symbolic
# vocabulary (before -> after global table).
ABSORBED_BY = {
    "ParameterSymbol:Parameter": "ParameterDecl/LocalParam (symbolic)",
    "NamedValueExpression:Parameter": "ParamRef (symbolic)",
    "GenerateBlockArraySymbol:GenerateBlockArray":
        "GenerateFor (one structural node, never unrolled)",
    "GenerateBlockSymbol:GenerateBlock": "GenerateIf / generate-for body",
    "GenvarSymbol:Genvar": "GenvarRef (symbolic)",
    "WildcardImportSymbol:WildcardImport": "Import (packages resolve)",
    "TransparentMemberSymbol:TransparentMember":
        "EnumType members (metadata, never folded)",
    "VariableSymbol:range": "symbolic PackedType bounds (ParamRef)",
    "PortSymbol:range": "symbolic PackedType bounds (ParamRef)",
    "PortSymbol:2state": "package/enum-typed ports now resolve",
    "InvalidStatement": "package-typed statements now bind",
    "ProceduralBlockSymbol:NoEventControl":
        "processes bind once package types resolve",
}


def walk_counts(node, kinds, unsupported):
    if isinstance(node, dict):
        k = node.get("kind")
        if k is not None:
            kinds[k] += 1
            if k == "Unsupported":
                unsupported[node.get("sv_kind", "?")] += 1
        for v in node.values():
            walk_counts(v, kinds, unsupported)
    elif isinstance(node, list):
        for v in node:
            walk_counts(v, kinds, unsupported)


def census_file(root, rel, tmpdir):
    top = os.path.basename(rel)[:-3]
    sources = [os.path.join(root, p) for p in PKG_FILES]
    sources.append(os.path.join(root, rel))
    out = os.path.join(tmpdir, top + ".json")
    try:
        try:
            extract.process_symbolic(top, sources, [], out)
        except extract.ExtractError as exc:
            # File basename != declared module name (e.g. the two
            # register_file variants both declare cv32e40p_register_file):
            # retry with the sole non-package top instance if unambiguous.
            msg = str(exc)
            if "no such module among top instances (" not in msg:
                raise
            cands = [c.strip() for c in
                     msg.split("(", 1)[1].rstrip(")").split(",")]
            if len(cands) != 1 or not cands[0]:
                raise
            top = cands[0]
            out = os.path.join(tmpdir, os.path.basename(rel)[:-3] + ".json")
            extract.process_symbolic(top, sources, [], out)
        with open(out, "r", encoding="utf-8") as f:
            env = json.load(f)
    except Exception as exc:
        return {"file": rel, "top": top, "error": "%s: %s"
                % (type(exc).__name__, str(exc)[:200])}
    kinds = Counter()
    unsupported = Counter()
    walk_counts(env["design"], kinds, unsupported)
    nodes_total = sum(kinds.values())
    symbolic_total = sum(kinds.get(k, 0) for k in SYMBOLIC_CLASS)
    unsupported_total = sum(unsupported.values())
    tiers = sorted({TIER_OF.get(k, "T-?") for k in unsupported})
    if rel in ARRAY_FILES:
        tiers.append("T-array")
    sha = None
    for sf in env.get("source_files", []):
        if sf.get("path", "").endswith(os.path.basename(rel)):
            sha = sf.get("sha256")
    rec = {
        "file": rel,
        "top": top,
        "error": None,
        "source_sha256": sha,
        "nodes_total": nodes_total,
        "concrete_total": nodes_total - symbolic_total - unsupported_total,
        "symbolic_total": symbolic_total,
        "unsupported_total": unsupported_total,
        "unsupported": dict(sorted(unsupported.items())),
        "tiers": tiers,
        "kinds": dict(sorted(kinds.items())),
        "packages": env.get("packages", []),
    }
    if rel in SKIP_REASON:
        rec["skip_reason"] = SKIP_REASON[rel]
    return rec


def baseline_m0(root, rels, tmpdir):
    """Single-file M0 mode (byte-preserved pre-phase behavior) over the
    same files: the honest 'before' column."""
    m0dir = os.path.join(tmpdir, "m0")
    os.makedirs(m0dir, exist_ok=True)
    total = Counter()
    per_file = {}
    for rel in rels:
        src = os.path.join(m0dir, os.path.basename(rel))
        shutil.copy(os.path.join(root, rel), src)
        extract.process_file(src)
        with open(src + ".json", "r", encoding="utf-8") as f:
            env = json.load(f)
        kinds = Counter()
        unsupported = Counter()
        walk_counts(env["design"], kinds, unsupported)
        per_file[rel] = sum(unsupported.values())
        total += unsupported
    return {
        "mode": "M0 single-file (pre-phase behavior, byte-preserved)",
        "unsupported_total": sum(total.values()),
        "unsupported_by_kind": dict(sorted(
            total.items(), key=lambda kv: (-kv[1], kv[0]))),
        "per_file_unsupported": dict(sorted(per_file.items())),
    }


def git_commit(root):
    try:
        out = subprocess.run(
            ["git", "-C", root, "rev-parse", "HEAD"],
            capture_output=True, text=True, timeout=30)
        if out.returncode == 0:
            return out.stdout.strip()
    except OSError:
        pass
    return None


def ladder(records):
    """Cumulative unlock schedule over the blocker-derived tiers."""
    rows = []
    cleared = set()
    provable = [r for r in records
                if not r.get("error") and "skip_reason" not in r]
    tier_nodes = Counter()
    tier_files = Counter()
    for r in records:
        if r.get("error"):
            continue
        seen = set()
        for k, n in r.get("unsupported", {}).items():
            t = TIER_OF.get(k, "T-?")
            tier_nodes[t] += n
            seen.add(t)
        for t in seen:
            tier_files[t] += 1
    have = set()
    for tier in TIER_LADDER:
        have.add(tier)
        newly = []
        for r in provable:
            if r["file"] in cleared:
                continue
            need = {TIER_OF.get(k, "T-?") for k in r["unsupported"]}
            if need <= have:
                newly.append(os.path.basename(r["file"])[:-3]
                             .replace("cv32e40p_", ""))
                cleared.add(r["file"])
        rows.append({
            "tier": tier,
            "residual_nodes": tier_nodes.get(tier, 0),
            "files_touched": tier_files.get(tier, 0),
            "newly_cleared": newly,
            "cumulative_cleared": len(cleared),
        })
    return rows, dict(sorted(tier_nodes.items())), \
        dict(sorted(tier_files.items()))


def md_replace(md, marker, table):
    b = "<!-- %s:begin -->" % marker
    e = "<!-- %s:end -->" % marker
    i, j = md.index(b), md.index(e)
    return md[:i + len(b)] + "\n" + table + "\n" + md[j:]


def gen_md(path, records, base, ladder_rows, after_by_kind):
    # 1. The scoreboard table.
    lines = ["| file | nodes | concrete | symbolic | Unsupported "
             "(top classes) | tier needed | spec sketch |",
             "|---|---|---|---|---|---|---|"]
    for r in records:
        name = os.path.basename(r["file"])
        if r.get("error"):
            lines.append("| `%s` | error | | | `%s` | | |"
                         % (name, r["error"]))
            continue
        blockers = ", ".join(
            "%s×%d" % (SHORT.get(t, t), n) for t, n in sorted(
                r["unsupported"].items(),
                key=lambda kv: (-kv[1], kv[0]))[:3]) or "—"
        tiers = "+".join(t.replace("T-", "")
                         for t in r["tiers"]) if r["tiers"] else "—"
        lines.append("| `%s` | %d | %d | %d | **%d** — %s | %s | %s |" % (
            name, r["nodes_total"], r["concrete_total"],
            r["symbolic_total"], r["unsupported_total"], blockers,
            ("T-" + tiers) if r["tiers"] else "—",
            SPEC_SKETCH.get(r["file"], "")))
    scoreboard = "\n".join(lines)

    # 2. Global blockers before -> after.
    keys = sorted(set(base["unsupported_by_kind"]) | set(after_by_kind),
                  key=lambda k: (-after_by_kind.get(k, 0),
                                 -base["unsupported_by_kind"].get(k, 0), k))
    lines = ["| blocker class | before (M0) | after (symbolic) | "
             "disposition |", "|---|---|---|---|"]
    for k in keys:
        b = base["unsupported_by_kind"].get(k, 0)
        a = after_by_kind.get(k, 0)
        if a == 0:
            disp = "absorbed: " + ABSORBED_BY.get(k, "symbolic vocabulary")
        elif k in TIER_OF and TIER_OF[k] == "vendor":
            disp = "fp_wrapper only (vendor fpnew — skipped)"
        else:
            disp = TIER_OF.get(k, "T-?")
            if a > b:
                disp += " (grows: generate bodies/package-typed regions " \
                        "now visible)"
        lines.append("| `%s` | %d | %d | %s |" % (k, b, a, disp))
    lines.append("| **total** | **%d** | **%d** | |"
                 % (base["unsupported_total"],
                    sum(after_by_kind.values())))
    blockers = "\n".join(lines)

    # 3. The ladder.
    lines = ["| tier (cumulative) | residual nodes | files touched | "
             "newly fully cleared | cumulative cleared (of 26 provable) |",
             "|---|---|---|---|---|"]
    for row in ladder_rows:
        lines.append("| %s | %d | %d | %s | %d |" % (
            "+ " + row["tier"] if row is not ladder_rows[0] else row["tier"],
            row["residual_nodes"], row["files_touched"],
            ", ".join(row["newly_cleared"]) or "—",
            row["cumulative_cleared"]))
    lad = "\n".join(lines)

    with open(path, "r", encoding="utf-8") as f:
        md = f.read()
    md = md_replace(md, "census", scoreboard)
    md = md_replace(md, "blockers", blockers)
    md = md_replace(md, "ladder", lad)
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(md)


def main(argv=None):
    ap = argparse.ArgumentParser(prog="cv32e40p_census.py",
                                 description=__doc__)
    ap.add_argument("root", help="cv32e40p checkout (contains rtl/)")
    ap.add_argument("--out-json", default="docs/cv32e40p-census.json")
    ap.add_argument("--out-md", default=None,
                    help="also regenerate the scoreboard/blockers/ladder "
                    "tables in this markdown file (between the markers)")
    ap.add_argument("--tmpdir", default=None)
    args = ap.parse_args(argv)

    rtl = os.path.join(args.root, "rtl")
    rels = sorted(
        "rtl/" + fn for fn in os.listdir(rtl)
        if fn.endswith(".sv") and os.path.isfile(os.path.join(rtl, fn)))
    tmpdir = args.tmpdir or os.path.join(args.root, ".census-envelopes")
    os.makedirs(tmpdir, exist_ok=True)

    records = [census_file(args.root, rel, tmpdir) for rel in rels]
    base = baseline_m0(args.root, rels, tmpdir)

    total_unsup = Counter()
    vendor_files_unsup = 0
    for r in records:
        for k, n in r.get("unsupported", {}).items():
            total_unsup[k] += n
        if "skip_reason" in r:
            vendor_files_unsup += r.get("unsupported_total", 0)
    vendor_nodes = sum(n for k, n in total_unsup.items()
                       if TIER_OF.get(k) == "vendor")
    sym_use = Counter()
    for r in records:
        for k in SYMBOLIC_KINDS:
            sym_use[k] += r.get("kinds", {}).get(k, 0)
    ladder_rows, tier_nodes, tier_files = ladder(records)
    after_by_kind = dict(sorted(
        total_unsup.items(), key=lambda kv: (-kv[1], kv[0])))

    out = {
        "schema": "cv32e40p-census-2",
        "extractor_schema": extract.SYM_SCHEMA_VERSION,
        "frontend": extract.FRONTEND,
        "checkout_git_commit": git_commit(args.root),
        "files": len(records),
        "skipped_files": sorted(SKIP_REASON),
        "clean_files": sum(
            1 for r in records if r.get("unsupported_total") == 0),
        "error_files": sum(1 for r in records if r.get("error")),
        "totals": {
            "nodes": sum(r.get("nodes_total", 0) for r in records),
            "concrete": sum(r.get("concrete_total", 0) for r in records),
            "symbolic": sum(r.get("symbolic_total", 0) for r in records),
            "unsupported": sum(total_unsup.values()),
            "unsupported_semantic": sum(total_unsup.values()) - vendor_nodes,
            "unsupported_excl_skipped":
                sum(total_unsup.values()) - vendor_files_unsup,
        },
        "baseline_m0": base,
        "unsupported_by_kind": after_by_kind,
        "tier_of": dict(sorted(TIER_OF.items())),
        "tier_nodes": tier_nodes,
        "tier_files": tier_files,
        "ladder": ladder_rows,
        "symbolic_vocabulary_use": dict(sorted(sym_use.items())),
        "records": records,
    }
    with open(args.out_json, "w", encoding="utf-8", newline="\n") as f:
        json.dump(out, f, indent=1)
        f.write("\n")
    print("wrote %s (%d files; M0 baseline %d -> symbolic residual %d "
          "unsupported nodes)"
          % (args.out_json, len(records), base["unsupported_total"],
             sum(total_unsup.values())))

    if args.out_md:
        gen_md(args.out_md, records, base, ladder_rows, after_by_kind)
        print("updated %s" % args.out_md)
    return 0


if __name__ == "__main__":
    sys.exit(main())
