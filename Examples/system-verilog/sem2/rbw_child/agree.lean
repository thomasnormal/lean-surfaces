/-
Examples/system-verilog/sem2/rbw_child — a self-reading `always_comb` inside
a CHILD instance (`t[0] = a; y = t[1]; t[1] = b;` in `rbw_child_leaf`,
instantiated as `u` by `rbw_child`), REFUSED at ingestion by the always_comb
self-read guard (WP4, 2026-10-28, `LeanModels/Sv/CombGuard2.lean`), with a
message that names the instance, the child module and the flattened signal
prefix (`Process2.inInstance`, `LeanModels/Sv/Hier2.lean`; WP4 round 3).
The `harness/sv/cases2.json` row `rbw_child` is a loud-refusal row
(`AlwaysComb:self-read`).

  rbw_child.sv      — the SystemVerilog source
  rbw_child.sv.json — generated envelope (extractors/sv/extract.py --top)
  agree.lean — THIS FILE: `load_design_sv2` refuses the envelope, and the
               flattened design at the defaults carries the child's refusal
               under the instance's name
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.rbw_child.agree

open LeanModels.Sv

/--
error: load_design_sv2: 'Examples/system-verilog/sem2/rbw_child/rbw_child.sv.json' REFUSED — at the defaults, in the instantiated design of module 'rbw_child': in instance 'u' of module 'rbw_child_leaf' (its signals flatten under the prefix 'u.' inside the module that instantiates it): always_comb block reads bit [1] of 't' before writing it on some path through its body, and writes it later on that path: IEEE 1800-2023 §9.2.2.2.1 leaves the variables a block writes out of its implicit sensitivity list, so an event-driven simulator runs the block once per wake-up and that read sees the PREVIOUS run's value (Icarus 12, Xcelium), while the settle semantics re-runs the block to its fixpoint (as Verilator 5.042 and Yosys 0.53 do): no answer is safe, so the block is refused (write the bits before every read of them, or move the read after the last write) (`AlwaysComb:self-read`, `Stmt2.combAdmits`)
-/
#guard_msgs (whitespace := lax) in
load_design_sv2 rbw_child from "Examples/system-verilog/sem2/rbw_child/rbw_child.sv.json"

/-- The hierarchy flattened at its defaults (`PDesign.instantiateH`, the
family `name.sem` uses for an instantiating top). -/
def flattened : IO Design2 := do
  let text ← IO.FS.readFile "Examples/system-verilog/sem2/rbw_child/rbw_child.sv.json"
  match loadHierString text with
  | .error e => throw (IO.userError s!"envelope: {e}")
  | .ok (pd, lib) =>
    match pd.instantiateH lib [] (PDesign.surfaceFuel []) with
    | .ok d => pure d
    | .timeout => throw (IO.userError "instantiation: timeout")
    | .unsupported m => throw (IO.userError s!"instantiation: {m}")

/-! Exactly one process of the flattened design is loud: the guard's
refusal of the child's block, on `t[1]` (`selfReadMsg ("t", 1, 1)`), under
the instance `u` of `rbw_child_leaf` (prefix `u.`). The `#eval` throws (and
fails the build) on any difference. -/

#eval show IO Unit from do
  let d ← flattened
  unless d.name == "rbw_child" do throw (IO.userError "name differs")
  let loud := d.processes.toList.filter fun
    | .unsupported _ _ => true
    | _ => false
  let want := Process2.unsupported "AlwaysComb:self-read"
    ("in instance 'u' of module 'rbw_child_leaf' (its signals flatten under the prefix 'u.' inside the module that instantiates it): "
      ++ selfReadMsg ("t", 1, 1))
  unless toString (repr loud) == toString (repr [want]) do
    throw (IO.userError s!"the loud processes are not the guard's instance-named refusal: {repr loud}")
  unless d.decls.toList.any (·.name == "u.t") do
    throw (IO.userError "the child's `t` is not flattened as `u.t`")

end Examples.«system-verilog».sem2.rbw_child.agree
