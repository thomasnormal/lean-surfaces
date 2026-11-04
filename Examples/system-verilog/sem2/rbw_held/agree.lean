/-
Examples/system-verilog/sem2/rbw_held — the always_comb held-value self-read `if (c) t = a; y = t; t = b;`, REFUSED at
ingestion by the always_comb self-read guard (WP4, 2026-10-28,
`LeanModels/Sv/CombGuard2.lean`).
Tied to the hand-built design `heldDesign` of
`LeanModels/Sv/Comb2ProcExample.lean` (`held_guard`, `held_refused`). The
`harness/sv/cases2.json` row `rbw_held` is a loud-refusal row
(`AlwaysComb:self-read`). Measured before the guard, on its stimulus
(c, a, b) = (0, 00, 01) (0, 00, 10) (1, 11, 10): Icarus 12 and Xcelium y = 01 01 11, the settle semantics
(and Verilator 5.042, Yosys 0.53) y = 01 10 11 — IEEE 1800-2023 §9.2.2.2.1
sides with Icarus, the synthesized netlist with the settle answer, so no
answer is safe (retired declared divergence `sv-div-3`,
`docs/sv-declared-divergences.json`).

  rbw_held.sv      — the SystemVerilog source
  rbw_held.sv.json — generated envelope (extractors/sv/extract.py --top)
  agree.lean — THIS FILE: `load_design_sv2` refuses the envelope, and its
               instantiation is `heldDesign`'s declarations with the
               guard's refusal of `heldDesign`'s body as its one process
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Comb2ProcExample

/-!
# The SV source is refused at ingestion

`load_design_sv2` refuses the envelope at its defaults with the guard's
message (pinned verbatim below). The instantiation `name.sem` would compute
(`PDesign.instantiateG2`, the family of a flat envelope) has exactly
`heldDesign`'s declarations and ONE process: the loud
`AlwaysComb:self-read` process the guard puts in place of `heldBody`
(`held_guard`). The lowering refuses the body as well (`held_refused`):
nothing about it is proved through the always_comb settle theorem.
-/

namespace Examples.«system-verilog».sem2.rbw_held.agree

open LeanModels.Sv LeanModels.Sv.Comb2ProcExample

/--
error: load_design_sv2: 'Examples/system-verilog/sem2/rbw_held/rbw_held.sv.json' REFUSED — at the defaults, in the instantiated design of module 'rbw_held': always_comb block reads bits [1:0] of 't' before writing them on some path through its body, and writes them later on that path: IEEE 1800-2023 §9.2.2.2.1 leaves the variables a block writes out of its implicit sensitivity list, so an event-driven simulator runs the block once per wake-up and that read sees the PREVIOUS run's value (Icarus 12, Xcelium), while the settle semantics re-runs the block to its fixpoint (as Verilator 5.042 and Yosys 0.53 do): no answer is safe, so the block is refused (write the bits before every read of them, or move the read after the last write) (`AlwaysComb:self-read`, `Stmt2.combAdmits`)
-/
#guard_msgs (whitespace := lax) in
load_design_sv2 rbw_held from "Examples/system-verilog/sem2/rbw_held/rbw_held.sv.json"

/-- The envelope's instantiation at its defaults: `heldDesign`'s
declarations, and the guard's refusal of its body as the only process. -/
def instantiated : IO Design2 := do
  let text ← IO.FS.readFile "Examples/system-verilog/sem2/rbw_held/rbw_held.sv.json"
  match loadPDesignString text with
  | .error e => throw (IO.userError s!"envelope: {e}")
  | .ok pd =>
    match pd.instantiateG2 [] (PDesign.surfaceFuel []) with
    | .ok d => pure d
    | .timeout => throw (IO.userError "instantiation: timeout")
    | .unsupported m => throw (IO.userError s!"instantiation: {m}")

#eval show IO Unit from do
  let d ← instantiated
  unless d.name == heldDesign.name do throw (IO.userError "name differs")
  unless d.decls.toList == heldDesign.decls.toList do throw (IO.userError "declarations differ")
  unless toString (repr d.processes) ==
      toString (repr #[combGuardProc heldDesign.combWd heldBody]) do
    throw (IO.userError "processes differ from the guard's refusal of the body")
  unless toString (repr d.processes) ==
      toString (repr #[Process2.unsupported "AlwaysComb:self-read" (selfReadMsg ("t", 0, 2))]) do
    throw (IO.userError "the refusal is not the guard's message on t[1:0]")

end Examples.«system-verilog».sem2.rbw_held.agree
