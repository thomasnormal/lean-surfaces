/-
Examples/system-verilog/sem2/addsub_comb — the differential fixture of the
N-bit adder/subtractor with a zero flag written as one always_comb
(`harness/sv/cases2.json` rows `addsub_comb`, `addsub_comb_n1`,
`addsub_comb_n8`: `run2` of THIS envelope against Icarus), tied to the
hand-built design family `asDesign N` of `LeanModels/Sv/Comb2ProcExample.lean`
(`as_correct`, `as_terminates`, for every `N`).

  addsub_comb.sv      — the SystemVerilog source, `parameter N`
  addsub_comb.sv.json — generated envelope (extractors/sv/extract.py --top)
  agree.lean          — THIS FILE: the instantiated design IS `asDesign N`
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Comb2ProcExample
import LeanModels.Sv.CombAlias2Example

/-!
# The SV source instantiates to the proved design family

`load_design_sv2` turns the envelope into the family `addsub_comb.sem N`. At
every width checked below its name and declarations are exactly
`asDesign N`'s, its process list prints exactly as `asDesign N`'s
(`Process2` derives no `BEq`), and its `always_comb` body symbolically
executes to `asSym N`, the equations `as_correct` is proved from. These are
`#guard` evaluations at concrete widths (`N = 1, 2, 4, 8, 32`), not a
symbolic-`N` instantiation theorem (`Gen2.lean`'s recipe would give one).
-/

namespace Examples.«system-verilog».sem2.addsub_comb.agree

open LeanModels.Sv LeanModels.Sv.Comb2ProcExample

load_design_sv2 addsub_comb from "Examples/system-verilog/sem2/addsub_comb/addsub_comb.sv.json"

/-- The instantiated design at width `N` is `asDesign N`, and lowers to `asSym N`. -/
def same (N : Nat) : Bool :=
  (addsub_comb.sem N).name == (asDesign N).name &&
  (addsub_comb.sem N).decls.toList == (asDesign N).decls.toList &&
  toString (repr (addsub_comb.sem N).processes) == toString (repr (asDesign N).processes) &&
  -- the always_comb alias guard (`CombAlias2.lean`) leaves the design unchanged
  toString (repr (addsub_comb.sem N).aliasGuard.processes) ==
    toString (repr (addsub_comb.sem N).processes) &&
  match (addsub_comb.sem N).processes.toList with
  | [.alwaysComb body] => body.symExec (addsub_comb.sem N) [] == some (asSym N)
  | _ => false

#guard [1, 2, 4, 8, 32].all same

end Examples.«system-verilog».sem2.addsub_comb.agree
