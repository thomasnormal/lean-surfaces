/-
# SV phase-2 differential-harness runner (semantic tier, sv-0.2)

Executed by `harness/sv/diff_test2.py` as

  lake env lean --run harness/sv/runner2.lean <envelope.sv.json> <cases2.json> <case> <src|rev>

Loads a symbolic sv-0.2 envelope, resolves the case's parameter values
(declaration order; a parameter absent from the case's `params` object
takes its envelope default), instantiates the SEMANTIC tier
(`PDesign.instantiate2` → `Design2`), and prints:

  PORT <name> <in|out> <width>     — one line per port, at THESE parameters
                                     (the TB generator's width source)
  CYCLE <k> <name>=<binary> ...    — one line per stimulus cycle, `run2`
                                     under the requested schedule

Any failure (parse, crossCheck, instantiation, `.timeout`/`.unsupported`)
prints `ERROR: ...` on stderr and exits nonzero. The crossCheck gate is
replayed here exactly as `load_design_sv2` does at elaboration time.
-/

import Lean
import LeanModels.Sv.Ingest2

open Lean (Json)
open LeanModels.Sv

namespace SvHarness2

def getF (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{name}'"

def getFOpt (j : Json) (name : String) : Option Json :=
  match j.getObjVal? name with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

def getStrF (j : Json) (name : String) : Except String String := do
  match (← getF j name).getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"field '{name}' is not a string"

def getArrF (j : Json) (name : String) : Except String (Array Json) := do
  match (← getF j name).getArr? with
  | .ok a => .ok a
  | .error _ => .error s!"field '{name}' is not an array"

def getNatF (j : Json) (name : String) : Except String Nat := do
  match (← getF j name).getNat? with
  | .ok n => .ok n
  | .error _ => .error s!"field '{name}' is not a Nat"

/-- Find the requested case object. -/
def findCase (cases : Array Json) (name : String) : Except String Json := do
  for c in cases do
    if (← getStrF c "name") == name then
      return c
  .error s!"case '{name}' not found"

/-- Resolve the argument vector: envelope parameter order; per-name value
from the case's `params` object, else the parameter's envelope default
(evaluated in order, earlier parameters visible). -/
def resolveArgs (pd : PDesign) (paramsJ : Option Json) : Except String (List Int) := do
  let mut env : IEnv := {}
  let mut args : List Int := []
  for p in pd.params do
    let given : Option Int :=
      match paramsJ with
      | none => none
      | some pj =>
          match pj.getObjVal? p.name with
          | .ok v => v.getInt?.toOption
          | .error _ => none
    let v ← match given with
      | some v => pure v
      | none =>
          match p.default? with
          | none => .error s!"parameter '{p.name}': no case value and no default"
          | some e =>
              match evalInt env e with
              | .ok v => pure v
              | .error msg => .error s!"parameter '{p.name}' default: {msg}"
    env := env.bindVal p.name v
    args := args ++ [v]
  return args

/-- One stimulus entry: `{name: "<MSB-first bits>"}` → `SvState`,
validated against declared input widths. -/
def parseEntry (d : Design2) (j : Json) : Except String SvState := do
  match j with
  | .obj kvs =>
      let mut st : SvState := []
      for (name, v) in kvs.toArray do
        let bits ← match v.getStr? with
          | .ok s => pure s
          | .error _ => .error s!"stimulus '{name}' is not a string"
        let some lv := LVec.ofString? bits
          | .error s!"stimulus '{name}': bad digits {bits}"
        let some dc := d.decls.find? (·.name == name)
          | .error s!"stimulus '{name}': not a declared signal"
        unless dc.isInput do .error s!"stimulus '{name}': not an input port"
        unless lv.width == dc.width do
          .error s!"stimulus '{name}': width {lv.width} ≠ port width {dc.width}"
        st := st ++ [(name, lv)]
      return st
  | _ => .error "stimulus entry is not an object"

def sigmaOf : String → Except String ScheduleOracle
  | "src" => .ok σ_src
  | "rev" => .ok σ_rev
  | s => .error s!"unknown sigma '{s}' (want src|rev)"

end SvHarness2

open SvHarness2 in
def main (argv : List String) : IO UInt32 := do
  let err (msg : String) : IO UInt32 := do
    (← IO.getStderr).putStrLn s!"ERROR: {msg}"
    return 1
  match argv with
  | [envPath, casesPath, caseName, sigmaName] => do
    let envText ← IO.FS.readFile ⟨envPath⟩
    let casesText ← IO.FS.readFile ⟨casesPath⟩
    let r : Except String (Design2 × List SvState × List String × Nat) := do
      let pd ← loadPDesignString envText
      match pd.crossCheck with
      | [] => pure ()
      | msgs => .error s!"crossCheck REFUSED: {String.intercalate " | " msgs}"
      let cj ← Json.parse casesText
      let fuel := (getFOpt cj "fuel").bind (·.getNat?.toOption) |>.getD 1000
      let case ← findCase (← getArrF cj "cases") caseName
      let args ← resolveArgs pd (getFOpt case "params")
      let d ← match pd.instantiate2 args (PDesign.surfaceFuel args) with
        | .ok d => pure d
        | .timeout => .error "instantiate2: generate fuel exhausted"
        | .unsupported m => .error s!"instantiate2: {m}"
      let stim ← (← getArrF case "stimulus").toList.mapM (parseEntry d)
      let signals ← (← getArrF case "signals").toList.mapM (fun s => s.getStr?)
      pure (d, stim, signals, fuel)
    match r with
    | .error e => err e
    | .ok (d, stim, signals, fuel) =>
      let σ ← match sigmaOf sigmaName with
        | .ok σ => pure σ
        | .error e => return (← err e)
      let out ← IO.getStdout >>= pure
      for dc in d.decls do
        if dc.isInput then out.putStrLn s!"PORT {dc.name} in {dc.width}"
        else if dc.isOutput then out.putStrLn s!"PORT {dc.name} out {dc.width}"
      match run2 d σ fuel stim with
      | .timeout => err "run2: timeout (fuel exhausted / comb loop)"
      | .unsupported m => err s!"run2: unsupported: {m}"
      | .ok trace => do
          let mut k := 0
          for st in trace do
            let cells := signals.map fun s => s!"{s}={SvState.showSignal st s}"
            out.putStrLn (s!"CYCLE {k} " ++ " ".intercalate cells)
            k := k + 1
          return 0
  | _ => err "usage: runner2.lean <envelope.sv.json> <cases2.json> <case> <src|rev>"
