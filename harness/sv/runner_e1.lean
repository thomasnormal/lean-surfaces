/-
# SV E-core-1 differential runner

This runner keeps the retained `always_ff`/plain `always` source nodes and
executes them through the E-core-1 Active/NBA slot semantics.  It is separate
from the E-core-0 array runner: edge bodies are not lowered to combinational
processes and their source event remains in `Elab1`.
-/
import Lean
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.RunE1
import LeanModels.Sv.Kernel.Core1Elab

open Lean (Json)
open LeanModels.Sv
open LeanModels.Sv.Kernel

namespace SvHarnessE1

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
  | .ok s => pure s
  | .error _ => .error s!"field '{name}' is not a string"

def getArrF (j : Json) (name : String) : Except String (Array Json) := do
  match (← getF j name).getArr? with
  | .ok a => pure a
  | .error _ => .error s!"field '{name}' is not an array"

def findCase (cases : Array Json) (name : String) : Except String Json := do
  for c in cases do
    if (← getStrF c "name") == name then return c
  .error s!"case '{name}' not found"

def resolvePoint (pd : PDesign) (paramsJ : Option Json) :
    Except String (PDesign × List Int) :=
  pd.atPoint <| pd.params.map fun p =>
    match paramsJ with
    | none => none
    | some pj =>
        match pj.getObjVal? p.name with
        | .ok v => v.getInt?.toOption
        | .error _ => none

def caseOverrides (paramsJ : Option Json) : List (String × Int) :=
  match paramsJ with
  | some (.obj kvs) =>
      kvs.toArray.toList.filterMap fun (n, v) =>
        v.getInt?.toOption.map (n, ·)
  | _ => []

def renderOverrides (xs : List (String × Int)) : String :=
  String.intercalate "," (xs.map fun (n, v) => s!"{n}={v}")

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
        unless dc.isInput do
          .error s!"stimulus '{name}': not an input port"
        unless lv.width == dc.width do
          .error s!"stimulus '{name}': width {lv.width} ≠ port width {dc.width}"
        st := st ++ [(name, lv)]
      pure st
  | _ => .error "stimulus entry is not an object"

def stimulusArray (case : Json) : Except String (Array Json) := do
  match case.getObjVal? "stimulus_by_params" with
  | .error _ => getArrF case "stimulus"
  | .ok table =>
      let key := renderOverrides (caseOverrides (getFOpt case "params"))
      match table.getObjVal? key with
      | .ok value =>
          match value.getArr? with
          | .ok entries => pure entries
          | .error _ => .error s!"stimulus_by_params '{key}' is not an array"
      | .error _ => .error s!"stimulus_by_params has no point '{key}'"

def sigmaOf : String → Except String ScheduleOracle
  | "src" => .ok σ_src
  | "rev" => .ok σ_rev
  | s => .error s!"unknown sigma '{s}' (want src|rev)"

end SvHarnessE1

open SvHarnessE1 in
def main (argv : List String) : IO UInt32 := do
  let err (msg : String) : IO UInt32 := do
    (← IO.getStderr).putStrLn s!"ERROR: {msg}"
    return 1
  match argv with
  | [envPath, casesPath, caseName, sigmaName] => do
      let envText ← IO.FS.readFile ⟨envPath⟩
      let casesText ← IO.FS.readFile ⟨casesPath⟩
      let r : Except String (Design2 × List SvState × List String × Nat × String × Elab1) := do
        let (pd, lib) ← loadHierString envText
        match pd.crossCheck with
        | [] => pure ()
        | msgs => .error s!"crossCheck REFUSED: {String.intercalate " | " msgs}"
        for c in lib do
          match c.crossCheck with
          | [] => pure ()
          | msgs => .error s!"crossCheck REFUSED (module '{c.name}'): {String.intercalate " | " msgs}"
        let cj ← Json.parse casesText
        let fuel := (getFOpt cj "fuel").bind (·.getNat?.toOption) |>.getD 1000
        let case ← findCase (← getArrF cj "cases") caseName
        let clock ← getStrF case "clock"
        let (pd, args) ← resolvePoint pd (getFOpt case "params")
        unless (if lib.isEmpty then pd.int32Agrees args else pd.int32AgreesH lib args) do
          .error "int32: an INT-class constant expression leaves the 32-bit range at these parameters"
        let d ← do
          let flatTop := lib.isEmpty || GenItem.listInstFree pd.generates
          let inst := if flatTop then
              if pd.functions.isEmpty then pd.instantiateG2 args (PDesign.surfaceFuel args)
              else pd.instantiateFunctionsG2 args (PDesign.surfaceFuel args)
            else pd.instantiateH lib args (PDesign.surfaceFuel args)
          match inst with
          | .ok d => pure d
          | .timeout => .error "instantiate2: generate fuel exhausted"
          | .unsupported m => .error s!"instantiate2: {m}"
        unless d.namesNodup do
          .error "instantiate2: two declarations of one name after flattening"
        match d.clockViolation with
        | some (kind, text) => .error s!"{kind}: {text}"
        | none => pure ()
        let E ← match Elab1.ofEdgeDesign2 d with
          | .ok E => pure E
          | .error m => .error m
        let entries ← (← stimulusArray case).toList.mapM (parseEntry d)
        let signals ← (← getArrF case "signals").toList.mapM (fun s => s.getStr?)
        pure (d, entries, signals, fuel, clock, E)
      match r with
      | .error e => err e
      | .ok (d, entries, signals, fuel, clock, E) =>
          let σ ← match sigmaOf sigmaName with
            | .ok σ => pure σ
            | .error e => return (← err e)
          let out ← IO.getStdout
          for dc in d.decls do
            let sign := if dc.isSigned then "signed" else "unsigned"
            if dc.isInput then out.putStrLn s!"PORT {dc.name} in {dc.width} {sign}"
            else if dc.isOutput then out.putStrLn s!"PORT {dc.name} out {dc.width} {sign}"
          match runE1 E σ fuel clock entries with
          | .timeout => err "E-core-1: timeout (executor fuel exhausted)"
          | .unsupported m => err s!"E-core-1: unsupported: {m}"
          | .ok rows =>
              for (row, k) in rows.zipIdx do
                let st := E.base.view row.2.store
                let cells := signals.map fun s => s!"{s}={SvState.showSignal st s}"
                out.putStrLn (s!"CYCLE {k} " ++ " ".intercalate cells)
              return 0
  | _ => err "usage: runner_e1.lean <envelope.sv.json> <cases2.json> <case> <src|rev>"
