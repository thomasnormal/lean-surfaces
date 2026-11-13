/-
# SV E-core-0 differential runner

The command-line shape matches `runner2.lean`, but the instantiated Design2 is
transported through `Elab.ofDesign2` and evaluated by the E-core-0 array
executor.  E accepts only flat continuous assignments and always_comb bodies;
other processes remain loud through the source-shaped `Unsupported` node.
-/
import Lean
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.RunEArray
import LeanModels.Sv.Kernel.Core0Entry
import LeanModels.Sv.HierarchyNode2

open Lean (Json)
open LeanModels.Sv

namespace SvHarnessE0

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
      kvs.toArray.toList.filterMap fun (n, v) => (v.getInt?.toOption.map (n, ·))
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
        unless dc.isInput do .error s!"stimulus '{name}': not an input port"
        unless lv.width == dc.width do
          .error s!"stimulus '{name}': width {lv.width} ≠ port width {dc.width}"
        st := st ++ [(name, lv)]
      return st
  | _ => .error "stimulus entry is not an object"

def stimulusArray (case : Json) : Except String (Array Json) := do
  match case.getObjVal? "stimulus_by_params" with
  | .error _ => getArrF case "stimulus"
  | .ok table =>
      let key := renderOverrides (caseOverrides (getFOpt case "params"))
      match table.getObjVal? key with
      | .ok value =>
          match value.getArr? with
          | .ok entries => .ok entries
          | .error _ => .error s!"stimulus_by_params '{key}' is not an array"
      | .error _ => .error s!"stimulus_by_params has no point '{key}'"

def sigmaOf : String → Except String ScheduleOracle
  | "src" => .ok σ_src
  | "rev" => .ok σ_rev
  | s => .error s!"unknown sigma '{s}' (want src|rev)"

end SvHarnessE0

open SvHarnessE0 in
def main (argv : List String) : IO UInt32 := do
  let err (msg : String) : IO UInt32 := do
    (← IO.getStderr).putStrLn s!"ERROR: {msg}"
    return 1
  match argv with
  | [envPath, casesPath, caseName, sigmaName] => do
    let envText ← IO.FS.readFile ⟨envPath⟩
    let casesText ← IO.FS.readFile ⟨casesPath⟩
    let r : Except String (Design2 × Option HierNode2 × List SvState × List String × Nat × Option EDesign2) := do
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
      let (pd, args) ← resolvePoint pd (getFOpt case "params")
      unless (if lib.isEmpty then pd.int32Agrees args else pd.int32AgreesH lib args) do
        .error "int32: an INT-class constant expression leaves the 32-bit range at these parameters"
      let sourceHier := match pd.generates with
        | [.inst _] => !lib.isEmpty
        | _ => false
      let (d, node?) ← if sourceHier then
        -- The source-shaped hierarchy executor keeps child processes as
        -- nodes, so its ordinary `Design2.aliasGuard` cannot see aliases
        -- created by parent port connections.  Use the existing flattened
        -- semantic view only to carry that guard across the hierarchy; the
        -- E execution below still uses `HierNode2` and never executes the
        -- flattened design.
        match pd.instantiateH lib args (PDesign.surfaceFuel args) with
        | .ok flat =>
            let guarded := flat.aliasGuard
            if guarded.processes.toList.any (fun p =>
              match p with
              | .unsupported "AlwaysComb:alias-read" _ => true
              | _ => false) then
              .error "AlwaysComb:alias-read: hierarchical continuous-copy alias"
            else if guarded.processes.toList.all (fun p =>
              match p with
              | .assign _ _ | .alwaysComb _ => true
              | _ => false) then
              -- A flattened, alias-guarded comb hierarchy is already in the
              -- ordinary E0 fragment; use it so port-connected wires settle
              -- through the same scheduler as flat continuous assignments.
              pure (guarded, none)
            else
              let node ← match pd.instantiateNode2 lib args with
                | .ok n => pure n
                | .timeout => .error "instantiateNode2: generate fuel exhausted"
                | .unsupported m => .error s!"instantiateNode2: {m}"
              pure (node.core, some node)
        | .timeout =>
            let node ← match pd.instantiateNode2 lib args with
              | .ok n => pure n
              | .timeout => .error "instantiateNode2: generate fuel exhausted"
              | .unsupported m => .error s!"instantiateNode2: {m}"
            pure (node.core, some node)
        | .unsupported _ =>
            let node ← match pd.instantiateNode2 lib args with
              | .ok n => pure n
              | .timeout => .error "instantiateNode2: generate fuel exhausted"
              | .unsupported m => .error s!"instantiateNode2: {m}"
            pure (node.core, some node)
      else
        let flatTop := lib.isEmpty || GenItem.listInstFree pd.generates
        let inst := if flatTop then
          if pd.functions.isEmpty then pd.instantiateG2 args (PDesign.surfaceFuel args)
          else pd.instantiateFunctionsG2 args (PDesign.surfaceFuel args)
        else pd.instantiateH lib args (PDesign.surfaceFuel args)
        let d ← match inst with
          | .ok d => pure d
          | .timeout => .error "instantiate2: generate fuel exhausted"
          | .unsupported m => .error s!"instantiate2: {m}"
        pure (d, none)
      unless d.namesNodup do .error "instantiateH: two declarations of one name after flattening"
      -- Keep the source-shaped alias admission boundary in E-core-0 aligned
      -- with the ordinary loader: IEEE 1800-2023 §§4.7–4.8 leave the update
      -- order of a continuous copy and an always_comb wake-up open, so a
      -- block that reads such a copy before writing its source must refuse.
      let d := d.aliasGuard
      let sourceE := pd.processes.any fun p =>
        match p with | .alwaysImplicit _ => true | _ => false
      match d.clockViolation with
      | some (k, msg) =>
          if k == "Clock:multiple" then
            .error s!"{k}: {msg}"
          else pure ()
      | none => pure ()
      for p in d.processes do
        match p with
        | .unsupported k msg =>
            if k == "AlwaysComb:alias-read" then
              .error s!"{k}: {msg}"
            else if sourceE then pure () else .error s!"{k}: {msg}"
        | .alwaysFF _ _ | .alwaysPlain _ _ =>
            .error "Clock:edge: edge-triggered process is outside E-core-0"
        | .alwaysFFR _ _ _ _ =>
            .error "Clock:async-reset: asynchronous reset process is outside E-core-0"
        | _ => pure ()
      let entries ← (← stimulusArray case).toList.mapM (parseEntry d)
      let signals ← (← getArrF case "signals").toList.mapM (fun s => s.getStr?)
      let eDesign? := if sourceE then some (pd.instantiateDE2 args) else none
      pure (d, node?, entries, signals, fuel, eDesign?)
    match r with
    | .error e => err e
    | .ok (d, node?, entries, signals, fuel, eDesign?) =>
      let σ ← match sigmaOf sigmaName with
        | .ok σ => pure σ
        | .error e => return (← err e)
      let E := match eDesign? with
        | some ed => LeanModels.Sv.Kernel.Elab.ofEDesign2 ed
        | none => LeanModels.Sv.Kernel.Elab.ofDesign2 d
      let out ← IO.getStdout
      for dc in d.decls do
        let sign := if dc.isSigned then "signed" else "unsigned"
        if dc.isInput then out.putStrLn s!"PORT {dc.name} in {dc.width} {sign}"
        else if dc.isOutput then out.putStrLn s!"PORT {dc.name} out {dc.width} {sign}"
      let result := match node? with
        | some node => runHierE0 node σ fuel entries
        | none =>
            match LeanModels.Sv.Kernel.runE0Array E σ fuel entries with
            | .ok rows => .ok (rows.map fun row : LeanModels.Sv.Kernel.E0Row => E.view row.2.store)
            | .timeout => .timeout
            | .unsupported m => .unsupported m
      match result with
      | .timeout => err "E-core-0: timeout (executor fuel exhausted)"
      | .unsupported m => err s!"E-core-0: unsupported: {m}"
      | .ok rows =>
          let mut k := 0
          for st in rows do
            let cells := signals.map fun s => s!"{s}={SvState.showSignal st s}"
            out.putStrLn (s!"CYCLE {k} " ++ " ".intercalate cells)
            k := k + 1
          return 0
  | _ => err "usage: runner_e0.lean <envelope.sv.json> <cases2.json> <case> <src|rev>"
