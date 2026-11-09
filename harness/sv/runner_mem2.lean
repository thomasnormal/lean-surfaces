/-
Source-shaped one-rank memory runner for the phase-2 differential harness.
It is deliberately separate from runner2: the legacy Design2/SvState view
cannot represent an unpacked cell, while this runner keeps the PDecl and
MemState route intact.  The command-line shape is the same as runner2; the
sigma and optional probe arguments are accepted for harness compatibility.
-/

import Lean
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.MemPreemptGuard

open Lean (Json)
open LeanModels.Sv
open LeanModels.Sv.Kernel

namespace SvMemHarness

def getF (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{name}'"

def getOpt (j : Json) (name : String) : Option Json :=
  match j.getObjVal? name with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

def getStr (j : Json) (name : String) : Except String String := do
  match (← getF j name).getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"field '{name}' is not a string"

def getArr (j : Json) (name : String) : Except String (Array Json) := do
  match (← getF j name).getArr? with
  | .ok a => .ok a
  | .error _ => .error s!"field '{name}' is not an array"

def findCase (cases : Array Json) (name : String) : Except String Json := do
  for c in cases do
    if (← getStr c "name") == name then return c
  .error s!"case '{name}' not found"

def resolvePoint (pd : PDesign) (paramsJ : Option Json) : Except String (PDesign × List Int) :=
  pd.atPoint <| pd.params.map fun p =>
    match paramsJ with
    | some j => (j.getObjVal? p.name).toOption.bind (·.getInt?.toOption)
    | none => none

def parseEntry (d : MemDesign2) (j : Json) : Except String SvState := do
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

def addClock : Option String → Nat → List SvState → List SvState
  | _, _, [] => []
  | none, _, s :: rest => s :: addClock none 0 rest
  | some name, _, s :: rest =>
      -- gen_tb2 drives every row while the clock is low, raises it once,
      -- samples at the following negedge, then starts the next row low.
      -- The memory state therefore sees one rising edge per row.
      SvState.set s name (LVec.ofNat 1 1) :: addClock (some name) 0 rest

def lowAfterSample (clock : String) (st : MemCycleState) : MemCycleState :=
  { st with scalar := SvState.set st.scalar clock (LVec.ofNat 1 0) }

def runMemAtNegedge (d : MemDesign2) (fuel : Nat) (clock : String)
    (st : MemCycleState) : List SvState → Res (List SvState)
  | [] => .ok []
  | input :: rest => do
      let sampled ← memStep d fuel input st
      let next := lowAfterSample clock sampled
      let trace ← runMemAtNegedge d fuel clock next rest
      return next.scalar :: trace

end SvMemHarness

open SvMemHarness in
def main (argv : List String) : IO UInt32 := do
  let err (msg : String) : IO UInt32 := do
    (← IO.getStderr).putStrLn s!"ERROR: {msg}"
    return 1
  let argv := match argv with | [e, c, n, s, _p] => [e, c, n, s] | xs => xs
  match argv with
  | [envPath, casesPath, caseName, _sigma] => do
      let envText ← IO.FS.readFile ⟨envPath⟩
      let casesText ← IO.FS.readFile ⟨casesPath⟩
      let r : Except String (MemDesign2 × List SvState × List String × Nat × String) := do
        let (pd, lib) ← loadHierString envText
        unless lib.isEmpty do .error "memory runner does not admit hierarchy"
        match pd.crossCheck with
        | [] => pure ()
        | msgs => .error s!"crossCheck REFUSED: {String.intercalate " | " msgs}"
        let cj ← Json.parse casesText
        let case ← findCase (← getArr cj "cases") caseName
        let (pd, args) ← resolvePoint pd (getOpt case "params")
        let d ← match instantiateMem2 pd args with
          | .ok d => pure d
          | .timeout => .error "instantiateMem2: timeout"
          | .unsupported m => .error s!"instantiateMem2: {m}"
        -- The source-shaped memory cycle is process-atomic, while IEEE
        -- 1800-2023 §4.7 permits mid-process suspension.  Guard this route
        -- before executing it; `runMem2` remains the low-level executor.
        if let some (k, msg) := d.memoryPreemptionReport then
          .error s!"{k}: {msg}"
        let stim0 ← (← getArr case "stimulus").toList.mapM (parseEntry d)
        let clock := (getOpt case "clock").bind (·.getStr?.toOption)
        let stim := addClock clock 0 stim0
        let signals ← (← getArr case "signals").toList.mapM (·.getStr?)
        let fuel := (getOpt cj "fuel").bind (·.getNat?.toOption) |>.getD 1000
        pure (d, stim, signals, fuel, clock.getD "clk")
      match r with
      | .error e => err e
      | .ok (d, stim, signals, fuel, clock) =>
          let out ← IO.getStdout
          for dc in d.decls do
            let sign := if dc.isSigned then "signed" else "unsigned"
            if dc.isInput then out.putStrLn s!"PORT {dc.name} in {dc.width} {sign}"
            else if dc.isOutput then out.putStrLn s!"PORT {dc.name} out {dc.width} {sign}"
          match d.initStateRes with
          | .timeout => err "memory init: timeout"
          | .unsupported m => err s!"memory init: unsupported: {m}"
          | .ok initial =>
            match runMemInitial d fuel initial with
            | .timeout => err "memory initial: timeout"
            | .unsupported m => err s!"memory initial: unsupported: {m}"
            | .ok initial' => match runMemAtNegedge d fuel clock initial' stim with
              | .timeout => err "runMem2: timeout"
              | .unsupported m => err s!"runMem2: unsupported: {m}"
              | .ok trace =>
                let rec emit (k : Nat) : List SvState → IO Unit
                  | [] => pure ()
                  | st :: rest => do
                      let cells := signals.map fun s => s!"{s}={SvState.showSignal st s}"
                      out.putStrLn (s!"CYCLE {k} " ++ " ".intercalate cells)
                      emit (k + 1) rest
                emit 0 trace
                return 0
  | _ => err "usage: runner_mem2.lean <envelope.sv.json> <cases2.json> <case> <src|rev> [<probes.json>]"
