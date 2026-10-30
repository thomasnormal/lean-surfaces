/-
# SV phase-2 differential-harness runner (semantic tier, sv-0.2)

Executed by `harness/sv/diff_test2.py` as

  lake env lean --run harness/sv/runner2.lean <envelope.sv.json> <cases2.json> <case> <src|rev>

Loads a symbolic sv-0.2 envelope, resolves the case's parameter values
(declaration order; a parameter absent from the case's `params` object
takes its envelope default — and, when untyped, its default's type:
`PDesign.atPoint`), instantiates the SEMANTIC tier
(`PDesign.instantiateG2` → `Design2`: `instantiate2` under the one-driver
rule, `name.sem`'s family; a hierarchical envelope — top plus module
library — through `PDesign.instantiateH`, which flattens it), and
prints:

  PORT <name> <in|out> <width>     — one line per port, at THESE parameters
                                     (the TB generator's width source)
  CYCLE <k> <name>=<binary> ...    — one line per stimulus cycle, `run2`
                                     under the requested schedule

Any failure (parse, crossCheck, instantiation, a one-driver violation
`PortConn:driver`, `.timeout`/`.unsupported`)
prints `ERROR: ...` on stderr and exits nonzero. The crossCheck gate is
replayed here exactly as `load_design_sv2` does at elaboration time.

THE MULTI-POINT CROSS-CHECK (round 3 CX, `LeanModels/Sv/Probe2.lean`):

  lake env lean --run harness/sv/runner2.lean <envelope> <cases2.json> <case> <src|rev> <probes.json>

with a probe sidecar (`extract.py --probe-points`, written by
`diff_test2.py --xcheck` into its work dir) FIRST prints, before anything
else and whatever happens after, one line per entry of the sidecar point
whose overrides are exactly the case's `params`:

  XCHECK ok          <point> <entry>
  XCHECK UNCONFIRMED <point> <entry>: <verdict>
  XCHECK FAIL        <point> <entry>: <verdict>

(`ProbeVerdict.status`; `XCHECK FAIL nopoint: …` when the sidecar has no
such point, or does not parse). The harness counts any `FAIL` as an
`XCHECK-FAIL` case; `UNCONFIRMED` (the two designs are equal except where
one side refuses) fails the case unless every simulator then matches the
model at this very point (`diff_test2.py`).
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

/-- Resolve the parameter point: envelope parameter order; per-name value
from the case's `params` object (an integer OVERRIDE, as the testbench
passes it: `#(.P(v))`), else the parameter's envelope default (evaluated in
order, earlier parameters visible). `PDesign.atPoint` also retypes every
NOT-overridden untyped parameter with a non-INT default to its default's
type (IEEE 1800-2023 §6.20.2), so the instantiated design is the one the
simulator elaborates at exactly these overrides. -/
def resolvePoint (pd : PDesign) (paramsJ : Option Json) :
    Except String (PDesign × List Int) :=
  pd.atPoint <| pd.params.map fun p =>
    match paramsJ with
    | none => none
    | some pj =>
        match pj.getObjVal? p.name with
        | .ok v => v.getInt?.toOption
        | .error _ => none

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

/-- The case's `params` as an override list (non-integer values skipped —
the runner's `resolvePoint` reads them the same way). -/
def caseOverrides (paramsJ : Option Json) : List (String × Int) :=
  match paramsJ with
  | some (.obj kvs) =>
      kvs.toArray.toList.filterMap fun (n, v) => (v.getInt?.toOption.map (n, ·))
  | _ => []

/-- The `XCHECK` lines of the case's point (`Envelope2.probeReport` of the
sidecar point whose overrides are exactly the case's). -/
def xcheckLines (envText probesText casesText caseName : String) : List String :=
  let r : Except String (List String) := do
    let envl ← parseEnvelope2String envText
    let pr ← parseProbes2String probesText
    let cj ← Json.parse casesText
    let case ← findCase (← getArrF cj "cases") caseName
    let ov := caseOverrides (getFOpt case "params")
    let same (a b : List (String × Int)) : Bool :=
      a.length == b.length && a.all (b.contains ·)
    match pr.points.find? (fun p => same p.overrides ov) with
    | none => .error s!"the sidecar has no point {renderOverrides ov}"
    | some p =>
        pure <| (envl.probeReport { pr with points := [p] }).map fun (l, v) =>
          if v.ok then s!"XCHECK ok   {l}" else s!"XCHECK {v.status} {l}: {v.render}"
  match r with
  | .ok ls => ls
  | .error e => [s!"XCHECK FAIL nopoint: {e}"]

end SvHarness2

open SvHarness2 in
def main (argv : List String) : IO UInt32 := do
  let err (msg : String) : IO UInt32 := do
    (← IO.getStderr).putStrLn s!"ERROR: {msg}"
    return 1
  let (argv, probes?) := match argv with
    | [e, c, n, s, p] => ([e, c, n, s], some p)
    | _ => (argv, none)
  match argv with
  | [envPath, casesPath, caseName, sigmaName] => do
    let envText ← IO.FS.readFile ⟨envPath⟩
    let casesText ← IO.FS.readFile ⟨casesPath⟩
    -- The multi-point cross-check FIRST (round 3 CX): printed whatever
    -- the rest of the run does, so a refusal row still reports it.
    if let some pp := probes? then
      let prText ← IO.FS.readFile ⟨pp⟩
      let o ← IO.getStdout
      for ln in xcheckLines envText prText casesText caseName do
        o.putStrLn ln
      o.flush
    let r : Except String (Design2 × List SvState × List String × Nat) := do
      let (pd, lib) ← loadHierString envText
      match pd.crossCheck with
      | [] => pure ()
      | msgs => .error s!"crossCheck REFUSED: {String.intercalate " | " msgs}"
      -- A hierarchical envelope (F3): every library module at its own
      -- defaults, exactly as `load_design_sv2` gates it.
      for c in lib do
        match c.crossCheck with
        | [] => pure ()
        | msgs => .error s!"crossCheck REFUSED (module '{c.name}'): {String.intercalate " | " msgs}"
      let cj ← Json.parse casesText
      let fuel := (getFOpt cj "fuel").bind (·.getNat?.toOption) |>.getD 1000
      let case ← findCase (← getArrF cj "cases") caseName
      let (pd, args) ← resolvePoint pd (getFOpt case "params")
      -- Exact 32-bit `int` constants must give the design the unbounded
      -- fast path gives (`PDesign.int32Agrees`): otherwise the proof-facing
      -- family is not the circuit a simulator elaborates here.
      unless (if lib.isEmpty then pd.int32Agrees args else pd.int32AgreesH lib args) do
        .error "int32: an INT-class constant expression leaves the 32-bit range at these parameters (exact 32-bit `int` arithmetic and the unbounded constant tier build different designs)"
      -- A hierarchical envelope flattens through `instantiateH` (Hier2.lean);
      -- an instance-free top through `instantiateG2`, `instantiate2` under
      -- the same one-driver rule (`name.sem`'s family, 2026-10-28 WP2).
      let flatTop := lib.isEmpty || GenItem.listInstFree pd.generates
      let inst := if flatTop then pd.instantiateG2 args (PDesign.surfaceFuel args)
        else pd.instantiateH lib args (PDesign.surfaceFuel args)
      let d ← match inst with
        | .ok d => pure d
        | .timeout => .error "instantiate2: generate fuel exhausted"
        | .unsupported m => .error s!"instantiate2: {m}"
      unless d.namesNodup do
        .error "instantiateH: two declarations of one name after flattening"
      -- The one-driver rule (`Hier2.lean`, "Drivers"), named before `run2`
      -- would stop at the loud process.
      for p in d.processes do
        match p with
        | .unsupported "PortConn:driver" msg => .error s!"PortConn:driver: {msg}"
        | _ => pure ()
      -- The legacy-select range guard (round 3 folds, `RangeGuard2.lean`):
      -- a check beside `name.sem`, at this row's point, every module of the
      -- hierarchy at its own point.
      -- Round 6 (2026-10-29): the same guard family also reports
      -- `Select:wide-index` and `Select:partial-overhang`
      -- (`PDesign.selectGuardReport`, with the legacy half unchanged).
      if let some (k, msg) := pd.selectGuardReport lib args then
        .error s!"{k}: {msg}"
      -- The always_comb alias guard (round 6, lane B, `CombAlias2.lean`): a
      -- check beside `name.sem`, applied to the instantiated design (the
      -- flattened one for a hierarchy, port connections included). An
      -- `always_comb` that reads a continuous copy of a variable it writes
      -- becomes the loud `AlwaysComb:alias-read` process, named here before
      -- `run2` would stop at it; an admitted design is returned unchanged.
      let d := d.aliasGuard
      for p in d.processes do
        match p with
        | .unsupported "AlwaysComb:alias-read" msg => .error s!"AlwaysComb:alias-read: {msg}"
        | _ => pure ()
      -- The clock discipline (WP-Q0, 2026-10-30, `ClockGuard2.lean`): a
      -- check beside `name.sem`, at this row's point on the instantiated
      -- (flattened) design. A clock that is not an input port of the top, a
      -- clock read as data, a second clock or an internal asynchronous reset
      -- is named here (`Clock:source`, `Clock:data-read`, `Clock:multiple`,
      -- `Clock:reset`) before `run2` would run the design on cycles where no
      -- simulator sees an edge.
      if let some (k, msg) := d.clockReport then
        .error s!"{k}: {msg}"
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
      | .unsupported m =>
          -- Round 6: name the first loud node with its text as well
          -- (`Design2.firstLoud`): `m` carries only the node's kind.
          let detail := match d.firstLoud with
            | some (k, t) => s!" [{k}: {t}]"
            | none => ""
          err s!"run2: unsupported: {m}{detail}"
      | .ok trace => do
          let mut k := 0
          for st in trace do
            let cells := signals.map fun s => s!"{s}={SvState.showSignal st s}"
            out.putStrLn (s!"CYCLE {k} " ++ " ".intercalate cells)
            k := k + 1
          return 0
  | _ => err "usage: runner2.lean <envelope.sv.json> <cases2.json> <case> <src|rev> [<probes.json>]"
