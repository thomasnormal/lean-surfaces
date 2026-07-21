/-
# SV M0 differential-harness runner (Lean side)

Executed by `harness/sv/diff_test.py` as

  lake env lean --run harness/sv/runner.lean <envelope.sv.json> <cases.json> <case> <src|rev>

and prints one canonical line per cycle — `CYCLE <k> <name>=<binary> ...` —
identical in format to the Xcelium testbench's `$display` output (signals in
the case's `signals` order, values as `%b` strings with `x`/`z`). Any failure
(load error, `.timeout`, `.unsupported`) prints `ERROR: ...` on stderr and
exits nonzero.

## Envelope adapter (why this file has its own parser)

`LeanModels/Sv/Json.lean` was written against the design contract before
`docs/sv-envelope-schema.md` existed, and its vocabulary does NOT match the
real extractor output: the actual envelopes use `design.modules[]` with
separate `ports` (`dir: "in"|"out"`), `Var`/`Net` decls whose `init` is a
`Literal` *expression node*, process kind `AlwaysPosedge` with a `style`
field, and assignment `target`s that are `Ident` nodes — where `Json.lean`
expects a flat single-module payload, string targets, and `AlwaysFF`/`Always`
kinds. The adapter below parses the schema-doc vocabulary, reusing
`Json.lean`'s `parseExpr`/`parseUnaryOpName`/`parseBinOpName` (whose alternate
spellings DO cover the real expression nodes: `Literal.bits`, `Unary.operand`,
`Ternary.then/else`). Porting this adapter into `Json.lean` is an integration
item — the harness must not edit files it does not own.

Interpreter facts this runner relies on (`LeanModels/Sv/Semantics.lean`):
`run d σ fuel stim` = one `cycleStep` snapshot per stimulus entry; `σ_src` =
source order (Xcelium's empirical order), `σ_rev` = reverse; stimulus entries
only ever overwrite declared *input* ports, absent inputs hold.
-/

import Lean
import LeanModels.Sv.Json
import LeanModels.Sv.Semantics

open Lean (Json)
open LeanModels.Sv

namespace SvHarness

/-! ## JSON field helpers (Json.lean's are private) -/

def getF (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{name}'"

/-- Optional field: absent or `null` ↦ `none`. -/
def getFOpt (j : Json) (name : String) : Option Json :=
  match j.getObjVal? name with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

def getStrF (j : Json) (name : String) : Except String String := do
  match (← getF j name).getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"field '{name}' is not a string"

def getNatF (j : Json) (name : String) : Except String Nat := do
  match (← getF j name).getNat? with
  | .ok n => .ok n
  | .error _ => .error s!"field '{name}' is not a Nat"

def getArrF (j : Json) (name : String) : Except String (Array Json) := do
  match (← getF j name).getArr? with
  | .ok a => .ok a
  | .error _ => .error s!"field '{name}' is not an array"

def unsupportedText (j : Json) : String :=
  (getFOpt j "text").bind (·.getStr?.toOption) |>.getD ""

/-! ## Envelope adapter: docs/sv-envelope-schema.md → `Design` -/

/-- Assignment/continuous-assign target: the schema guarantees an `Ident`
expression node in M0. -/
def targetName (j : Json) : Except String String := do
  match ← parseExpr j with
  | .ident n => .ok n
  | .unsupported svKind _ => .error s!"unsupported assignment target ({svKind})"
  | _ => .error "assignment target is not a plain identifier"

/-- Statement nodes per the schema doc (`Block.stmts`, expr-node targets,
`If.then/else`). Expressions inside delegate to `Json.lean`'s `parseExpr`. -/
partial def parseStmtE (j : Json) : Except String Stmt := do
  let kind ← getStrF j "kind"
  match kind with
  | "Block" =>
      return .block (← (← getArrF j "stmts").mapM parseStmtE)
  | "BlockingAssign" =>
      return .blockingAssign (← targetName (← getF j "target"))
        (← parseExpr (← getF j "value"))
  | "NonblockingAssign" =>
      return .nbaAssign (← targetName (← getF j "target"))
        (← parseExpr (← getF j "value"))
  | "If" =>
      let elseBranch ← match getFOpt j "else" with
        | none => pure none
        | some je => pure (some (← parseStmtE je))
      return .ifStmt (← parseExpr (← getF j "cond"))
        (← parseStmtE (← getF j "then")) elseBranch
  | "Unsupported" =>
      return .unsupported (← getStrF j "sv_kind") (unsupportedText j)
  | k => .error s!"unknown statement kind '{k}'"

/-- Process nodes: `AlwaysPosedge` (style `always_ff`/`always`),
`AlwaysComb`, `Assign`, `Unsupported`. -/
def parseProcessE (j : Json) : Except String Process := do
  let kind ← getStrF j "kind"
  match kind with
  | "AlwaysPosedge" =>
      let clock ← getStrF j "clock"
      let body ← parseStmtE (← getF j "body")
      match ← getStrF j "style" with
      | "always_ff" => return .alwaysFF clock body
      | "always" => return .alwaysPlain clock body
      | s => .error s!"unknown AlwaysPosedge style '{s}'"
  | "AlwaysComb" =>
      return .alwaysComb (← parseStmtE (← getF j "body"))
  | "Assign" =>
      return .assign (← targetName (← getF j "target"))
        (← parseExpr (← getF j "value"))
  | "Unsupported" =>
      return .unsupported (← getStrF j "sv_kind") (unsupportedText j)
  | k => .error s!"unknown process kind '{k}'"

/-- `Port` → `Decl` (`dir: "in"|"out"`; unsupported ports are load errors —
the harness needs every port drivable/sampleable). -/
def parsePortE (j : Json) : Except String Decl := do
  match ← getStrF j "kind" with
  | "Port" =>
      let name ← getStrF j "name"
      let width ← getNatF j "width"
      match ← getStrF j "dir" with
      | "in" => return { name, width, isInput := true }
      | "out" => return { name, width, isOutput := true }
      | d => .error s!"port '{name}': unknown dir '{d}'"
  | "Unsupported" =>
      .error s!"unsupported port ({(getStrF j "sv_kind").toOption.getD "?"})"
  | k => .error s!"unknown port kind '{k}'"

/-- `Var`/`Net` → `Decl`. `init` is a `Literal` expression node in M0 (a
non-literal `Net` init would be an implicit continuous-assign driver — absent
from the M0 examples, rejected loudly here). -/
def parseDeclE (j : Json) : Except String Decl := do
  match ← getStrF j "kind" with
  | "Var" | "Net" =>
      let name ← getStrF j "name"
      let width ← getNatF j "width"
      let init ← match getFOpt j "init" with
        | none => pure none
        | some ji =>
            match ← parseExpr ji with
            | .lit v => pure (some v)
            | _ => .error s!"decl '{name}': non-literal initializer (outside M0 harness support)"
      return { name, width, init }
  | "Unsupported" =>
      .error s!"unsupported decl ({(getStrF j "sv_kind").toOption.getD "?"})"
  | k => .error s!"unknown decl kind '{k}'"

/-- One `Module` payload → `Design` (decls = ports first, then vars/nets, in
source order — `initState`/`σ_src` order). Unsupported members in `others`
become an `unsupported` process so the interpreter is loud, not silent. -/
def parseModuleE (j : Json) : Except String Design := do
  let name ← getStrF j "name"
  let ports ← (← getArrF j "ports").mapM parsePortE
  let vars ← (← getArrF j "decls").mapM parseDeclE
  let mut processes ← (← getArrF j "processes").mapM parseProcessE
  let others ← getArrF j "others"
  if !others.isEmpty then
    processes := processes.push
      (.unsupported "ModuleOthers" s!"{others.size} unsupported module member(s)")
  return { name, decls := ports ++ vars, processes }

/-- Full envelope text → `Design`. Validates `schema_version`/`language` and
the M0 single-module shape. -/
def loadEnvelopeDesign (text : String) : Except String Design := do
  let j ← Json.parse text
  let sv ← getStrF j "schema_version"
  unless sv == "sv-0.1" do throw s!"unsupported schema_version '{sv}' (want sv-0.1)"
  let lang ← getStrF j "language"
  unless lang == "systemverilog" do throw s!"unsupported language '{lang}'"
  let design ← getF j "design"
  let modules ← getArrF design "modules"
  let dOthers ← getArrF design "others"
  unless dOthers.isEmpty do throw s!"design.others is non-empty ({dOthers.size} node(s))"
  match modules with
  | #[m] => parseModuleE m
  | ms => .error s!"expected exactly one module in the envelope, got {ms.size}"

/-! ## Cases -/

/-- One stimulus object → `SvState`: input-port name ↦ MSB-first binary
string at the exact declared width. Non-input or undeclared names and width
mismatches are loud (they would silently diverge from the testbench). -/
def parseStim (d : Design) (j : Json) : Except String SvState := do
  let obj ← match j.getObj? with
    | .ok o => pure o
    | .error _ => .error "stimulus entry is not an object"
  let pairs : Array (String × Json) := obj.foldl (fun acc k v => acc.push (k, v)) #[]
  pairs.foldlM (init := ([] : SvState)) fun st (name, vj) => do
    let s ← match vj.getStr? with
      | .ok s => pure s
      | .error _ => .error s!"stimulus '{name}': value is not a string"
    let some v := LVec.ofString? s
      | .error s!"stimulus '{name}': bad binary string {s.quote} (digits 0 1 x z _)"
    match d.decls.find? (·.name == name) with
    | none => .error s!"stimulus name '{name}' is not declared in the design"
    | some dc =>
        unless dc.isInput do throw s!"stimulus name '{name}' is not an input port"
        unless v.width == dc.width do
          throw s!"stimulus '{name}': width {v.width} ≠ declared width {dc.width}"
        return SvState.set st name v

structure Prepared where
  design : Design
  fuel : Nat
  signals : Array String
  stim : List SvState

/-- Load envelope + cases file, select the named case, cross-check it. -/
def prepare (envText casesText caseName : String) : Except String Prepared := do
  let d ← loadEnvelopeDesign envText
  let cj ← Json.parse casesText
  let fuel := ((getF cj "fuel").toOption.bind (·.getNat?.toOption)).getD 1000
  let arr ← getArrF cj "cases"
  let some c := arr.find? fun c => (getStrF c "name").toOption == some caseName
    | .error s!"no case named '{caseName}' in cases.json"
  let ex ← getStrF c "example"
  unless ex == d.name do
    throw s!"case example '{ex}' ≠ envelope module '{d.name}'"
  let signals ← (← getArrF c "signals").mapM fun s =>
    match s.getStr? with
    | .ok n => .ok n
    | .error _ => .error "signals entries must be strings"
  for n in signals do
    unless d.decls.any (·.name == n) do
      throw s!"sampled signal '{n}' is not declared in the design"
  let stim ← (← getArrF c "stimulus").toList.mapM (parseStim d)
  return { design := d, fuel, signals, stim }

/-- The canonical per-cycle line, identical to the testbench's
`$display("CYCLE %0d <name>=%b ...")`. -/
def lineFor (signals : Array String) (k : Nat) (st : SvState) : String :=
  String.intercalate " "
    (s!"CYCLE {k}" :: signals.toList.map fun n => s!"{n}={SvState.showSignal st n}")

end SvHarness

open SvHarness in
def main (args : List String) : IO UInt32 := do
  match args with
  | [envPath, casesPath, caseName, sigmaName] =>
    let σ ← match sigmaName with
      | "src" => pure σ_src
      | "rev" => pure σ_rev
      | s => do
          IO.eprintln s!"ERROR: unknown sigma '{s}' (want src|rev)"
          return 2
    let envText ← IO.FS.readFile envPath
    let casesText ← IO.FS.readFile casesPath
    match prepare envText casesText caseName with
    | .error e =>
        IO.eprintln s!"ERROR: {e}"
        return 1
    | .ok p =>
        match LeanModels.Sv.run p.design σ p.fuel p.stim with
        | .ok snaps =>
            let mut k := 0
            for st in snaps do
              IO.println (lineFor p.signals k st)
              k := k + 1
            return 0
        | .timeout =>
            IO.eprintln "ERROR: interpreter timeout (fuel exhausted — combinational loop?)"
            return 1
        | .unsupported msg =>
            IO.eprintln s!"ERROR: unsupported: {msg}"
            return 1
  | _ =>
    IO.eprintln "usage: lake env lean --run harness/sv/runner.lean <envelope.sv.json> <cases.json> <case> <src|rev>"
    return 2
