import LeanModels.Sv.Json
import LeanModels.Sv.Semantics
import LeanModels.Sv.Surface

/-!
# SV M0 scheduler smoke tests (`LeanModels.Sv`)

`#guard` tests of `Semantics.lean` on hand-built copies of the five M0
gallery designs (transcribed to match `Examples/sv/*.sv.json` exactly),
covering every Xcelium-verified outcome the design contract names, plus the
loud paths (`.timeout` on a comb loop, `.unsupported` on out-of-tier
nodes).

The second half ingests the **real** extractor envelopes end-to-end. The
parser in `Json.lean` predates `docs/sv-envelope-schema.md` and does not
match the actual envelope shape (`design.modules[]` + separate `ports`,
`AlwaysPosedge {style}`, assignment targets as `Ident` *nodes*, decl `init`
as an expression node), so this file carries a self-contained adapter for
the real schema — `namespace EnvelopeIngest` — which reuses `parseExpr`
from `Json.lean` (whose expression vocabulary does match) and re-parses
everything above it. The `#eval` blocks at the bottom read
`Examples/sv/*.sv.json` from disk (paths relative to the repo root, where
`lake env lean` runs per the contract), check the ingested designs against
the hand-built ones node-for-node, and re-run the semantic checks on the
ingested designs — a mismatch fails the file, so a green
`lake env lean LeanModels/Sv/Tests.lean` certifies extractor → ingester →
interpreter end to end.
-/

namespace LeanModels.Sv

/-! ## Test helpers -/

/-- The `%b` trace of one signal, `none` unless the run was `.ok`. -/
private def sigTrace (r : Res (List SvState)) (name : String) : Option (List String) :=
  match r with
  | .ok tr => some (tr.map fun st => SvState.showSignal st name)
  | _ => none

private def isUnsupported : Res (List SvState) → Bool
  | .unsupported _ => true
  | _ => false

private def b8 (n : Nat) : LVec := .ofNat 8 n
private def bit (n : Nat) : LVec := .ofNat 1 n

/-! ## Hand-built designs (exact transcriptions of `Examples/sv/*.sv`) -/

private def adderD : Design :=
  { name := "adder"
    decls := #[
      { name := "a", width := 8, isInput := true },
      { name := "b", width := 8, isInput := true },
      { name := "s", width := 8, isOutput := true }]
    processes := #[.assign "s" (.binary .add (.ident "a") (.ident "b"))] }

private def counterD : Design :=
  { name := "counter"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "rst", width := 1, isInput := true },
      { name := "count", width := 8, isOutput := true }]
    processes := #[
      .alwaysFF "clk" (.ifStmt (.ident "rst")
        (.nbaAssign "count" (.lit (.ofNat 8 0)))
        (some (.nbaAssign "count"
          (.binary .add (.ident "count") (.lit (.ofNat 8 1))))))] }

private def raceBlkD : Design :=
  { name := "race_blk"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "a", width := 8, init := some (b8 1) },
      { name := "b", width := 8, init := some (b8 2) }]
    processes := #[
      .alwaysPlain "clk" (.blockingAssign "a" (.ident "b")),
      .alwaysPlain "clk" (.blockingAssign "b" (.ident "a"))] }

private def swapNbaD : Design :=
  { name := "swap_nba"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "a", width := 8, init := some (b8 1) },
      { name := "b", width := 8, init := some (b8 2) }]
    processes := #[
      .alwaysPlain "clk" (.nbaAssign "a" (.ident "b")),
      .alwaysPlain "clk" (.nbaAssign "b" (.ident "a"))] }

private def xselD : Design :=
  { name := "xsel"
    decls := #[
      { name := "sel", width := 1, isInput := true },
      { name := "a", width := 8, isInput := true },
      { name := "b", width := 8, isInput := true },
      { name := "y", width := 8, isOutput := true }]
    processes := #[
      .alwaysComb (.ifStmt (.ident "sel")
        (.blockingAssign "y" (.ident "a"))
        (some (.blockingAssign "y" (.ident "b"))))] }

/-! ## Startup state (LRM §6.8) -/

#guard initState counterD ==
  [("clk", .xVec 1), ("rst", .xVec 1), ("count", .xVec 8)]
#guard initState raceBlkD == [("clk", .xVec 1), ("a", b8 1), ("b", b8 2)]

/-! ## `swap_nba`: swaps every cycle, under EVERY schedule (gallery ex. 3) -/

private def clkCyc : SvState := [("clk", bit 1)]
private def swapStim : List SvState := [clkCyc, clkCyc]

#guard sigTrace (run swapNbaD σ_src 64 swapStim) "a" == some ["00000010", "00000001"]
#guard sigTrace (run swapNbaD σ_src 64 swapStim) "b" == some ["00000001", "00000010"]
-- schedule-independent: reversed σ, and mixed per-invocation σ, same trace
#guard run swapNbaD σ_rev 64 swapStim == run swapNbaD σ_src 64 swapStim
#guard run swapNbaD (.revWhen (· % 3 == 1)) 64 swapStim == run swapNbaD σ_src 64 swapStim

/-! ## `race_blk`: the Xcelium-verified (2,2)-vs-(1,1) race (gallery ex. 3) -/

private def raceStim : List SvState := [clkCyc]

#guard sigTrace (run raceBlkD σ_src 64 raceStim) "a" == some ["00000010"]  -- (2,2)
#guard sigTrace (run raceBlkD σ_src 64 raceStim) "b" == some ["00000010"]
#guard sigTrace (run raceBlkD σ_rev 64 raceStim) "a" == some ["00000001"]  -- (1,1)
#guard sigTrace (run raceBlkD σ_rev 64 raceStim) "b" == some ["00000001"]
#guard run raceBlkD σ_src 64 raceStim != run raceBlkD σ_rev 64 raceStim
-- invocation-counter protocol: on this 1-cycle run the edge phase is oracle
-- invocation k = 1 (k = 0 was the first comb-settle pass), so reversing only
-- odd invocations also yields the (1,1) outcome
#guard run raceBlkD (.revWhen (· % 2 == 1)) 64 raceStim == run raceBlkD σ_rev 64 raceStim

/-! ## `counter`: x through pre-reset edges (x+1 = x!), reset, count, wrap -/

private def rstCyc (r : Nat) : SvState := [("clk", bit 1), ("rst", bit r)]
private def counterStim : List SvState :=
  [rstCyc 0, rstCyc 0, rstCyc 1, rstCyc 0, rstCyc 0, rstCyc 0]

#guard sigTrace (run counterD σ_src 64 counterStim) "count" ==
  some ["xxxxxxxx", "xxxxxxxx", "00000000", "00000001", "00000010", "00000011"]
#guard run counterD σ_rev 64 counterStim == run counterD σ_src 64 counterStim

-- wrap-around at 256 (mod 2^8 arithmetic): after the reset cycle, cycle
-- 255 shows 11111111 and cycle 256 wraps to 0
private def wrapCount : List String :=
  (sigTrace (run counterD σ_src 64 (rstCyc 1 :: List.replicate 256 (rstCyc 0))) "count").getD []
#guard wrapCount.length == 257
#guard wrapCount[255]? == some "11111111"
#guard wrapCount.getLastD "" == "00000000"

-- the stimulus cannot clobber non-input signals ("count" is an output):
#guard sigTrace (run counterD σ_src 64 [[("rst", bit 1), ("count", b8 77)]]) "count" ==
  some ["00000000"]
-- an input absent from a stimulus entry holds its previous value (rst stays 1):
#guard sigTrace (run counterD σ_src 64 [rstCyc 1, []]) "count" ==
  some ["00000000", "00000000"]

/-! ## `xsel`: X-optimism — sel = x/z takes the ELSE branch (gallery ex. 5) -/

private def xselStim (sel : LVec) : List SvState :=
  [[("sel", sel), ("a", b8 0xAA), ("b", b8 0x55)]]

#guard sigTrace (run xselD σ_src 64 (xselStim (bit 1))) "y" == some ["10101010"]  -- a
#guard sigTrace (run xselD σ_src 64 (xselStim (bit 0))) "y" == some ["01010101"]  -- b
#guard sigTrace (run xselD σ_src 64 (xselStim (.lit "x"))) "y" == some ["01010101"]  -- b!
#guard sigTrace (run xselD σ_src 64 (xselStim (.lit "z"))) "y" == some ["01010101"]  -- b!
#guard run xselD σ_rev 64 (xselStim (.lit "x")) == run xselD σ_src 64 (xselStim (.lit "x"))

/-! ## `adder`: known add + whole-vector x collapse (gallery ex. 1) -/

#guard sigTrace (run adderD σ_src 64 [[("a", b8 5), ("b", b8 3)]]) "s" ==
  some ["00001000"]
#guard sigTrace (run adderD σ_src 64 [[("a", b8 200), ("b", b8 100)]]) "s" ==
  some ["00101100"]  -- 300 mod 256 = 44
#guard sigTrace (run adderD σ_src 64 [[("a", .lit "0000000x"), ("b", b8 3)]]) "s" ==
  some ["xxxxxxxx"]  -- ONE x bit → ALL EIGHT result bits x (§11.4.3)
-- with no stimulus for a cycle, inputs stay x from startup → s all-x
#guard sigTrace (run adderD σ_src 64 [[]]) "s" == some ["xxxxxxxx"]

/-! ## Edge-phase mechanics: blocking immediacy and NBA last-wins -/

-- blocking assigns inside one body are immediately visible: q = 1; r = q
private def blkSeqD : Design :=
  { name := "blk_seq"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "q", width := 8 }, { name := "r", width := 8 }]
    processes := #[.alwaysFF "clk" (.block #[
      .blockingAssign "q" (.lit (b8 1)),
      .blockingAssign "r" (.ident "q")])] }

#guard sigTrace (run blkSeqD σ_src 64 [clkCyc]) "r" == some ["00000001"]

-- two NBAs to the same target in one edge phase: LAST write wins
private def nbaLastD : Design :=
  { name := "nba_last"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "q", width := 8 }]
    processes := #[.alwaysFF "clk" (.block #[
      .nbaAssign "q" (.lit (b8 1)),
      .nbaAssign "q" (.lit (b8 2))])] }

#guard sigTrace (run nbaLastD σ_src 64 [clkCyc]) "q" == some ["00000010"]

-- NBA reads pre-commit state even inside ONE body: q <= 5; r <= q sees old q
private def nbaReadD : Design :=
  { name := "nba_read"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "q", width := 8, init := some (b8 9) }, { name := "r", width := 8 }]
    processes := #[.alwaysFF "clk" (.block #[
      .nbaAssign "q" (.lit (b8 5)),
      .nbaAssign "r" (.ident "q")])] }

#guard sigTrace (run nbaReadD σ_src 64 [clkCyc]) "q" == some ["00000101"]
#guard sigTrace (run nbaReadD σ_src 64 [clkCyc]) "r" == some ["00001001"]  -- old q!

/-! ## Loud paths -/

-- combinational loop (assign a = ~a from a known start) → .timeout
private def oscD : Design :=
  { name := "osc"
    decls := #[{ name := "a", width := 1, init := some (bit 0) }]
    processes := #[.assign "a" (.unary .bnot (.ident "a"))] }

#guard run oscD σ_src 64 [[]] == (.timeout : Res (List SvState))
-- ... but ~x = x is a FIXPOINT: the same loop from startup x settles
#guard sigTrace (run { oscD with decls := #[{ name := "a", width := 1 }] } σ_src 64 [[]]) "a"
  == some ["x"]

-- an unsupported PROCESS is loud on every cycle (never silently dropped)
private def initialD : Design :=
  { name := "bad"
    decls := #[]
    processes := #[.unsupported "ProceduralBlockSymbol:Initial" "initial begin #10; end"] }

#guard isUnsupported (run initialD σ_src 64 [[]])
#guard run initialD σ_src 64 [] == (.ok [] : Res (List SvState))  -- no cycles, no observation

-- an unsupported STATEMENT is loud only when reached: rst=0 avoids it, rst=1 hits it
private def guardedD : Design :=
  { name := "guarded"
    decls := #[
      { name := "rst", width := 1, isInput := true },
      { name := "count", width := 8 }]
    processes := #[
      .alwaysFF "clk" (.ifStmt (.ident "rst")
        (.unsupported "CaseStatement" "case (count) ... endcase")
        (some (.nbaAssign "count" (.lit (b8 7)))))] }

#guard sigTrace (run guardedD σ_src 64 [[("rst", bit 0)]]) "count" == some ["00000111"]
#guard isUnsupported (run guardedD σ_src 64 [[("rst", bit 1)]])

-- a nonblocking assign inside always_comb is outside the M0 cycle semantics
private def combNbaD : Design :=
  { name := "comb_nba"
    decls := #[{ name := "y", width := 1 }]
    processes := #[.alwaysComb (.nbaAssign "y" (.lit (bit 0)))] }

#guard isUnsupported (run combNbaD σ_src 64 [[]])

-- reading an undeclared identifier is loud
#guard evalExpr 8 [] (.ident "ghost") ==
  (.unsupported "unknown identifier 'ghost' (not a declared signal)" : Res LVec)

-- fuel exhaustion at any depth is .timeout
#guard evalExpr 0 [] (.lit (bit 0)) == (.timeout : Res LVec)
#guard run counterD σ_src 0 [rstCyc 1] == (.timeout : Res (List SvState))

/-! ## Expression plumbing through the interpreter -/

#guard evalExpr 8 [("a", .lit "10")] (.binary .eq (.ident "a") (.lit (.lit "10")))
  == .ok (.ofLogic .l1)
#guard evalExpr 8 [("a", .lit "1x")] (.binary .eq (.ident "a") (.lit (.lit "00")))
  == .ok (.ofLogic .l0)  -- definite mismatch beats the x
#guard evalExpr 8 [("c", .lit "x"), ("a", .lit "1010"), ("b", .lit "1001")]
  (.ternary (.ident "c") (.ident "a") (.ident "b")) == .ok (.lit "10xx")  -- §11.4.11 merge
#guard evalExpr 8 [("a", .lit "10"), ("b", .lit "01")]
  (.concat #[.ident "a", .ident "b"]) == .ok (.lit "1001")
#guard evalExpr 8 [] (.unary .lnot (.lit (.lit "0x"))) == .ok (.ofLogic .lx)

-- run is a function: same arguments, same trace (determinism, pinned)
#guard run counterD σ_src 64 counterStim == run counterD σ_src 64 counterStim

/-! ## Real-envelope ingestion (schema `sv-0.1`, per `docs/sv-envelope-schema.md`)

`Json.lean`'s statement/process/module parsers predate the schema doc and
do not match the real extractor output; this adapter is written against the
schema doc and reuses only `parseExpr` (whose vocabulary does match:
`Literal.bits`, `Unary.operand`, `Ternary.then/else`, symbol op names are
all accepted there). Differences handled here:

* envelope `design` is `{kind: "Design", modules: [...], others: [...]}`;
* module `ports` (with `dir`) are separate from `decls` (`Var`/`Net`);
* decl `init` is an expression node (must be a `Literal` in M0);
* assignment/continuous-assign `target` is an `Ident` *node*, not a string
  (non-`Ident` targets become `unsupported`, mirroring the extractor's
  `AssignmentExpression:target`);
* processes are `AlwaysPosedge {style, clock, body}` / `AlwaysComb` /
  `Assign`;
* `Unsupported` members found in `ports`/`decls`/`others` are appended to
  `Design.processes` as `Process.unsupported` — the design still loads and
  the interpreter is loud when it runs (`Process.isCombPhase`).

Deviation note (M0-irrelevant): a `Net` decl's `init` is per LRM an
implicit continuous assign; this adapter stores it as a time-0 initializer
like a `Var`'s. No M0 example has one. -/

namespace EnvelopeIngest

open Lean (Json)

private def field (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{name}'"

private def strField (j : Json) (name : String) : Except String String := do
  match (← field j name).getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"field '{name}' is not a string"

private def natField (j : Json) (name : String) : Except String Nat := do
  match (← field j name).getNat? with
  | .ok n => .ok n
  | .error _ => .error s!"field '{name}' is not a Nat"

/-- Optional field: absent or `null` ↦ `none`. -/
private def optField (j : Json) (name : String) : Option Json :=
  match j.getObjVal? name with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

private def kindOf (j : Json) : Except String String := strField j "kind"

/-- `sv_kind`/`text` of an `Unsupported` node, defensively defaulted. -/
private def unsupPair (j : Json) : String × String :=
  ( ((optField j "sv_kind").bind (·.getStr?.toOption)).getD "?"
  , ((optField j "text").bind (·.getStr?.toOption)).getD "" )

/-- An assignment `target` node: always an `Ident` per the schema;
anything else ↦ `none` (caller demotes to `unsupported`). -/
private def targetName (j : Json) : Except String (Option String) := do
  match ← LeanModels.Sv.parseExpr j with
  | .ident n => return some n
  | _ => return none

/-- Statement nodes per the schema doc (real vocabulary; `Json.parseStmt`
does not match it). -/
partial def parseStmt (j : Json) : Except String Stmt := do
  match ← kindOf j with
  | "Block" =>
      return .block (← (← (← field j "stmts").getArr?).mapM parseStmt)
  | "BlockingAssign" =>
      match ← targetName (← field j "target") with
      | some n => return .blockingAssign n (← LeanModels.Sv.parseExpr (← field j "value"))
      | none => return .unsupported "AssignmentExpression:target" ""
  | "NonblockingAssign" =>
      match ← targetName (← field j "target") with
      | some n => return .nbaAssign n (← LeanModels.Sv.parseExpr (← field j "value"))
      | none => return .unsupported "AssignmentExpression:target" ""
  | "If" =>
      let cond ← LeanModels.Sv.parseExpr (← field j "cond")
      let thenB ← parseStmt (← field j "then")
      let elseB ← match optField j "else" with
        | none => pure none
        | some je => some <$> parseStmt je
      return .ifStmt cond thenB elseB
  | "Unsupported" =>
      let (k, t) := unsupPair j
      return .unsupported k t
  | other => throw s!"unknown statement kind {other.quote}"

/-- Process nodes per the schema doc (`AlwaysPosedge {style}` etc.). -/
def parseProcess (j : Json) : Except String Process := do
  match ← kindOf j with
  | "AlwaysPosedge" =>
      let clock ← strField j "clock"
      let body ← parseStmt (← field j "body")
      match ← strField j "style" with
      | "always_ff" => return .alwaysFF clock body
      | "always" => return .alwaysPlain clock body
      | s => throw s!"unknown AlwaysPosedge style {s.quote}"
  | "AlwaysComb" =>
      return .alwaysComb (← parseStmt (← field j "body"))
  | "Assign" =>
      match ← targetName (← field j "target") with
      | some n => return .assign n (← LeanModels.Sv.parseExpr (← field j "value"))
      | none => return .unsupported "AssignmentExpression:target" ""
  | "Unsupported" =>
      let (k, t) := unsupPair j
      return .unsupported k t
  | other => throw s!"unknown process kind {other.quote}"

/-- One `Module` payload → `Design`. Ports become input/output `Decl`s
(before the module-body decls, i.e. in overall declaration order);
`Unsupported` ports/decls/others become trailing `Process.unsupported`
entries so the loaded design is loud when run. -/
def parseModule (j : Json) : Except String Design := do
  let name ← strField j "name"
  let mut decls : Array Decl := #[]
  let mut unsup : Array Process := #[]
  for pj in ← (← field j "ports").getArr? do
    match ← kindOf pj with
    | "Port" =>
        let dir ← strField pj "dir"
        unless dir == "in" || dir == "out" do
          throw s!"unknown port dir {dir.quote}"
        decls := decls.push
          { name := ← strField pj "name", width := ← natField pj "width"
            isInput := dir == "in", isOutput := dir == "out" }
    | "Unsupported" =>
        let (k, t) := unsupPair pj
        unsup := unsup.push (.unsupported k t)
    | other => throw s!"unknown port kind {other.quote}"
  for dj in ← (← field j "decls").getArr? do
    match ← kindOf dj with
    | "Var" | "Net" =>
        let dname ← strField dj "name"
        let init ← match optField dj "init" with
          | none => pure none
          | some ij =>
              match ← LeanModels.Sv.parseExpr ij with
              | .lit v => pure (some v)
              | _ => throw s!"decl '{dname}': non-literal initializer is outside the M0 ingestion tier"
        decls := decls.push { name := dname, width := ← natField dj "width", init }
    | "Unsupported" =>
        let (k, t) := unsupPair dj
        unsup := unsup.push (.unsupported k t)
    | other => throw s!"unknown decl kind {other.quote}"
  let processes ← (← (← field j "processes").getArr?).mapM parseProcess
  let others := (← (← field j "others").getArr?).map fun oj =>
    let (k, t) := unsupPair oj
    Process.unsupported k t
  return { name, decls, processes := processes ++ unsup ++ others }

/-- Full real-schema envelope → `Design` (single M0 module; design-level
`others` are appended as unsupported processes like module ones). -/
def loadDesign (j : Json) : Except String Design := do
  let sv ← strField j "schema_version"
  unless sv == "sv-0.1" do throw s!"unsupported schema_version {sv.quote}"
  let lang ← strField j "language"
  unless lang == "systemverilog" do throw s!"unsupported language {lang.quote}"
  let design ← field j "design"
  let modules ← (← field design "modules").getArr?
  match modules[0]? with
  | none => throw "envelope has no modules"
  | some mj =>
      unless modules.size == 1 do
        throw s!"multi-module envelope ({modules.size} modules) is outside the M0 ingestion tier"
      let d ← parseModule mj
      let dothers := (← (← field design "others").getArr?).map fun oj =>
        let (k, t) := unsupPair oj
        Process.unsupported k t
      return { d with processes := d.processes ++ dothers }

/-- JSON text → `Design`. -/
def loadDesignString (s : String) : Except String Design :=
  Json.parse s >>= loadDesign

/-- Read + ingest an envelope file (path relative to the cwd, which is the
repo root under `lake env lean`). Throws on any parse/ingest error. -/
def loadFile (path : String) : IO Design := do
  match loadDesignString (← IO.FS.readFile path) with
  | .ok d => return d
  | .error e => throw (IO.userError s!"{path}: {e}")

end EnvelopeIngest

/-! ### Adapter unit test on a hand-written real-schema snippet -/

#guard (EnvelopeIngest.loadDesignString r#"{
  "schema_version": "sv-0.1",
  "language": "systemverilog",
  "frontend": {"name": "pyslang", "version": "11.0.0"},
  "source_file": "x.sv",
  "source_sha256": "00",
  "design": {"kind": "Design", "modules": [
    {"kind": "Module", "span": null, "name": "m",
     "ports": [{"kind": "Port", "span": null, "name": "clk", "dir": "in", "width": 1}],
     "decls": [{"kind": "Var", "span": null, "name": "a", "width": 8,
                "init": {"kind": "Literal", "span": null, "width": 8, "bits": "00000001"}}],
     "processes": [
       {"kind": "AlwaysPosedge", "span": null, "style": "always", "clock": "clk",
        "body": {"kind": "BlockingAssign", "span": null,
                 "target": {"kind": "Ident", "span": null, "width": 8, "name": "a"},
                 "value": {"kind": "Ident", "span": null, "width": 8, "name": "a"}}}],
     "others": [{"kind": "Unsupported", "span": null, "sv_kind": "InstanceSymbol:Instance", "text": "sub u();"}]}],
    "others": []},
  "lean_blocks": []
}"#).toOption ==
  some
    { name := "m"
      decls := #[
        { name := "clk", width := 1, isInput := true },
        { name := "a", width := 8, init := some (b8 1) }]
      processes := #[
        .alwaysPlain "clk" (.blockingAssign "a" (.ident "a")),
        .unsupported "InstanceSymbol:Instance" "sub u();"] }

/-! ### End-to-end: the five REAL envelopes from disk

Each `#eval` fails the file (and thus `lake env lean`) on any mismatch. -/

private def check (label : String) (b : Bool) : IO Unit := do
  unless b do throw (IO.userError s!"FAIL: {label}")

/-- Ingest one envelope and require exact equality with the hand-built
design (name, decls incl. widths/ports/inits, processes, node for node). -/
private def checkIngest (path : String) (expected : Design) : IO Design := do
  let d ← EnvelopeIngest.loadFile path
  check s!"{path}: ingested design == hand-built design" (d == expected)
  check s!"{path}: no unsupported nodes" (!d.hasUnsupported)
  return d

#eval show IO Unit from do
  -- byte-real envelopes must ingest to EXACTLY the hand-built designs ...
  let adder ← checkIngest "Examples/sv/adder.sv.json" adderD
  let counter ← checkIngest "Examples/sv/counter.sv.json" counterD
  let race ← checkIngest "Examples/sv/race_blk.sv.json" raceBlkD
  let swap ← checkIngest "Examples/sv/swap_nba.sv.json" swapNbaD
  let xsel ← checkIngest "Examples/sv/xsel.sv.json" xselD
  -- ... and the ingested designs must reproduce the Xcelium-verified outcomes
  check "counter.sv.json: x → reset → count trace" <|
    sigTrace (run counter σ_src 64 counterStim) "count" ==
      some ["xxxxxxxx", "xxxxxxxx", "00000000", "00000001", "00000010", "00000011"]
  check "race_blk.sv.json: (2,2) under σ_src" <|
    (sigTrace (run race σ_src 64 raceStim) "a" == some ["00000010"]) &&
    (sigTrace (run race σ_src 64 raceStim) "b" == some ["00000010"])
  check "race_blk.sv.json: (1,1) under σ_rev" <|
    (sigTrace (run race σ_rev 64 raceStim) "a" == some ["00000001"]) &&
    (sigTrace (run race σ_rev 64 raceStim) "b" == some ["00000001"])
  check "swap_nba.sv.json: swaps under both σ" <|
    (sigTrace (run swap σ_src 64 swapStim) "a" == some ["00000010", "00000001"]) &&
    (run swap σ_rev 64 swapStim == run swap σ_src 64 swapStim)
  check "xsel.sv.json: sel=x takes else" <|
    sigTrace (run xsel σ_src 64 (xselStim (.lit "x"))) "y" == some ["01010101"]
  check "adder.sv.json: 5+3 and x-collapse" <|
    (sigTrace (run adder σ_src 64 [[("a", b8 5), ("b", b8 3)]]) "s" == some ["00001000"]) &&
    (sigTrace (run adder σ_src 64 [[("a", .lit "0000000x"), ("b", b8 3)]]) "s" ==
      some ["xxxxxxxx"])

/-! ## `#sv_check` demos (Surface.lean surface syntax)

Conversions of `#guard` checks from the sections above — same designs, same
Xcelium-verified outcomes, in the readable stimulus/expectation form
(`docs/sv-spec-surface.md`, "Implementation status"). The raw `#guard` forms
above are kept: `#sv_check` covers `%b`-column checks of completed runs;
`#guard` remains for everything else (`.timeout`/`.unsupported` outcomes,
trace equality across schedules, expression-level plumbing). -/

-- counter: x through pre-reset edges, reset, count (= the counterStim #guard)
#sv_check counterD
    [[clk := 1, rst := 0], [clk := 1, rst := 0], [clk := 1, rst := 1],
     [clk := 1, rst := 0], [clk := 1, rst := 0], [clk := 1, rst := 0]]
  shows count = [x, x, 0, 1, 2, 3]

-- counter: the stimulus cannot clobber the output; a held (absent) rst input
#sv_check counterD [[rst := 1, count := 77]] shows count = [0]
#sv_check counterD [[clk := 1, rst := 1], []] shows count = [0, 0]

-- swap_nba: swaps every cycle — and under the reversed schedule too
#sv_check swapNbaD [[clk := 1], [clk := 1]] shows a = [2, 1], b = [1, 2]
#sv_check swapNbaD [[clk := 1], [clk := 1]] under σ_rev shows a = [2, 1], b = [1, 2]

-- race_blk: (2,2) under source order, (1,1) under reverse — the race
#sv_check raceBlkD [[clk := 1]] shows a = [2], b = [2]
#sv_check raceBlkD [[clk := 1]] under σ_rev shows a = [1], b = [1]

-- xsel: known select, and X-optimism (sel = x/z takes the ELSE branch)
#sv_check xselD [[sel := 1, a := 0xAA, b := 0x55]] shows y = ["10101010"]
#sv_check xselD [[sel := 0, a := 0xAA, b := 0x55]] shows y = ["01010101"]
#sv_check xselD [[sel := "x", a := 0xAA, b := 0x55]] shows y = ["01010101"]
#sv_check xselD [[sel := "z", a := 0xAA, b := 0x55]] shows y = ["01010101"]

-- adder: known add, wrap, whole-vector x-collapse, all-x startup inputs
#sv_check adderD [[a := 5, b := 3], [a := 200, b := 100]] shows s = [8, "00101100"]
#sv_check adderD [[a := "0000000x", b := 3]] shows s = [x]
#sv_check adderD [[]] shows s = [x]

-- edge-phase mechanics (blocking immediacy; NBA last-write-wins; NBA
-- pre-commit reads)
#sv_check blkSeqD [[clk := 1]] shows r = [1]
#sv_check nbaLastD [[clk := 1]] shows q = [2]
#sv_check nbaReadD [[clk := 1]] shows q = [5], r = [9]

end LeanModels.Sv
