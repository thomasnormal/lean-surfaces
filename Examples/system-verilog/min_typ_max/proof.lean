import LeanModels.Sv.Load

namespace Examples.systemVerilog.minTypMax.proof

open LeanModels.Sv LeanModels.Sv.SelfCheck

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- The actual parsed typical-choice RHS and assignments in runtime.sv.
def expression : SExpr := .m0 (.ident "typical_source")
def blocking : SStmt := .m0 (.blockingAssign "captured" (.ident "typical_source"))
def nba : SStmt := .m0 (.nbaAssign "captured" (.ident "typical_source"))
def sources (state : SvState) (minimum typical maximum : LVec) : SvState :=
  ("minimum_source", minimum) :: ("typical_source", typical) ::
    ("maximum_source", maximum) :: state

/-- The selected source is read at execution time, rather than sampled at elaboration. -/
theorem live_value (state : SvState) (minimum typical maximum : LVec) (fuel : Nat) :
    evalSExpr (fuel + 8) (sources state minimum typical maximum) expression =
      .ok typical := by
  rfl

/-- Changing either unselected source cannot change the value of the expression. -/
theorem unselected_independent (state : SvState)
    (minimum minimum' typical maximum maximum' : LVec) (fuel : Nat) :
    evalSExpr (fuel + 8) (sources state minimum typical maximum) expression =
      evalSExpr (fuel + 8) (sources state minimum' typical maximum') expression := by
  rfl

/-- Blocking assignment stores the current selected value without altering pending work. -/
theorem blocking_store (state : SvState) (minimum typical maximum : LVec)
    (pending : NbaQueue) (output : Out) (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 16) (sources state minimum typical maximum) pending output blocking =
      .ok (SvState.set (sources state minimum typical maximum) "captured" typical,
        pending, output) := by
  unfold blocking
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  rfl

/-- The NBA captures the selected value now and leaves current storage unchanged. -/
theorem nba_captures (state : SvState) (minimum typical maximum : LVec)
    (pending : NbaQueue) (output : Out) (fuel : Nat) (running : output.halted = false) :
    execSStmt (fuel + 16) (sources state minimum typical maximum) pending output nba =
      .ok (sources state minimum typical maximum, pending ++ [("captured", typical)], output) := by
  unfold nba
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  rfl

private theorem lookup_set_self (state : SvState) (name : String) (value : LVec) :
    SvState.lookup (SvState.set state name value) name = some value := by
  induction state with
  | nil => simp [SvState.set, SvState.lookup]
  | cons binding rest ih =>
    rcases binding with ⟨key, old⟩
    simp only [SvState.set]
    split <;> simp_all [SvState.lookup]

/-- Later changes to the selected source cannot alter the already captured NBA. -/
theorem captured_after_change (state : SvState) (old replacement : LVec) (fuel : Nat) :
    evalSExpr (fuel + 4)
      (commitNba (SvState.set state "typical_source" replacement) [("captured", old)])
      (.m0 (.ident "captured")) = .ok old := by
  simp [commitNba, evalSExpr, evalExpr, readSignal, lookup_set_self]

#print axioms live_value
#print axioms unselected_independent
#print axioms blocking_store
#print axioms nba_captures
#print axioms captured_after_change

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | .forLoop _ _ _ body | .repeatLoop _ _ body => containsStatement wanted body
  | _ => false

-- REFERENCE: 0728d2d4a990a029ee44f6e1 24.03-s004 2026-10-20 | tests=choices | source=Examples/system-verilog/min_typ_max/choices.sv@sha256:a85302083f858d586ac7d39e2def9dba807dfbd9b97dfcddff76635eccd062f6 | top=top | args=["-ii_val","-typdelays"] | map=README.md#min-typ-max
-- REFERENCE: 49c6fa3ca4f3d7e47f7dcc3b 24.03-s004 2026-10-20 | tests=composition | source=Examples/system-verilog/min_typ_max/composition.sv@sha256:33946782fb97af254d492cfc3e0a0a44386197a41fd7768f8cba9c7d376a849b | top=top | args=["-ii_val","-typdelays"] | map=README.md#min-typ-max
-- REFERENCE: 38303d599b21911c77aab27e 24.03-s004 2026-10-20 | tests=runtime | source=Examples/system-verilog/min_typ_max/runtime.sv@sha256:ccca4ce35fb7861fbe1747dfbdd8034c76d569419a600e4eec430f3ec859cb4f | top=top | args=["-ii_val","-typdelays"] | map=README.md#min-typ-max
-- REFERENCE: 927a5566cea80ee8ccb9a225 24.03-s004 2026-10-20 | tests=elaboration | source=Examples/system-verilog/min_typ_max/elaboration.sv@sha256:1cbf484159215aafc8bcaf39fb399660dbb7c08453385e15eacb1c19a9bd6194 | top=top | args=["-ii_val","-typdelays"] | map=README.md#min-typ-max
-- REFERENCE: 4bdb569966f9172d6fd69af9 24.03-s004 2026-10-20 | tests=timing | source=Examples/system-verilog/min_typ_max/timing.sv@sha256:d5aad3f19c9ab96a87f9b901af987a5b8237892c45e208c3718b8170787e167b | top=top | args=["-ii_val","-typdelays"] | map=README.md#min-typ-max
-- REFERENCE: 7852196ee4fbb3f239912613 24.03-s004 2026-10-20 | tests=unknown | source=Examples/system-verilog/min_typ_max/unknown.sv@sha256:0e495a69a067340b5cf7d60d8a36aee9e4d48d21fa69ab4331fd2c0acd2ebc0e | top=top | args=["-ii_val","-typdelays"] | map=README.md#min-typ-max
-- REFERENCE: 8f9dab996795162b9f1c4293 24.03-s004 2026-10-20 | tests=unselected | source=Examples/system-verilog/min_typ_max/unselected.sv@sha256:1b0b86e6f0dc54a2f3406ad1efd3039f810fd7722573886ef55f71d40d05c27a | top=top | args=["-ii_val","-typdelays"] | map=README.md#min-typ-max
-- REFERENCE: ff52df8c8ba81fa91d0a3a78 24.03-s004 2026-10-20 | tests=unselected_math | source=Examples/system-verilog/min_typ_max/unselected_math.sv@sha256:bede42e2ee0f5be2e9e80d917687aba0b532ca0afa3034bdd76c8b481f13ba0b | top=top | args=["-ii_val","-typdelays"] | map=README.md#min-typ-max
-- REFERENCE: c878ad77f567fd6033c055d1 24.03-s004 2026-10-20 | tests=effects | source=Examples/system-verilog/min_typ_max/effects.sv@sha256:91dbf53d197088535f4a965c0597f873c0f274c47178054b54f8ae9861fb0d5c | top=top | args=["-ii_val","-typdelays"] | map=README.md#min-typ-max
-- REFERENCE: cf25df2003a11d9b08aed26c 24.03-s004 2026-10-20 | tests=argument_context | source=Examples/system-verilog/min_typ_max/argument_context.sv@sha256:a22a1fe86b7de8adcd491f88612589517c712432d020458a46c6db1313f1c5a2 | top=top | args=["-ii_val","-typdelays"] | map=README.md#min-typ-max
-- SYNTHETIC-ORACLE: tests=fixtureReceipt-schema | origin=spec | authority=docs/sv-envelope-schema.md#min-typ-max | map=choice:enum;zero-width:positive-width;mismatch:selected-width;certificates:parsed-source;effects:pure-source

def fixtureReceipt : IO Unit := do
  for (name, expected) in [
    ("choices", ["choices 22 2 -127", "widths 8 8"]),
    ("composition", ["composition 1142 4 20 5", "relations 0 concat 2b", "patterns 25 0000000a"]),
    ("runtime", ["before 22", "captured 22 live 55"]),
    ("elaboration", ["typical 8 ff"]),
    ("timing", ["marker3", "selected"]),
    ("unknown", ["states zz 01000101"]),
    ("unselected", ["unselected 7 0"]),
    ("unselected_math", ["unselected-math 7"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/min_typ_max/{name}.sv.json")
      | throw (IO.userError s!"{name} failed to load")
    if name == "runtime" then
      for statement in [blocking, nba] do
        unless design.procs.any (fun process => match process with
            | .initial body => containsStatement statement body
            | _ => false) do
          throw (IO.userError "min/typ/max certificate differs from parsed source")
    if name != "runtime" && name != "timing" then
      unless runSelfCheck design 32768 == .ok expected do
        throw (IO.userError s!"{name} time-zero transcript differs")
    for oracle in [ρ_src, ρ_rev] do
      let .ok initial := elabTimedDesign 32768 design
        | throw (IO.userError s!"{name} timed loader refused")
      let .ok (.ok _, first) := SvM.exec (slotStep oracle 32768) initial
        | throw (IO.userError s!"{name} initial slot refused")
      let mut world := first
      for _ in List.range 16 do
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec
            (do advanceTime 1; wakeTimers; slotStep oracle 32768) world
          | throw (IO.userError s!"{name} resumed slot refused")
        world := next
      unless world.out.halted && world.out.flush == expected do
        throw (IO.userError s!"{name} complete transcript differs")
  for name in ["effects", "argument_context"] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/min_typ_max/{name}.sv.json")
      | throw (IO.userError s!"{name} lost its executable refusal")
    match runSelfCheck design 32768 with
    | .unsupported _ => pure ()
    | _ => throw (IO.userError s!"{name} lost its refusal boundary")
  for (choice, width, childWidth) in [("other", 8, 8), ("typ", 0, 0), ("typ", 8, 4)] do
    let value := Lean.Json.mkObj [("kind", .str "Ident"), ("width", Lean.toJson childWidth),
      ("name", .str "typical_source")]
    let node := Lean.Json.mkObj [("kind", .str "MinTypMax"), ("choice", .str choice),
      ("width", Lean.toJson width), ("value", value)]
    match parseSExpr node with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "malformed min/typ/max wrapper accepted")

#eval fixtureReceipt

end Examples.systemVerilog.minTypMax.proof
