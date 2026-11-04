import LeanModels.Sv.Load
import LeanModels.Sv.Obs

namespace Examples.systemVerilog.staticLocals.proof
open LeanModels.Sv LeanModels.Sv.SelfCheck
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

-- REFERENCE: 7deb2ae9ce23b3daa158a048 24.03-s004 2026-10-20 | tests=automatic | source=Examples/system-verilog/static_locals/automatic.sv@sha256:74119694a29fe12d0f61f9f2e4c0e09d218efceba416b4e8bb9dca7940416a78 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
-- REFERENCE: a474b88404d946bd9c175b3c 24.03-s004 2026-10-20 | tests=certificate | source=Examples/system-verilog/static_locals/certificate.sv@sha256:a30bce69093252b7575e14be45e9f905c8ad55c6d79bf9fdd9f41d0ff3689e04 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
-- REFERENCE: 92ad75893d727250b88b982a 24.03-s004 2026-10-20 | tests=default_lifetime | source=Examples/system-verilog/static_locals/default_lifetime.sv@sha256:6e767758354f37fd5dcaf0870316446f4672462fccebd13204749e0019f6ceff | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
-- REFERENCE: d5b996840a9241012d0c6493 24.03-s004 2026-10-20 | tests=initializer_effect | source=Examples/system-verilog/static_locals/initializer_effect.sv@sha256:b86e3915122d0f39b3da881afd30d97dc0e8eae0137934dbf02d0c819411aca2 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
-- REFERENCE: 776555f02dea92c46ced95b5 24.03-s004 2026-10-20 | tests=initializer_order | source=Examples/system-verilog/static_locals/initializer_order.sv@sha256:03e197775515f1206d8ca6c2aa92735d698ee6a3c07a7c659cf6bb6e3077132a | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
-- REFERENCE: 255f3bee71bd2fb0fa23be5b 24.03-s004 2026-10-20 | tests=initializer_read | source=Examples/system-verilog/static_locals/initializer_read.sv@sha256:b38e50c1ad1551e64dbd459e00b4e9581135bd03d063be3ecbd8ad4c043259d5 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
-- REFERENCE: c33d70fdad4993c446d887a3 24.03-s004 2026-10-20 | tests=nba | source=Examples/system-verilog/static_locals/nba.sv@sha256:ba6b1c518c4b7c5ef49bb492e0c6478805d6cb235468690cafc002eec1f8305e | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
-- REFERENCE: f2acc5a16b42767004a1df2d 24.03-s004 2026-10-20 | tests=preentry | source=Examples/system-verilog/static_locals/preentry.sv@sha256:6e134cef86fa23267206140df38e8b25227a17e73cf4f7200b5b27fb9e162a0b | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
-- REFERENCE: e99e93c829e313a6bd95e3c1 24.03-s004 2026-10-20 | tests=reentry | source=Examples/system-verilog/static_locals/reentry.sv@sha256:fd5c1b3d38f16a2a3ca9ef257b7d1c43d80e0edbd787d9d40d357130e97f1d9b | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
-- REFERENCE: 63d03789ee75d95c9c60c270 24.03-s004 2026-10-20 | tests=shadow | source=Examples/system-verilog/static_locals/shadow.sv@sha256:643d3494bd9e12cdadcb5af3a20c07be3753d8cf68c7789ce0e89409dda750d2 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
-- REFERENCE: 2c18aac11282bafbc7d8e496 24.03-s004 2026-10-20 | tests=structure | source=Examples/system-verilog/static_locals/structure.sv@sha256:dfca10b91fb1b039b3ca1082fb9122343a1299a3677d753e9b193a749eb0649c | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
-- REFERENCE: aab68993bb563b089657e1e8 24.03-s004 2026-10-20 | tests=capture | source=Examples/system-verilog/static_locals/capture.sv@sha256:38d0fe5fbef2ae6bfdb267543ddb8978b60f9d31036d8125d04839ee9dfbcda1 | top=top | args=["-ii_val","-abvcoveron","-abvrecordcoverall","-abvdisableasrtst"] | map=Examples/system-verilog/static_locals/README.md#procedural-variable-lifetimes
-- SYNTHETIC-ORACLE: tests=storage-and-admission | origin=spec | authority=docs/sv-procedural-lifetimes.md#procedural-variable-lifetimes | map=static:pre-process-once;automatic:per-entry;binding:declaration-identity;initializers:closed-pure;barriers:default-provenance-order-effects-invalid

/-- The actual static declaration from certificate.sv. -/
def counter : SDecl :=
  { name := "count", width := 4, init := some (.m0 (.lit (.ofNat 4 14))) }
def increment : SStmt := .m0 (.blockingAssign "count"
  (.binary .add (.ident "count") (.lit (.ofNat 4 1))))

/-- Static initialization is a pre-process declaration action. -/
theorem initialized_before_entry (state : SvState) (fuel : Nat) :
    initDecls (fuel + 2) [counter] state =
      .ok (SvState.set state "count" (.ofNat 4 14)) := by
  rfl

/-- Re-entering the source declaration does not reset any store or work. -/
theorem entry_retains (state : SvState) (pending : NbaQueue) (output : Out) (fuel : Nat) :
    execSStmt (fuel + 2) state pending output .skip = .ok (state,pending,output) := by
  simp [execSStmt]

/-- Each actual increment reads the retained value, not the initializer. -/
theorem increment_retained (state : SvState) (value : LVec) (pending : NbaQueue)
    (output : Out) (running : output.halted = false) (fuel : Nat) :
    execSStmt (fuel + 12) (("count",value)::state) pending output increment =
      .ok (SvState.set (("count",value)::state) "count" (value.add (.ofNat 4 1)),
           pending, output) := by
  unfold increment
  rw [execSStmt.eq_def]
  simp only [running, Bool.false_eq_true, if_false]
  rfl

/-- The retained four-bit source increment has the ordinary wrap rule. -/
theorem increment_modular (state : SvState) (value : BitVec 4) (fuel : Nat) :
    evalSExpr (fuel + 8) (("count",.ofBitVec value)::state)
      (.m0 (.binary .add (.ident "count") (.lit (.ofNat 4 1)))) =
      .ok (.ofBitVec (value + 1)) := by
  change Res.ok ((LVec.ofBitVec value).add (.ofNat 4 1)) = _
  rw [show LVec.ofNat 4 1 = .ofBitVec (1 : BitVec 4) from rfl, LVec.add_ofBitVec]

#print axioms initialized_before_entry
#print axioms entry_retains
#print axioms increment_retained
#print axioms increment_modular

partial def containsStatement (wanted : SStmt) (statement : SStmt) : Bool :=
  statement == wanted || match statement with
  | .block statements => statements.any (containsStatement wanted)
  | .repeatLoop _ _ body => containsStatement wanted body
  | .ifStmt _ yes no => containsStatement wanted yes || no.any (containsStatement wanted)
  | _ => false

def fixtureReceipt : IO Unit := do
  let .ok certificate := loadEnvelopeDesign
      (← IO.FS.readFile "Examples/system-verilog/static_locals/certificate.sv.json")
    | throw (IO.userError "certificate failed to load")
  let some declaration := certificate.decls.find? (·.name == "count")
    | throw (IO.userError "hoisted static declaration missing")
  unless declaration.width == 4 && declaration.init == some (.m0 (.lit (.ofNat 4 14))) do
    throw (IO.userError "startup theorem differs from source initializer")
  let some (SProc.initial (.block body)) := certificate.procs[0]?
    | throw (IO.userError "certificate process shape changed")
  unless body[0]? == some .skip && body.any (containsStatement increment) do
    throw (IO.userError "entry/increment theorem differs from parsed source")
  for (name, expected) in [("automatic", ["automatic 1 3", "automatic 2 6", "automatic 3 9"]),
      ("capture", ["capture 1 2", "capture 2 8"]),
      ("certificate", ["certificate 0 0"]),
      ("nba", ["nba 5 9", "stable 9"]),
      ("preentry", ["before 6 1xz1 1001", "after 9"]),
      ("reentry", ["entry 5 5", "entry 6 5", "entry 7 5", "retained 7"]),
      ("shadow", ["inner 2 3 8", "distinct 2 9 8"]),
      ("structure", ["initial 2 3 12", "instances 10 3 17"])] do
    let .ok design := loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/static_locals/{name}.sv.json")
      | throw (IO.userError s!"{name} load failed")
    for oracle in [ρ_src, ρ_rev] do
      let .ok initial := elabTimedDesign 32768 design
        | throw (IO.userError s!"{name} timed load failed")
      let mut world := initial
      for _ in List.range 12 do
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec (slotStep oracle 32768) world
          | throw (IO.userError s!"{name} slot refused")
        world := next
        if world.out.halted then break
        let .ok (.ok _, next) := SvM.exec (do advanceTime 1; wakeTimers) world
          | throw (IO.userError s!"{name} timer refused")
        world := next
      unless world.out.halted && world.out.flush == expected do
        throw (IO.userError s!"{name} complete transcript differs")
  for name in ["default_lifetime", "initializer_effect", "initializer_order", "initializer_read"] do
    match loadEnvelopeDesign
        (← IO.FS.readFile s!"Examples/system-verilog/static_locals/{name}.sv.json") with
    | .error _ => pure ()
    | .ok design =>
      match elabTimedDesign 32768 design with
      | .error _ => pure ()
      | .ok world =>
        match SvM.exec (slotStep ρ_src 32768) world with
        | .ok (.ok _, _) => throw (IO.userError s!"{name} lost refusal")
        | _ => pure ()

#eval fixtureReceipt
end Examples.systemVerilog.staticLocals.proof
