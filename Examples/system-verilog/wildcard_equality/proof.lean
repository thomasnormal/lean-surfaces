import LeanModels.Sv.Ingest2
import LeanModels.Sv.Param2
import LeanModels.Sv.SelfCheck

namespace Examples.systemVerilog.wildcardEquality.proof

open LeanModels.Sv

load_design_sv2 equality from "Examples/system-verilog/wildcard_equality/wildcard_equality.sv.json"

def source (different : Bool) : PExpr :=
  match equality.pdesign.processes with
  | [.assign "equal" eq, .assign "different" ne] => if different then ne else eq
  | _ => .unsupported "WildcardEquality:source" "assignments changed"

theorem equality_source :
    source false = .binary (.m0 .wildEq) (.ident "left") (.ident "right") := rfl

theorem inequality_source :
    source true = .binary (.m0 .wildNe) (.ident "left") (.ident "right") := rfl

def sourceExpr (different : Bool) (width : Nat) : Expr :=
  instExpr { widths := [("left", width), ("right", width)] } (some 32) (source different)

theorem source_instantiation (different : Bool) (width : Nat) :
    sourceExpr different width =
      .binary (if different then .wildNe else .wildEq) (.ident "left") (.ident "right") := by
  cases different <;>
    simp [sourceExpr, equality_source, inequality_source, instExpr, selfWidth, List.lookup]

theorem eq_all_wildcards (left right : LVec) (sameWidth : left.width = right.width)
    (masked : ∀ bit ∈ right.bits, bit.isKnown = false) :
    left.eqWildcard right = .l1 := by
  have mismatch : (Array.zip left.bits right.bits).any
      (fun (x, y) => y.isKnown && x.isKnown && x != y) = false := by
    apply Array.any_eq_false'.mpr
    rintro ⟨x, y⟩ h
    simp [masked y (Array.of_mem_zip h).2]
  have unknown : (Array.zip left.bits right.bits).any
      (fun (x, y) => y.isKnown && !x.isKnown) = false := by
    apply Array.any_eq_false'.mpr
    rintro ⟨x, y⟩ h
    simp [masked y (Array.of_mem_zip h).2]
  unfold LVec.eqWildcard
  rw [if_neg (fun h => h sameWidth)]
  dsimp only
  rw [mismatch, unknown]
  rfl

/-- Any all-wildcard right operand makes the real equality assignment true. -/
theorem source_matches_all_wildcards (left right : LVec) (fuel : Nat)
    (sameWidth : left.width = right.width)
    (masked : ∀ bit ∈ right.bits, bit.isKnown = false) :
    evalExpr (fuel + 2) [("left", left), ("right", right)]
      (sourceExpr false left.width) = .ok (.ofLogic .l1) := by
  rw [source_instantiation]
  change Res.ok (LVec.ofLogic (left.eqWildcard right)) = _
  rw [eq_all_wildcards left right sameWidth masked]

/-- The corresponding real inequality assignment is false under the same mask. -/
theorem source_rejects_all_wildcards (left right : LVec) (fuel : Nat)
    (sameWidth : left.width = right.width)
    (masked : ∀ bit ∈ right.bits, bit.isKnown = false) :
    evalExpr (fuel + 2) [("left", left), ("right", right)]
      (sourceExpr true left.width) = .ok (.ofLogic .l0) := by
  rw [source_instantiation]
  change Res.ok (LVec.ofLogic (left.eqWildcard right).not) = _
  rw [eq_all_wildcards left right sameWidth masked]
  rfl

#print axioms source_matches_all_wildcards
#print axioms source_rejects_all_wildcards

/-! REFERENCE: values.sv, group wildcard-equality-values. The nested signed
comparison is one-bit and self-determined before the enclosing division. -/
def nested (different : Bool) : PExpr :=
  .binary (.m0 .div)
    (.binary (.m0 (if different then .wildNe else .wildEq))
      (.signedResize 4 (.unary (.m0 .neg) (.lit (.lit "1000"))))
      (.signedResize 4 (.lit (.lit "1000"))))
    (.lit (.lit "1"))

#guard evalExpr 64 [] (instExpr {} (some 8) (nested false)) == .ok (.ofNat 8 1)
#guard evalExpr 64 [] (instExpr {} (some 8) (nested true)) == .ok (.ofNat 8 0)
#guard evalExpr2 64 [] (instExpr2 {} [] (some 8) (nested false)) == .ok (.ofNat 8 1)
#guard evalExpr2 64 [] (instExpr2 {} [] (some 8) (nested true)) == .ok (.ofNat 8 0)

#eval show IO Unit from do
  let text ← IO.FS.readFile "Examples/system-verilog/wildcard_equality/values.sv.json"
  let .ok fixture := SelfCheck.loadEnvelopeDesign text
    | throw (IO.userError "wildcard-equality fixture failed to load")
  unless SelfCheck.runSelfCheck fixture 4096 == .ok ["PASS"] do
    throw (IO.userError "wildcard-equality fixture disagrees")

end Examples.systemVerilog.wildcardEquality.proof
