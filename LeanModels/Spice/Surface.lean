import Lean
import LeanModels.Python.Surface
import LeanModels.Spice.Json
import LeanModels.Spice.Semantics
import LeanModels.Spice.Solve

/-!
# SPICE specification surface

`load_netlist` turns an extracted JSON envelope into a literal `Netlist` at
elaboration time. The `⊨dc` judgment is universal: every assignment obeying
the flattened physical laws must satisfy the stated property.
-/

namespace LeanModels.Spice

/-! ## Literal ingestion -/

deriving instance Lean.ToExpr for Span
deriving instance Lean.ToExpr for ElementKind
deriving instance Lean.ToExpr for Element
deriving instance Lean.ToExpr for Instance
deriving instance Lean.ToExpr for Unsupported
deriving instance Lean.ToExpr for Card
deriving instance Lean.ToExpr for Subckt
deriving instance Lean.ToExpr for SubcktEntry
deriving instance Lean.ToExpr for Netlist

open Lean Elab Command in
/-- Read a `spice-0.1` envelope at elaboration time and declare a literal
`Netlist`. The path is relative to the package root under `lake build`. -/
elab "load_netlist " name:ident " from " path:str : command => do
  let pathString := path.getString
  let contents ←
    match ← (IO.FS.readFile ⟨pathString⟩).toBaseIO with
    | .ok contents => pure contents
    | .error error =>
        throwErrorAt path "load_netlist: cannot read '{pathString}': {toString error}"
  let envelope ←
    match parseEnvelopeString contents with
    | .ok envelope => pure envelope
    | .error error =>
        throwErrorAt path "load_netlist: invalid envelope '{pathString}': {error}"
  let declarationName := (← getCurrNamespace) ++ name.getId
  if (← getEnv).contains declarationName then
    throwErrorAt name "load_netlist: '{declarationName}' has already been declared"
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := declarationName
      levelParams := []
      type := Lean.mkApp (Lean.mkConst ``LeanModels.Spice.Netlist)
        (Lean.mkConst ``Rat)
      value := Lean.toExpr envelope.netlist
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst declarationName
    addDocStringCore declarationName
      s!"SPICE netlist loaded from `{pathString}` (source `{envelope.sourceFile}`, sha256 `{envelope.sourceSha256}`)."
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst declarationName) (isBinder := true)

macro "#print_netlist " name:ident : command => `(#eval (repr $name))

/-! ## Universal DC judgment -/

/-- Every physically admissible DC assignment satisfies `property`. -/
def DCModels (netlist : Netlist) (property : Assignment → Prop) : Prop :=
  ∀ assignment, SatisfiesNetlist netlist assignment → property assignment

/-- Surface form with explicit voltage/current accessor binders:
`divider ⊨dc { v, i => v "out" = 10 / 3 }`. -/
syntax:50 term:51 " ⊨dc " "{" ident ", " ident " => " term "}" : term
macro_rules
  | `($netlist ⊨dc { $voltage, $current => $property }) =>
      `(DCModels $netlist (fun assignment =>
          let $voltage := assignment.volt
          let $current := assignment.cur
          $property))

/-- Predicate-level form for contracts that already name an assignment. -/
infix:50 " ⊨dc? " => DCModels

/-- Concrete non-vacuity check through hierarchy flattening and the exact
checked MNA solver. -/
macro "#spice_check " netlist:term " shows " node:str " = " value:term : command =>
  `(#guard
      match flatten $netlist with
      | .ok flat =>
          match solve flat with
          | .ok assignment => assignment.volt $node == $value
          | .error _ => false
      | .error _ => false)

open Lean Parser Tactic in
/-- Unfold a concrete netlist's finite DC equations and discharge exact Rat
algebra with core `grind`. This tactic does not trust the executable solver. -/
macro "spice_solve" "[" netlist:ident "]" : tactic =>
  `(tactic|
    unfold $netlist <;>
    simp [DCModels, SatisfiesNetlist, Satisfies, SupportEq, WellPosed,
          flatten, flattenBudget, flattenCards, findSubckt, lookupRename,
          qualify, renameNode, renameElement, FlatNetlist.nodes,
          FlatNetlist.branchNames, DeviceLaw, deviceLawHolds,
          kclSum, currentInto] at * <;> grind)

end LeanModels.Spice
