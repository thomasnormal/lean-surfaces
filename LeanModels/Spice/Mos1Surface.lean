import LeanModels.Spice.Mos1
import Mathlib.Tactic

/-! Checked names and equation-extraction tactics for resolved MOS1 views. -/

namespace LeanModels.Spice

syntax:max "mos_node! " term:max str : term

open Lean Elab Term in
elab_rules : term
  | `(mos_node! $circuit:term $name:str) => do
      let circuitExpr ←
        elabTerm circuit (some (mkConst ``Mos1ResolvedCircuit))
      let candidate := mkApp (mkConst ``node) (mkStrLit name.getString)
      let membershipSyntax ←
        `((node $name) ∈ Mos1ResolvedCircuit.nodes $circuit)
      let membership ← elabTerm membershipSyntax (some (mkSort .zero))
      let proof ←
        try
          let proof ← Meta.mkDecideProof membership
          Meta.check proof
          pure proof
        catch _ =>
          throwErrorAt name
            "mos_node!: `{name.getString}` is not present in the resolved \
            MOS1 circuit; use `#mos1_nodes <circuit>` to inspect its nodes"
      pure <| mkApp3 (mkConst ``Mos1ResolvedCircuit.checkedNode)
        circuitExpr candidate proof

open Lean Elab Command in
elab "#mos1_nodes " circuit:term : command => do
  elabCommand
    (← `(#eval IO.println
      (Mos1ResolvedCircuit.describeNodes $circuit:term)))

declare_syntax_cat mos1ExtractItem
syntax str " => " ident "," ident : mos1ExtractItem
syntax (name := mos1Extract)
  "mos1_extract " ident ident " at " term:max
    " [" mos1ExtractItem,* "]" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| mos1_extract $hs:ident $hb:ident at $circuit:term
        [$items,*]) => do
      for item in items.getElems do
        match item with
        | `(mos1ExtractItem| $name:str => $hkcl:ident, $hbounds:ident) =>
            if name.getString == "0" then
              throwErrorAt name
                "mos1_extract: ground has no KCL obligation"
            withMainContext do
              let _ ← Term.elabTerm
                (← `(mos_node! $circuit $name)) (some (mkConst ``NodeId))
            evalTactic (← `(tactic| first
              | have $hkcl :=
                  Mos1Satisfies.kclAt $hs
                    (target :=
                      (⟨node $name, by decide⟩ :
                        Mos1ResolvedCircuit.Node $circuit))
                    (by decide)
              | have $hkcl :=
                  Mos1ComponentSatisfies.kclAt $hs
                    (target :=
                      (⟨node $name, by decide⟩ :
                        Mos1ResolvedCircuit.Node $circuit))
                    (by decide) (by decide)))
            evalTactic (← `(tactic|
              have $hbounds :=
                Mos1WithinSupply.boundsAt $hb
                  (target :=
                    (⟨node $name, by decide⟩ :
                      Mos1ResolvedCircuit.Node $circuit))))
        | _ => throwErrorAt item "mos1_extract: malformed node entry"

end LeanModels.Spice
