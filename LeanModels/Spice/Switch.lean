import LeanModels.Spice.Semantics

/-!
# Ideal-switch MOS semantics

This tier gives transistor-level CMOS decks a small, explicit *ideal-switch
abstraction*. An NMOS conducts exactly when its gate is high; a PMOS conducts
exactly when its gate is low; a conducting device equates its drain and source
logic levels. Off devices impose no relation.

This is not a physical NMOS/PMOS I-V model: it has no voltage, current,
threshold, KCL, body effect, leakage, delay, or contention semantics. The same
extracted deck is checked with ngspice to validate that its analog operating
points lie inside the chosen logic-level bands.
-/

namespace LeanModels.Spice

/-- Boolean logic levels assigned to every named circuit node. -/
structure LogicState where
  level : String → Bool

/-- Rename every terminal of a MOS transistor during hierarchical expansion. -/
def renameMosfet (path : String) (renames : List (String × String))
    (mosfet : Mosfet) : Mosfet :=
  { mosfet with
    name := qualify path mosfet.name
    drain := renameNode path renames mosfet.drain
    gate := renameNode path renames mosfet.gate
    source := renameNode path renames mosfet.source
    bulk := renameNode path renames mosfet.bulk }

/-- Hierarchical expansion for the switch tier. Unlike the linear `flatten`,
this retains MOS transistors and model declarations as cards. -/
def flattenSwitchCards (defs : Array (SubcktEntry Rat)) :
    Nat → List String → String → List (String × String) → List Card →
      Except FlattenError (List Card)
  | 0, _, _, _, _ => .error .depth
  | _ + 1, _, _, _, [] => .ok []
  | fuel + 1, active, path, renames, card :: rest => do
      let head ← match card with
        | .element element =>
            pure [.element (renameElement path renames element)]
        | .mosfet mosfet =>
            pure [.mosfet (renameMosfet path renames mosfet)]
        | .mosModel model => pure [.mosModel model]
        | .op _ => pure []
        | .unsupported card =>
            throw (.unsupported card.spiceKind card.text)
        | .subckt subckt => throw (.nestedSubckt subckt.name)
        | .xInstance inst =>
            let subckt ← match findSubckt defs inst.subckt with
              | some subckt => pure subckt
              | none => throw (.missingSubckt inst.subckt)
            if active.contains subckt.name then
              throw (.recursion subckt.name)
            if subckt.ports.size != inst.connections.size then
              throw (.portArity inst.name subckt.ports.size inst.connections.size)
            let actuals := inst.connections.toList.map (renameNode path renames)
            let localRenames := subckt.ports.toList.zip actuals
            flattenSwitchCards defs fuel (subckt.name :: active)
              (qualify path inst.name) localRenames subckt.body.toList
      let tail ← flattenSwitchCards defs fuel active path renames rest
      pure (head ++ tail)

/-- Expand `.SUBCKT` instances while preserving switch-level device cards. -/
def flattenSwitch (netlist : Netlist) : Except FlattenError Netlist := do
  let cards ← flattenSwitchCards netlist.subckts (flattenBudget netlist)
    [] "" [] netlist.cards.toList
  pure { title := netlist.title, subckts := #[], cards := cards.toArray }

/-- Find the first structured MOS model declaration with the requested name. -/
def Netlist.findMosModel (netlist : Netlist) (name : String) : Option MosPolarity :=
  netlist.cards.toList.findSome? fun
    | .mosModel model =>
        if model.name == name then some model.polarity else none
    | _ => none

/-- The ideal-switch law for one MOS transistor. Bulk terminals are retained
in the AST and exercised by ngspice, but body effects are outside this tier. -/
def MosfetSwitchLaw (netlist : Netlist) (state : LogicState)
    (mosfet : Mosfet) : Prop :=
  match netlist.findMosModel mosfet.model with
  | some .nmos =>
      state.level mosfet.gate = true →
        state.level mosfet.drain = state.level mosfet.source
  | some .pmos =>
      state.level mosfet.gate = false →
        state.level mosfet.drain = state.level mosfet.source
  | none => False

/-- Meaning of one card in the switch tier. Voltage sources are treated as
external drivers and are pinned by the surrounding gate contract. -/
def SwitchCardLaw (netlist : Netlist) (state : LogicState) : Card → Prop
  | .element element =>
      match element.kind with
      | .vsource => True
      | _ => False
  | .mosfet mosfet => MosfetSwitchLaw netlist state mosfet
  | .mosModel _ | .op _ => True
  | .xInstance _ | .unsupported _ | .subckt _ => False

/-- Conjunction of the switch laws for a concrete card list. -/
def SwitchCardsSatisfy (netlist : Netlist) (state : LogicState) :
    List Card → Prop
  | [] => True
  | card :: rest =>
      SwitchCardLaw netlist state card ∧
        SwitchCardsSatisfy netlist state rest

/-- A transistor deck satisfies every ideal-switch device law after
hierarchical expansion. Non-source linear elements remain outside this tier. -/
def SwitchSatisfies (netlist : Netlist) (state : LogicState) : Prop :=
  match flattenSwitch netlist with
  | .error _ => False
  | .ok flat => SwitchCardsSatisfy flat state flat.cards.toList

end LeanModels.Spice
