import LeanModels.Spice.Ast

/-!
# Ideal-switch MOS semantics

This tier gives transistor-level CMOS decks a small, explicit digital
abstraction. An NMOS conducts exactly when its gate is high; a PMOS conducts
exactly when its gate is low; a conducting device equates its drain and source
logic levels. Off devices impose no relation.

This is not a model of nonlinear MOS currents. The same extracted deck is
checked with ngspice to validate that its analog operating points lie inside
the chosen logic-level bands.
-/

namespace LeanModels.Spice

/-- Boolean logic levels assigned to every named circuit node. -/
structure LogicState where
  level : String → Bool

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

/-- A flat transistor deck satisfies every ideal-switch device law.
Hierarchy and non-source linear elements are intentionally rejected in this
first low-level gate tier. -/
def SwitchSatisfies (netlist : Netlist) (state : LogicState) : Prop :=
  netlist.subckts = #[] ∧
    SwitchCardsSatisfy netlist state netlist.cards.toList

/-- Supply and input assumptions for a two-input CMOS gate. -/
def DrivesTwo (state : LogicState) (leftName rightName : String)
    (left right : Bool) : Prop :=
  state.level "0" = false ∧
  state.level "vdd" = true ∧
  state.level leftName = left ∧
  state.level rightName = right

/-- An exact Boolean contract for a transistor-level two-input gate.

The first conjunct is soundness: every switch-model state has the advertised
output. The second is realizability: the switch constraints are consistent
for every input vector. -/
def BinaryGateContract (netlist : Netlist)
    (leftName rightName outputName : String)
    (operation : Bool → Bool → Bool) : Prop :=
  ∀ left right,
    (∀ state, SwitchSatisfies netlist state →
      DrivesTwo state leftName rightName left right →
      state.level outputName = operation left right) ∧
    ∃ state, SwitchSatisfies netlist state ∧
      DrivesTwo state leftName rightName left right

end LeanModels.Spice
