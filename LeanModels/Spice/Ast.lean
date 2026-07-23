/-!
# SPICE M0 abstract syntax

The value-bearing types are parameterized, with `Rat` as the DC default.
This keeps the M0 API concise while allowing a later AC lane to instantiate
the same syntax and assignments with Gaussian rationals.
-/

namespace LeanModels.Spice

/-- Inclusive, one-based source line span for one logical SPICE card. -/
structure Span where
  line : Nat
  endLine : Nat
deriving Repr, BEq, DecidableEq, Inhabited

/-- The five element kinds represented in M0. -/
inductive ElementKind where
  | resistor
  | capacitor
  | inductor
  | vsource
  | isource
deriving Repr, BEq, DecidableEq, Inhabited

/-- A supported two-terminal element. Node order preserves SPICE orientation. -/
structure Element (Value : Type := Rat) where
  kind : ElementKind
  span : Span
  name : String
  n1 : String
  n2 : String
  value : Value
deriving Repr, BEq, Inhabited

/-- Channel polarity for the ideal-switch MOS tier. -/
inductive MosPolarity where
  | nmos
  | pmos
deriving Repr, BEq, DecidableEq, Inhabited

/-- A four-terminal MOS transistor (`M` card).

The AST retains the model name instead of assigning device behavior here.
The linear-DC semantics rejects this card, while the switch semantics resolves
the referenced `.model` declaration. -/
structure Mosfet where
  span : Span
  name : String
  drain : String
  gate : String
  source : String
  bulk : String
  model : String
deriving Repr, BEq, Inhabited

/-- The polarity-bearing portion of a `.model ... nmos|pmos` declaration.
Analog model parameters remain in the source deck for ngspice; the formal
switch tier deliberately depends only on channel polarity. -/
structure MosModel where
  span : Span
  name : String
  polarity : MosPolarity
deriving Repr, BEq, Inhabited

/-- A subcircuit instance (`X` card). -/
structure Instance where
  span : Span
  name : String
  subckt : String
  connections : Array String
deriving Repr, BEq, Inhabited

/-- An out-of-tier card preserved by the extractor. -/
structure Unsupported where
  span : Span
  spiceKind : String
  text : String
deriving Repr, BEq, Inhabited

mutual
  /-- A card in a top-level netlist or subcircuit body. Nested subcircuits are
  represented faithfully here and rejected later by M0 flattening. -/
  inductive Card (Value : Type := Rat) where
    | element (element : Element Value)
    | mosfet (mosfet : Mosfet)
    | mosModel (model : MosModel)
    | xInstance (inst : Instance)
    | op (span : Span)
    | unsupported (card : Unsupported)
    | subckt (subckt : Subckt Value)
  deriving Repr, BEq, Inhabited

  /-- A `.subckt` definition. `ports` and `body` preserve source order. -/
  structure Subckt (Value : Type := Rat) where
    span : Span
    name : String
    ports : Array String
    body : Array (Card Value)
  deriving Repr, BEq, Inhabited
end

/-- Top-level `.subckt` list entry. Malformed definitions are retained as one
unsupported entry rather than mixed into the ordinary top-level cards. -/
inductive SubcktEntry (Value : Type := Rat) where
  | definition (subckt : Subckt Value)
  | unsupported (card : Unsupported)
deriving Repr, BEq, Inhabited

/-- Extractor-level netlist, including hierarchy and loud unsupported cards. -/
structure Netlist (Value : Type := Rat) where
  title : String
  subckts : Array (SubcktEntry Value)
  cards : Array (Card Value)
deriving Repr, BEq, Inhabited

/-- Hierarchy-free input to DC semantics. Its type excludes instances,
analysis cards, nested definitions, and unsupported cards by construction. -/
structure FlatNetlist (Value : Type := Rat) where
  elements : Array (Element Value)
deriving Repr, BEq, Inhabited

/-- Voltages and named branch currents. Total functions intentionally leave
off-support values unconstrained; uniqueness is stated only on netlist support. -/
structure Assignment (Value : Type := Rat) where
  volt : String → Value
  cur : String → Value

/-- Whether an unsupported card occurs anywhere in an extractor netlist. -/
def Netlist.hasUnsupported (netlist : Netlist Value) : Bool :=
  netlist.subckts.any subcktEntryHas || netlist.cards.any cardHas
where
  subcktEntryHas : SubcktEntry Value → Bool
    | .definition subckt => subckt.body.any cardHas
    | .unsupported _ => true
  cardHas : Card Value → Bool
    | .element _ | .mosfet _ | .mosModel _ | .xInstance _ | .op _ => false
    | .unsupported _ => true
    -- A nested definition is a distinct flattening error before its body is reached.
    | .subckt _ => false

/-! ## AST smoke guards -/

private def dividerAst : Netlist :=
  { title := "divider"
    subckts := #[]
    cards := #[
      .element { kind := .vsource, span := ⟨12, 12⟩, name := "v1",
                 n1 := "in", n2 := "0", value := 5 },
      .element { kind := .resistor, span := ⟨13, 13⟩, name := "r1",
                 n1 := "in", n2 := "out", value := 1000 },
      .op ⟨14, 14⟩] }

#guard dividerAst.cards.size == 3
#guard dividerAst.hasUnsupported == false

private def badAst : Netlist :=
  { title := "bad", subckts := #[],
    cards := #[.unsupported ⟨⟨1, 1⟩, ".tran", ".tran 1u 1m"⟩] }

#guard badAst.hasUnsupported

end LeanModels.Spice
