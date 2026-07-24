import LeanModels.Spice.Switch

/-!
# Validated MOS1 circuit representation

The extractor AST is intentionally lossless and string-oriented. This module
is the validation boundary: successful conversion resolves model references
and produces a circuit whose semantic objects have distinct Lean types.
-/

namespace LeanModels.Spice

structure NodeId where
  name : String
deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

structure SourceId where
  name : String
deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

structure TransistorId where
  name : String
deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

structure ModelId where
  name : String
deriving Repr, BEq, ReflBEq, LawfulBEq, DecidableEq, Inhabited

def node (name : String) : NodeId := ⟨name⟩
def sourceId (name : String) : SourceId := ⟨name⟩
def transistorId (name : String) : TransistorId := ⟨name⟩
def modelId (name : String) : ModelId := ⟨name⟩

instance : ToString NodeId := ⟨NodeId.name⟩
instance : ToString SourceId := ⟨SourceId.name⟩
instance : ToString TransistorId := ⟨TransistorId.name⟩
instance : ToString ModelId := ⟨ModelId.name⟩

def ground : NodeId := node "0"
def supply : NodeId := node "vdd"

/-- The exact, validated parameter set for the supported MOS Level-1 profile.
`LEVEL=1` and `IS=0` are enforced by conversion and therefore do not remain
as dynamically named fields. -/
structure Mos1Model where
  id : ModelId
  polarity : MosPolarity
  threshold : Rat
  transconductance : Rat
  channelLengthModulation : Rat
deriving Repr, BEq, Inhabited

structure Mos1VoltageSource where
  span : Span
  id : SourceId
  positive : NodeId
  negative : NodeId
  voltage : Rat
deriving Repr, BEq, Inhabited

/-- A transistor with its model reference already resolved. -/
structure Mos1Transistor where
  span : Span
  id : TransistorId
  drain : NodeId
  gate : NodeId
  source : NodeId
  bulk : NodeId
  model : Mos1Model
deriving Repr, BEq, Inhabited

inductive Mos1Device where
  | voltageSource (source : Mos1VoltageSource)
  | transistor (transistor : Mos1Transistor)
deriving Repr, BEq, Inhabited

/-- Hierarchy-free, model-resolved input to the MOS1 circuit semantics. -/
structure Mos1Circuit where
  title : String
  devices : Array Mos1Device
deriving Repr, BEq, Inhabited

def Mos1Device.nodes : Mos1Device → List NodeId
  | Mos1Device.voltageSource source => [source.positive, source.negative]
  | Mos1Device.transistor mos =>
      [mos.drain, mos.gate, mos.source, mos.bulk]

/-- All nodes mentioned by a validated circuit. Duplicates preserve the
literal device traversal and are harmless for membership. -/
def Mos1Circuit.nodes (circuit : Mos1Circuit) : List NodeId :=
  circuit.devices.toList.flatMap Mos1Device.nodes

/-- A node whose membership in a particular validated circuit is proved. -/
abbrev Mos1Circuit.Node (circuit : Mos1Circuit) :=
  { candidate : NodeId // candidate ∈ circuit.nodes }

/-- Erase a checked circuit-local node to the identifier consumed by the
physical semantics. -/
abbrev Mos1Circuit.checkedNode (circuit : Mos1Circuit) (candidate : NodeId)
    (_ : candidate ∈ circuit.nodes) : NodeId :=
  candidate

def Mos1Circuit.nodeNames (circuit : Mos1Circuit) : List String :=
  circuit.nodes.eraseDups.map NodeId.name

def Mos1Circuit.describeNodes (circuit : Mos1Circuit) : String :=
  String.intercalate ", " circuit.nodeNames

inductive Mos1ValidationError where
  | flatten (error : FlattenError)
  | unsupportedElement (name : String) (kind : ElementKind)
  | unsupportedCard (kind : String)
  | missingModel (device : TransistorId) (model : ModelId)
  | invalidModel (model : ModelId)
deriving Repr, BEq, Inhabited

def Mos1ValidationError.describe : Mos1ValidationError → String
  | .flatten error => s!"hierarchy expansion failed: {repr error}"
  | .unsupportedElement name kind =>
      s!"element `{name}` has unsupported kind `{repr kind}`"
  | .unsupportedCard kind => s!"card `{kind}` is outside the MOS1 tier"
  | .missingModel device model =>
      s!"transistor `{device}` references missing model `{model}`"
  | .invalidModel model =>
      s!"model `{model}` does not match the supported profile \
        (LEVEL=1, positive KP, LAMBDA=0, IS=0, and polarity-normalized VTO > 0)"

/-- Look up one exact raw model parameter. This function exists only on the
source side of the validation boundary. -/
def MosModel.parameter? (model : MosModel) (name : String) : Option Rat :=
  model.parameters.toList.findSome? fun parameter =>
    if parameter.name == name then some parameter.value else none

def Netlist.findMosModelCard (netlist : Netlist)
    (id : ModelId) : Option MosModel :=
  netlist.cards.toList.findSome? fun
    | .mosModel model => if model.name == id.name then some model else none
    | _ => none

/-- Validate the exact model profile represented by `Mos1Model`.

The threshold is polarity-normalized to a positive value. Positive `KP`,
zero channel-length modulation, and zero junction saturation are part of the
current proof tier rather than implicit side assumptions. -/
def MosModel.toMos1? (raw : MosModel) : Option Mos1Model := do
  let level ← raw.parameter? "level"
  if level != 1 then none else
  let vto ← raw.parameter? "vto"
  let transconductance ← raw.parameter? "kp"
  let channelLengthModulation ← raw.parameter? "lambda"
  let junctionSaturation ← raw.parameter? "is"
  if transconductance ≤ 0 then none else
  if channelLengthModulation != 0 then none else
  if junctionSaturation != 0 then none else
  let threshold :=
    match raw.polarity with
    | .nmos => vto
    | .pmos => -vto
  if threshold ≤ 0 then none else
  pure {
    id := modelId raw.name
    polarity := raw.polarity
    threshold
    transconductance
    channelLengthModulation }

private def validateModelCard (raw : MosModel) :
    Except Mos1ValidationError Unit :=
  match raw.toMos1? with
  | some _ => .ok ()
  | none => .error (.invalidModel (modelId raw.name))

private def Mosfet.toMos1 (flat : Netlist) (raw : Mosfet) :
    Except Mos1ValidationError Mos1Transistor := do
  let requested := modelId raw.model
  let modelCard ←
    match flat.findMosModelCard requested with
    | some model => pure model
    | none => throw (.missingModel (transistorId raw.name) requested)
  let model ←
    match modelCard.toMos1? with
    | some model => pure model
    | none => throw (.invalidModel requested)
  pure {
    span := raw.span
    id := transistorId raw.name
    drain := node raw.drain
    gate := node raw.gate
    source := node raw.source
    bulk := node raw.bulk
    model }

private def Element.toMos1 (raw : Element) :
    Except Mos1ValidationError Mos1VoltageSource :=
  match raw.kind with
  | .vsource =>
      .ok {
        span := raw.span
        id := sourceId raw.name
        positive := node raw.n1
        negative := node raw.n2
        voltage := raw.value }
  | kind => .error (.unsupportedElement raw.name kind)

private def validateCards (flat : Netlist) :
    List Card → Except Mos1ValidationError (List Mos1Device)
  | [] => .ok []
  | card :: rest => do
      let head ←
        match card with
        | .element raw =>
            pure (some (.voltageSource (← raw.toMos1)))
        | .mosfet raw =>
            pure (some (.transistor (← raw.toMos1 flat)))
        | .mosModel raw =>
            validateModelCard raw
            pure none
        | .op _ => pure none
        | .xInstance _ => throw (.unsupportedCard "X")
        | .subckt _ => throw (.unsupportedCard ".SUBCKT")
        | .unsupported raw => throw (.unsupportedCard raw.spiceKind)
      let tail ← validateCards flat rest
      pure <| match head with
        | some device => device :: tail
        | none => tail

/-- Flatten and validate a raw extractor netlist into the typed MOS1 IR. -/
def Netlist.toMos1 (netlist : Netlist) :
    Except Mos1ValidationError Mos1Circuit := do
  let flat ← (flattenSwitch netlist).mapError .flatten
  let devices ← validateCards flat flat.cards.toList
  pure { title := flat.title, devices := devices.toArray }

end LeanModels.Spice
