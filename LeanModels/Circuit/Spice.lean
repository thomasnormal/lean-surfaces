import LeanModels.Circuit.Elaboration
import LeanModels.Circuit.ExactLiteral

/-!
# Direct SPICE parsing and typed circuit elaboration

This parser accepts title/comment lines, linear electrical devices, typed
MOS Level-1 models and transistors, `.subckt` definitions, `X` instances,
`.op`, and `.end`. Every other card fails loudly. Hierarchy is retained in
`SourceCircuit` and recursively flattened during typed elaboration.
-/

namespace LeanModels.Circuit.Spice

structure SourceSpan where
  line : Nat
deriving Repr, BEq, Inhabited

inductive SourceDeviceKind where
  | resistor
  | voltageSource
  | currentSource
  | capacitor
  | inductor
deriving Repr, BEq, Inhabited

structure SourceDevice where
  span : SourceSpan
  kind : SourceDeviceKind
  name : String
  positive : String
  negative : String
  value : Rat
deriving Repr, BEq, Inhabited

inductive SourceMosPolarity where
  | nmos
  | pmos
deriving Repr, BEq, DecidableEq, Inhabited

/-- A source model after resolving the supported parameter names. The
analysis-neutral artifact still validates the profile before accepting it. -/
structure SourceMosModel where
  span : SourceSpan
  name : String
  polarity : SourceMosPolarity
  level : Rat
  threshold : Rat
  transconductance : Rat
  channelLengthModulation : Rat
  junctionSaturation : Rat
deriving Repr, BEq, Inhabited

structure SourceMosfet where
  span : SourceSpan
  name : String
  drain : String
  gate : String
  source : String
  bulk : String
  model : String
deriving Repr, BEq, Inhabited

structure SourceInstance where
  span : SourceSpan
  name : String
  subcircuit : String
  connections : Array String
deriving Repr, BEq, Inhabited

structure SourceSubcircuit where
  span : SourceSpan
  name : String
  ports : Array String
  devices : Array SourceDevice
  mosfets : Array SourceMosfet
  instances : Array SourceInstance
deriving Repr, BEq, Inhabited

structure SourceCircuit where
  title : String
  devices : Array SourceDevice
  mosfets : Array SourceMosfet
  models : Array SourceMosModel
  instances : Array SourceInstance
  subcircuits : Array SourceSubcircuit
deriving Repr, BEq, Inhabited

inductive ParseError where
  | empty
  | malformed (line : Nat) (text : String)
  | unsupported (line : Nat) (text : String)
deriving Repr, BEq, Inhabited

def ParseError.describe : ParseError → String
  | .empty => "empty SPICE source"
  | .malformed line text => s!"line {line}: malformed SPICE card `{text}`"
  | .unsupported line text => s!"line {line}: unsupported SPICE card `{text}`"

private def words (text : String) : List String :=
  let text := text.replace "(" " " |>.replace ")" " "
  let flush (current : List Char) (result : List String) :=
    if current.isEmpty then result
    else String.ofList current.reverse :: result
  let rec go : List Char → List Char → List String → List String
    | [], current, result => (flush current result).reverse
    | char :: rest, current, result =>
        if char.isWhitespace then go rest [] (flush current result)
        else go rest (char :: current) result
  go text.toList [] []

def parseValue (token : String) : Option Rat :=
  ExactLiteral.parse token

private def parseDevice (line : Nat) (text : String) :
    Except ParseError SourceDevice := do
  let tokens := words text
  let name ← match tokens with
    | name :: _ => pure name.toLower
    | _ => throw (.malformed line text)
  let first ← match name.toList with
    | char :: _ => pure char.toLower
    | [] => throw (.malformed line text)
  match first, tokens with
  | 'r', [_name, positive, negative, value] =>
      let value ← match parseValue value with
        | some value => pure value
        | none => throw (.malformed line text)
      pure {
        span := ⟨line⟩, kind := .resistor, name
        positive := positive.toLower, negative := negative.toLower, value }
  | 'v', [_name, positive, negative, value] =>
      let value ← match parseValue value with
        | some value => pure value
        | none => throw (.malformed line text)
      pure {
        span := ⟨line⟩, kind := .voltageSource, name
        positive := positive.toLower, negative := negative.toLower, value }
  | 'v', [_name, positive, negative, dc, value] =>
      unless dc.toLower == "dc" do throw (.malformed line text)
      let value ← match parseValue value with
        | some value => pure value
        | none => throw (.malformed line text)
      pure {
        span := ⟨line⟩, kind := .voltageSource, name
        positive := positive.toLower, negative := negative.toLower, value }
  | 'i', [_name, positive, negative, value] =>
      let value ← match parseValue value with
        | some value => pure value
        | none => throw (.malformed line text)
      pure {
        span := ⟨line⟩, kind := .currentSource, name
        positive := positive.toLower, negative := negative.toLower, value }
  | 'i', [_name, positive, negative, dc, value] =>
      unless dc.toLower == "dc" do throw (.malformed line text)
      let value ← match parseValue value with
        | some value => pure value
        | none => throw (.malformed line text)
      pure {
        span := ⟨line⟩, kind := .currentSource, name
        positive := positive.toLower, negative := negative.toLower, value }
  | 'c', [_name, positive, negative, value] =>
      let value ← match parseValue value with
        | some value => pure value
        | none => throw (.malformed line text)
      pure {
        span := ⟨line⟩, kind := .capacitor, name
        positive := positive.toLower, negative := negative.toLower, value }
  | 'l', [_name, positive, negative, value] =>
      let value ← match parseValue value with
        | some value => pure value
        | none => throw (.malformed line text)
      pure {
        span := ⟨line⟩, kind := .inductor, name
        positive := positive.toLower, negative := negative.toLower, value }
  | _, _ => throw (.unsupported line text)

private def parseInstance (line : Nat) (text : String) :
    Except ParseError SourceInstance := do
  let tokens := words text
  match tokens.reverse with
  | subcircuit :: reversedPrefix =>
      match reversedPrefix.reverse with
      | name :: connections =>
          if connections.isEmpty then throw (.malformed line text)
          pure {
            span := ⟨line⟩
            name := name.toLower
            subcircuit := subcircuit.toLower
            connections := connections.map String.toLower |>.toArray }
      | _ => throw (.malformed line text)
  | _ => throw (.malformed line text)

private def parseMosfet (line : Nat) (text : String) :
    Except ParseError SourceMosfet := do
  match words text with
  | [name, drain, gate, source, bulk, model] =>
      pure {
        span := ⟨line⟩
        name := name.toLower
        drain := drain.toLower
        gate := gate.toLower
        source := source.toLower
        bulk := bulk.toLower
        model := model.toLower }
  | _ => throw (.malformed line text)

private def parseModelParameter (line : Nat) (text token : String) :
    Except ParseError (String × Rat) := do
  match token.splitOn "=" with
  | [name, value] =>
      let value ← match parseValue value with
        | some value => pure value
        | none => throw (.malformed line text)
      pure (name.toLower, value)
  | _ => throw (.malformed line text)

private def uniqueParameter (line : Nat) (text name : String)
    (parameters : List (String × Rat)) : Except ParseError Rat := do
  let found := parameters.filter (·.1 == name)
  match found with
  | [entry] => pure entry.2
  | _ => throw (.malformed line text)

private def parseModel (line : Nat) (text : String) :
    Except ParseError SourceMosModel := do
  match words text with
  | _directive :: name :: polarityToken :: parameterTokens =>
      let polarity ← match polarityToken.toLower with
        | "nmos" => pure SourceMosPolarity.nmos
        | "pmos" => pure SourceMosPolarity.pmos
        | _ => throw (.unsupported line text)
      let mut parameters := []
      for token in parameterTokens do
        parameters := (← parseModelParameter line text token) :: parameters
      let known := ["level", "vto", "kp", "lambda", "is"]
      unless parameters.all (known.contains ·.1) do
        throw (.unsupported line text)
      pure {
        span := ⟨line⟩
        name := name.toLower
        polarity
        level := ← uniqueParameter line text "level" parameters
        threshold := ← uniqueParameter line text "vto" parameters
        transconductance := ← uniqueParameter line text "kp" parameters
        channelLengthModulation := ← uniqueParameter line text "lambda" parameters
        junctionSaturation := ← uniqueParameter line text "is" parameters }
  | _ => throw (.malformed line text)

def parse (source : String) : Except ParseError SourceCircuit := do
  let lines := source.splitOn "\n"
  let title ← match lines with
    | [] => throw .empty
    | first :: _ => pure first.trimAscii.toString
  if title.isEmpty then throw .empty
  let mut devices := #[]
  let mut mosfets := #[]
  let mut models := #[]
  let mut instances := #[]
  let mut subcircuits := #[]
  let mut activeName : Option String := none
  let mut activeLine := 0
  let mut activePorts : Array String := #[]
  let mut activeDevices : Array SourceDevice := #[]
  let mut activeMosfets : Array SourceMosfet := #[]
  let mut activeInstances : Array SourceInstance := #[]
  for (raw, index) in lines.drop 1 |>.zipIdx do
    let text := raw.trimAscii.toString
    let line := index + 2
    if text.isEmpty || text.startsWith "*" then continue
    if text.toLower.startsWith ".subckt" then
      if activeName.isSome then throw (.malformed line text)
      match words text with
      | _directive :: name :: ports =>
          if ports.isEmpty then throw (.malformed line text)
          activeName := some name.toLower
          activeLine := line
          activePorts := ports.map String.toLower |>.toArray
          activeDevices := #[]
          activeMosfets := #[]
          activeInstances := #[]
      | _ => throw (.malformed line text)
      continue
    if text.toLower.startsWith ".ends" then
      let name ← match activeName with
        | some name => pure name
        | none => throw (.malformed line text)
      match words text with
      | [_directive] => pure ()
      | [_directive, closingName] =>
          unless closingName.toLower == name do
            throw (.malformed line text)
      | _ => throw (.malformed line text)
      subcircuits := subcircuits.push {
        span := ⟨activeLine⟩
        name
        ports := activePorts
        devices := activeDevices
        mosfets := activeMosfets
        instances := activeInstances }
      activeName := none
      activePorts := #[]
      activeDevices := #[]
      activeMosfets := #[]
      activeInstances := #[]
      continue
    if text.toLower == ".end" then
      if activeName.isSome then throw (.malformed line text)
      break
    if text.toLower == ".op" then continue
    if text.toLower.startsWith ".model" then
      if activeName.isSome then
        throw (.unsupported line text)
      models := models.push (← parseModel line text)
      continue
    let first ← match text.toList with
      | char :: _ => pure char.toLower
      | [] => throw (.malformed line text)
    if first == 'x' then
      let inst ← parseInstance line text
      if activeName.isSome then
        activeInstances := activeInstances.push inst
      else
        instances := instances.push inst
    else if first == 'm' then
      let mosfet ← parseMosfet line text
      if activeName.isSome then
        activeMosfets := activeMosfets.push mosfet
      else
        mosfets := mosfets.push mosfet
    else
      let device ← parseDevice line text
      if activeName.isSome then
        activeDevices := activeDevices.push device
      else
        devices := devices.push device
  if activeName.isSome then
    throw (.malformed activeLine "unterminated .subckt")
  pure { title, devices, mosfets, models, instances, subcircuits }

inductive ElaborationError where
  | missingGround
  | duplicateDevice (name : String)
  | duplicateSubcircuit (name : String)
  | missingSubcircuit (name : String)
  | recursiveSubcircuit (name : String)
  | portArity (name : String) (expected actual : Nat)
  | invalidResistance (name : String)
  | invalidCapacitance (name : String)
  | invalidInductance (name : String)
  | duplicateModel (name : String)
  | missingModel (device model : String)
  | invalidMos1Model (name : String)
deriving Repr, BEq, Inhabited

def ElaborationError.describe : ElaborationError → String
  | .missingGround => "the circuit has no ground node `0`"
  | .duplicateDevice name => s!"duplicate device name `{name}`"
  | .duplicateSubcircuit name => s!"duplicate subcircuit name `{name}`"
  | .missingSubcircuit name => s!"missing subcircuit `{name}`"
  | .recursiveSubcircuit name => s!"recursive subcircuit `{name}`"
  | .portArity name expected actual =>
      s!"instance `{name}` has {actual} connections; expected {expected}"
  | .invalidResistance name => s!"resistor `{name}` must be positive"
  | .invalidCapacitance name => s!"capacitor `{name}` must be positive"
  | .invalidInductance name => s!"inductor `{name}` must be positive"
  | .duplicateModel name => s!"duplicate MOS model `{name}`"
  | .missingModel device model =>
      s!"MOS transistor `{device}` references missing model `{model}`"
  | .invalidMos1Model name =>
      s!"MOS model `{name}` is outside the supported typed profile"

private def appendUnique (names : Array String) (name : String) : Array String :=
  if names.contains name then names else names.push name

private def sourceNodes (devices : Array SourceDevice)
    (mosfets : Array SourceMosfet) : Array String :=
  let linear := devices.foldl (fun names device =>
    appendUnique (appendUnique names device.positive) device.negative) #[]
  mosfets.foldl (fun names mosfet =>
    appendUnique
      (appendUnique
        (appendUnique (appendUnique names mosfet.drain) mosfet.gate)
        mosfet.source)
      mosfet.bulk) linear

private def duplicate? : List String → Option String
  | [] => none
  | name :: rest =>
      if rest.contains name then some name else duplicate? rest

private def SourceCircuit.subcircuit?
    (source : SourceCircuit) (name : String) : Option SourceSubcircuit :=
  source.subcircuits.find? fun subcircuit => subcircuit.name == name

private def qualify (path name : String) : String :=
  if path.isEmpty then name else path ++ "." ++ name

private def resolveNode (mapping : Array (String × String))
    (path node : String) : String :=
  if node == "0" then "0"
  else
    match mapping.find? fun entry => entry.1 == node with
    | some entry => entry.2
    | none => qualify path node

private def mapDevice (mapping : Array (String × String))
    (path : String) (device : SourceDevice) : SourceDevice :=
  { device with
    name := qualify path device.name
    positive := resolveNode mapping path device.positive
    negative := resolveNode mapping path device.negative }

private def mapMosfet (mapping : Array (String × String))
    (path : String) (mosfet : SourceMosfet) : SourceMosfet :=
  { mosfet with
    name := qualify path mosfet.name
    drain := resolveNode mapping path mosfet.drain
    gate := resolveNode mapping path mosfet.gate
    source := resolveNode mapping path mosfet.source
    bulk := resolveNode mapping path mosfet.bulk }

structure FlattenedSource where
  devices : Array SourceDevice
  mosfets : Array SourceMosfet
deriving Repr, BEq, Inhabited

def FlattenedSource.append (left right : FlattenedSource) : FlattenedSource :=
  { devices := left.devices ++ right.devices
    mosfets := left.mosfets ++ right.mosfets }

private partial def expandInstance (source : SourceCircuit)
    (outerMapping : Array (String × String)) (outerPrefix : String)
    (stack : List String) (inst : SourceInstance) :
    Except ElaborationError FlattenedSource := do
  if stack.contains inst.subcircuit then
    throw (.recursiveSubcircuit inst.subcircuit)
  let subcircuit ← match source.subcircuit? inst.subcircuit with
    | some subcircuit => pure subcircuit
    | none => throw (.missingSubcircuit inst.subcircuit)
  if subcircuit.ports.size != inst.connections.size then
    throw (.portArity inst.name subcircuit.ports.size
      inst.connections.size)
  let path := qualify outerPrefix inst.name
  let connections := inst.connections.map fun node =>
    resolveNode outerMapping outerPrefix node
  let mapping := subcircuit.ports.zip connections
  let mut result : FlattenedSource := {
    devices := subcircuit.devices.map (mapDevice mapping path)
    mosfets := subcircuit.mosfets.map (mapMosfet mapping path) }
  for nested in subcircuit.instances do
    result := result.append
      (← expandInstance source mapping path
        (inst.subcircuit :: stack) nested)
  pure result

def flattenSource (source : SourceCircuit) :
    Except ElaborationError FlattenedSource := do
  if let some name := duplicate? (source.subcircuits.map (·.name)).toList then
    throw (.duplicateSubcircuit name)
  let mut result : FlattenedSource :=
    { devices := source.devices, mosfets := source.mosfets }
  for inst in source.instances do
    result := result.append (← expandInstance source #[] "" [] inst)
  pure result

def elaborate (source : SourceCircuit) :
    Except ElaborationError LeanModels.Circuit.ElaboratedCircuit := do
  let flat ← flattenSource source
  let nodeNames := sourceNodes flat.devices flat.mosfets
  let groundIndex ← match nodeNames.findIdx? (· == "0") with
    | some index => pure index
    | none => throw .missingGround
  let deviceNames := flat.devices.map (·.name) ++ flat.mosfets.map (·.name)
  if let some name := duplicate? deviceNames.toList then
    throw (.duplicateDevice name)
  let modelNames := source.models.map (·.name)
  if let some name := duplicate? modelNames.toList then
    throw (.duplicateModel name)
  let mut models := #[]
  for (model, index) in source.models.zipIdx do
    unless model.level == 1 &&
        model.transconductance > 0 &&
        model.channelLengthModulation == 0 &&
        model.junctionSaturation == 0 do
      throw (.invalidMos1Model model.name)
    let threshold := match model.polarity with
      | .nmos => model.threshold
      | .pmos => -model.threshold
    unless threshold > 0 do
      throw (.invalidMos1Model model.name)
    let polarity := match model.polarity with
      | .nmos => LeanModels.Circuit.MosPolarity.nmos
      | .pmos => LeanModels.Circuit.MosPolarity.pmos
    models := models.push (.mos1 {
      id := ⟨index⟩
      polarity
      threshold
      transconductance := model.transconductance
      channelLengthModulation := model.channelLengthModulation
      junctionSaturation := model.junctionSaturation })
  let mut devices := #[]
  for (device, index) in flat.devices.zipIdx do
    let positive := ⟨(nodeNames.findIdx? (· == device.positive)).getD nodeNames.size⟩
    let negative := ⟨(nodeNames.findIdx? (· == device.negative)).getD nodeNames.size⟩
    let id := LeanModels.Circuit.DeviceId.mk index
    let typed ← match device.kind with
      | .resistor =>
          if device.value ≤ 0 then throw (.invalidResistance device.name)
          pure (LeanModels.Circuit.ElaboratedDevice.resistor
            id positive negative device.value)
      | .voltageSource =>
          pure (LeanModels.Circuit.ElaboratedDevice.voltageSource
            id positive negative device.value)
      | .currentSource =>
          pure (LeanModels.Circuit.ElaboratedDevice.currentSource
            id positive negative device.value)
      | .capacitor =>
          if device.value ≤ 0 then throw (.invalidCapacitance device.name)
          pure (LeanModels.Circuit.ElaboratedDevice.capacitor
            id positive negative device.value)
      | .inductor =>
          if device.value ≤ 0 then throw (.invalidInductance device.name)
          pure (LeanModels.Circuit.ElaboratedDevice.inductor
            id positive negative device.value)
    devices := devices.push typed
  for (mosfet, offset) in flat.mosfets.zipIdx do
    let modelIndex ← match modelNames.findIdx? (· == mosfet.model) with
      | some index => pure index
      | none => throw (.missingModel mosfet.name mosfet.model)
    let nodeId (name : String) :=
      LeanModels.Circuit.NodeId.mk
        ((nodeNames.findIdx? (· == name)).getD nodeNames.size)
    devices := devices.push (.mosfet
      ⟨flat.devices.size + offset⟩
      (nodeId mosfet.drain) (nodeId mosfet.gate)
      (nodeId mosfet.source) (nodeId mosfet.bulk)
      ⟨modelIndex⟩)
  pure {
    title := source.title
    nodeNames
    deviceNames
    modelNames
    ground := ⟨groundIndex⟩
    devices
    models }

def elaborateDC (source : SourceCircuit) :
    Except String LeanModels.Circuit.DCCircuit := do
  let circuit ← (elaborate source).mapError ElaborationError.describe
  circuit.toDCCircuit.mapError fun error => s!"exact DC projection failed: {repr error}"

def parseAndElaborate (source : String) :
    Except String LeanModels.Circuit.ElaboratedCircuit := do
  let parsed ← (parse source).mapError ParseError.describe
  (elaborate parsed).mapError ElaborationError.describe

def parseAndElaborateDC (source : String) :
    Except String LeanModels.Circuit.DCCircuit := do
  let parsed ← (parse source).mapError ParseError.describe
  elaborateDC parsed

#guard parseValue "1k" == some 1000
#guard parseValue "1.5" == some (3 / 2)
#guard parseValue "470u" == some (47 / 100000)
#guard parseValue "1e3" == some 1000
#guard parseValue "2.5e-3" == some (1 / 400)

end LeanModels.Circuit.Spice
