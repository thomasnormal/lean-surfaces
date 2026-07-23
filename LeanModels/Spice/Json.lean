import Lean
import LeanModels.Spice.Ast

/-!
# SPICE `spice-0.1` envelope ingestion

The parser follows `docs/spice-envelope-schema.md`. All entry points are pure
`Except String`; malformed JSON and schema mismatches produce descriptive
errors. An explicit `Unsupported` node is data, while an unknown `kind` is a
schema error.
-/

namespace LeanModels.Spice

open Lean (Json)

/-- Retained fields from a complete extractor envelope. -/
structure Envelope where
  schemaVersion : String
  language : String
  sourceFile : String
  sourceSha256 : String
  netlist : Netlist
deriving Repr, BEq, Inhabited

private def withCtx (ctx : String) : Except String α → Except String α
  | .ok value => .ok value
  | .error message => .error s!"{ctx}: {message}"

private def getField (json : Json) (name : String) : Except String Json :=
  withCtx s!"field {name.quote}" (json.getObjVal? name)

private def getString (json : Json) (name : String) : Except String String := do
  withCtx s!"field {name.quote}" ((← getField json name).getStr?)

private def getKind (json : Json) : Except String String :=
  getString json "kind"

private def parseStringArray (json : Json) : Except String (Array String) := do
  let values ← json.getArr?
  values.mapM fun value => value.getStr?

/-- Parse the inclusive line span carried by every card. -/
def parseSpan (json : Json) : Except String Span :=
  withCtx "span" do
    let line ← (← getField json "line").getNat?
    let endLine ← (← getField json "end_line").getNat?
    return { line, endLine }

/-- Parse and normalize an exact rational `{num, den}`. The schema promises
lowest terms; normalization also gives robust behavior on hand-written input. -/
def parseRat (json : Json) : Except String Rat :=
  withCtx "rational" do
    let num ← (← getField json "num").getInt?
    let den ← (← getField json "den").getNat?
    match den with
    | 0 => throw "denominator must be positive"
    | Nat.succ den => return Rat.normalize num (Nat.succ den) (Nat.succ_ne_zero den)

private def parseElementKind : String → Except String ElementKind
  | "R" => .ok .resistor
  | "C" => .ok .capacitor
  | "L" => .ok .inductor
  | "V" => .ok .vsource
  | "I" => .ok .isource
  | kind => .error s!"unknown element kind {kind.quote}"

private def parseElement (kind : String) (json : Json) : Except String Element :=
  withCtx kind do
    let nodes ← parseStringArray (← getField json "nodes")
    unless nodes.size == 2 do
      throw s!"field \"nodes\" must contain exactly two names, got {nodes.size}"
    let some n1 := nodes[0]? | throw "missing first node"
    let some n2 := nodes[1]? | throw "missing second node"
    return {
      kind := ← parseElementKind kind
      span := ← parseSpan (← getField json "span")
      name := ← getString json "name"
      n1, n2
      value := ← parseRat (← getField json "value") }

private def parseInstance (json : Json) : Except String Instance :=
  withCtx "X" do
    return {
      span := ← parseSpan (← getField json "span")
      name := ← getString json "name"
      subckt := ← getString json "subckt"
      connections := ← parseStringArray (← getField json "connections") }

private def parseUnsupported (json : Json) : Except String Unsupported :=
  withCtx "Unsupported" do
    return {
      span := ← parseSpan (← getField json "span")
      spiceKind := ← getString json "spice_kind"
      text := ← getString json "text" }

mutual
  /-- Parse any card valid in a top-level card list or subcircuit body. -/
  partial def parseCard (json : Json) : Except String Card := do
    let kind ← getKind json
    match kind with
    | "R" | "C" | "L" | "V" | "I" =>
        return .element (← parseElement kind json)
    | "X" => return .xInstance (← parseInstance json)
    | "Op" => return .op (← parseSpan (← getField json "span"))
    | "Unsupported" => return .unsupported (← parseUnsupported json)
    | "Subckt" => return .subckt (← parseSubckt json)
    | other =>
        throw s!"unknown card kind {other.quote} (schema mismatch; out-of-tier cards must be Unsupported)"

  /-- Parse a `.subckt` definition, including syntactically nested definitions. -/
  partial def parseSubckt (json : Json) : Except String Subckt :=
    withCtx "Subckt" do
      let kind ← getKind json
      unless kind == "Subckt" do
        throw s!"expected kind \"Subckt\", got {kind.quote}"
      return {
        span := ← parseSpan (← getField json "span")
        name := ← getString json "name"
        ports := ← parseStringArray (← getField json "ports")
        body := ← (← (← getField json "body").getArr?).mapM parseCard }
end

private def parseSubcktEntry (json : Json) : Except String SubcktEntry := do
  let kind ← getKind json
  match kind with
  | "Subckt" => return .definition (← parseSubckt json)
  | "Unsupported" => return .unsupported (← parseUnsupported json)
  | other =>
      throw s!"unknown subckts entry kind {other.quote} (want Subckt or Unsupported)"

/-- Parse the `netlist` payload. -/
def parseNetlist (json : Json) : Except String Netlist :=
  withCtx "netlist" do
    let kind ← getKind json
    unless kind == "Netlist" do
      throw s!"expected kind \"Netlist\", got {kind.quote}"
    return {
      title := ← getString json "title"
      subckts := ← (← (← getField json "subckts").getArr?).mapM parseSubcktEntry
      cards := ← (← (← getField json "cards").getArr?).mapM parseCard }

/-- Parse a complete envelope and validate its lane/version discriminators. -/
def parseEnvelope (json : Json) : Except String Envelope :=
  withCtx "envelope" do
    let schemaVersion ← getString json "schema_version"
    unless schemaVersion == "spice-0.1" do
      throw s!"unsupported schema_version {schemaVersion.quote} (want \"spice-0.1\")"
    let language ← getString json "language"
    unless language == "spice" do
      throw s!"unsupported language {language.quote} (want \"spice\")"
    return {
      schemaVersion, language
      sourceFile := ← getString json "source_file"
      sourceSha256 := ← getString json "source_sha256"
      netlist := ← parseNetlist (← getField json "netlist") }

/-- Main JSON entry point: complete envelope to its netlist payload. -/
def loadNetlist (json : Json) : Except String Netlist :=
  (fun envelope => envelope.netlist) <$> parseEnvelope json

/-- Convenience entry point from envelope text. -/
def parseEnvelopeString (text : String) : Except String Envelope :=
  Json.parse text >>= parseEnvelope

/-- Convenience entry point from envelope text to its netlist payload. -/
def loadNetlistString (text : String) : Except String Netlist :=
  (fun envelope => envelope.netlist) <$> parseEnvelopeString text

/-! ## Pure ingestion smoke guards -/

private def dividerEnvelope : String := r#"{
  "schema_version": "spice-0.1",
  "language": "spice",
  "frontend": {"name": "spice-extract", "version": "0.1"},
  "source_file": "Examples/spice/divider/divider.cir",
  "source_sha256": "placeholder",
  "netlist": {
    "kind": "Netlist", "title": "divider", "subckts": [],
    "cards": [
      {"kind":"V", "span":{"line":2,"end_line":2}, "name":"v1",
       "nodes":["in","0"], "value":{"num":5,"den":1}},
      {"kind":"R", "span":{"line":3,"end_line":3}, "name":"r1",
       "nodes":["in","out"], "value":{"num":1000,"den":1}},
      {"kind":"Op", "span":{"line":4,"end_line":4}}
    ]
  },
  "lean_blocks": []
}"#

#guard (loadNetlistString dividerEnvelope).toOption.map (·.cards.size) == some 3
#guard (loadNetlistString dividerEnvelope).toOption.map Netlist.hasUnsupported == some false

private def hierarchyEnvelope : String := r#"{
  "schema_version":"spice-0.1", "language":"spice",
  "source_file":"chain.cir", "source_sha256":"placeholder",
  "netlist":{"kind":"Netlist", "title":"chain",
    "subckts":[{"kind":"Subckt", "span":{"line":2,"end_line":4},
      "name":"attn", "ports":["a","b"],
      "body":[{"kind":"R", "span":{"line":3,"end_line":3},
        "name":"r1", "nodes":["a","b"], "value":{"num":1000,"den":1}}]}],
    "cards":[{"kind":"X", "span":{"line":5,"end_line":5}, "name":"x1",
      "subckt":"attn", "connections":["in","out"]}]},
  "lean_blocks":[]
}"#

#guard (loadNetlistString hierarchyEnvelope).toOption.map (·.subckts.size) == some 1
#guard (Json.parse "{\"num\":-3,\"den\":2}" >>= parseRat).toOption == some (-(3 / 2 : Rat))
#guard (Json.parse "{\"num\":1,\"den\":0}" >>= parseRat).toOption == none
#guard (loadNetlistString "{}").toOption == none

end LeanModels.Spice
