import Lean
import LeanModels.Es.Ast

/-!
# `es-0.1` envelope ingestion (`LeanModels.Es`)

Parses the envelope of `docs/es-envelope-schema.md` from `Lean.Json` into
the types of `Ast.lean`. All parsers are pure and return
`Except String _`; malformed or unknown input yields a descriptive
`.error`, never a panic.

Entry points: `parseEnvelope : Lean.Json → Except String Envelope` and
`parseEnvelopeString : String → Except String Envelope`.

**This lane defines its own helpers rather than importing a sibling's.**
`LeanModels/Es/` is a SIBLING of `LeanModels/Python/` and `LeanModels/C/`,
never a client of either — the tiers share the project's covenant and its
instruments, not their values. The helpers below are twenty lines;
coupling two tiers to save them would trade a structural decision for a
rounding error.

Three things this ingester does that its C sibling does not, each because
the schema forced it:

* **A `parse.status` of `"error"` is a SUCCESSFUL ingestion.** It becomes
  `ParseResult.error` with `program` absent, because 4,248 of the
  language-core slice's 18,114 tests assert their source must not parse.
  Refusing them here would make a quarter of the corpus unrepresentable.
* **`language_version` IS retained and is refusable.** Unlike a frontend
  stamp, the edition is an INPUT to the AST (`docs/es-envelope-schema.md`
  §0(1)), so an envelope from another edition is a different program.
* **An array element may be `null`.** `[1, , 3]` is an elided element and
  ESTree writes it as a hole, so a node list is `List (Option Node)` and
  the hole survives ingestion rather than being quietly closed up.
-/

namespace LeanModels.Es

open Lean (Json)

/-! ## Helpers -/

/-- Prefix an error with the context it happened in. -/
def withCtx (ctx : String) (r : Except String α) : Except String α :=
  match r with
  | .ok a => .ok a
  | .error e => .error s!"{ctx}: {e}"

/-- A required field. -/
def getField (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{name}'"

/-- A required string field. -/
def getStr (j : Json) (name : String) : Except String String := do
  let v ← getField j name
  withCtx s!"field '{name}'" v.getStr?

/-- A required natural-number field. -/
def getNat (j : Json) (name : String) : Except String Nat := do
  let v ← getField j name
  withCtx s!"field '{name}'" v.getNat?

/-- A required array field. -/
def getArr (j : Json) (name : String) : Except String (Array Json) := do
  let v ← getField j name
  withCtx s!"field '{name}'" v.getArr?

/-! ## Spans -/

def parseSpan (j : Json) : Except String EsSpan := withCtx "span" do
  let s ← getField j "span"
  return {
    start := (← getNat s "start"), stop := (← getNat s "end"),
    line := (← getNat s "line"), col := (← getNat s "col"),
    endLine := (← getNat s "end_line"), endCol := (← getNat s "end_col") }

/-- The span of a `parse.error`, which carries only the three fields the
frontend can supply. -/
def parseErrorPos (j : Json) : Except String (Nat × Nat) := do
  let s ← getField j "span"
  return ((← getNat s "line"), (← getNat s "col"))

/-! ## Literals -/

def parseLit (j : Json) : Except String Lit := withCtx "literal" do
  match ← getStr j "value_type" with
  | "number" => return .number (← getStr j "value")
  | "string" => return .string (← getStr j "value")
  | "boolean" =>
    let v ← getField j "value"
    match v.getBool? with
    | .ok b => return .boolean b
    | .error e => .error s!"field 'value': {e}"
  | "null" => return .null
  | "bigint" => return .bigint (← getStr j "value")
  | "regexp" => return .regexp (← getStr j "pattern") (← getStr j "flags")
  | other => .error s!"unknown value_type '{other}'"

/-! ## Nodes

The walk is fuel-free: JSON is finite and `Json` is well-founded, but Lean
cannot see that through `Array.mapM`, so the recursion is structural over
an explicit list. -/

mutual

partial def parseNode (j : Json) : Except String Node := do
  let kind ← getStr j "kind"
  let span ← parseSpan j
  if kind == "Unsupported" then
    return .unsupported (← getStr j "node_type") (← getStr j "text") span
  if kind == "Literal" then
    return .lit (← parseLit j) (← getStr j "raw") span
  match kindOf? kind with
  | none =>
    -- The extractor has already turned anything outside the vocabulary into
    -- an `Unsupported` leaf.  One arriving here means the extractor and this
    -- ingester DISAGREE about the vocabulary, which is an error and says so
    -- rather than being quietly widened.
    .error s!"kind '{kind}' is outside the pinned vocabulary — the extractor and the ingester disagree (see harness/es_census.py --check-schema)"
  | some k =>
    -- `Json.getObj?` gives a `Std.TreeMap.Raw String Json`, whose `toList` is
    -- sorted by key.  So both property lists are canonical and do not depend
    -- on the order the extractor happened to serialize — which is what makes
    -- a `#guard` about a node's shape stable.
    let fields ← withCtx "node" j.getObj?
    let (scalars, children) ← parseFields fields.toList
    return .mk k span scalars children

/-- Split a node's JSON fields into SCALARS and CHILDREN (`Ast.lean`'s
`Node.mk`).  `kind` and `span` are the node's own header and are dropped. -/
partial def parseFields :
    List (String × Json) →
    Except String (List (String × Scalar) × List (String × List (Option Node)))
  | [] => .ok ([], [])
  | (name, v) :: rest => do
    let (ss, cs) ← parseFields rest
    if name == "kind" || name == "span" then
      return (ss, cs)
    match v with
    | .null => return ((name, .null) :: ss, cs)
    | .bool b => return ((name, .bool b) :: ss, cs)
    | .str s => return ((name, .str s) :: ss, cs)
    | .num n => return ((name, .num n.mantissa) :: ss, cs)
    | .arr a =>
      let ns ← withCtx s!"property '{name}'" (parseNodeOpts a.toList)
      return (ss, (name, ns) :: cs)
    | .obj _ =>
      match v.getObjVal? "kind" with
      | .ok _ =>
        let n ← withCtx s!"property '{name}'" (parseNode v)
        return (ss, (name, [some n]) :: cs)
      | .error _ =>
        .error s!"property '{name}': an object with no 'kind' is not a node"

partial def parseNodeOpts : List Json → Except String (List (Option Node))
  | [] => .ok []
  | x :: rest => do
    let hd ←
      match x with
      | .null => pure none                 -- an ELIDED array element
      | _ => some <$> parseNode x
    let tl ← parseNodeOpts rest
    return hd :: tl

end

/-! ## The envelope -/

def parseSourceType (s : String) : Except String SourceType :=
  match s with
  | "script" => .ok .script
  | "module" => .ok .module
  | other => .error s!"unknown source_type '{other}'"

def parseParse (j : Json) : Except String ParseResult := withCtx "parse" do
  let p ← getField j "parse"
  match ← getStr p "status" with
  | "ok" =>
    let prog ← getField j "program"
    return .ok (← withCtx "program" (parseNode prog))
  | "error" =>
    let (line, col) ← parseErrorPos p
    return .error (← getStr p "error_kind") (← getStr p "message") line col
  | other => .error s!"unknown parse.status '{other}'"

def parseEnvelope (j : Json) : Except String Envelope := do
  return {
    schemaVersion := (← getStr j "schema_version"),
    languageVersion := (← getStr j "language_version"),
    specRevision := (← getStr j "spec_revision"),
    sourceFile := (← getStr j "source_file"),
    sourceSha256 := (← getStr j "source_sha256"),
    sourceType := (← parseSourceType (← getStr j "source_type")),
    parse := (← parseParse j) }

def parseEnvelopeString (s : String) : Except String Envelope := do
  match Json.parse s with
  | .ok j => parseEnvelope j
  | .error e => .error s!"JSON: {e}"

/-! ## Projections the `#guard`s are stated through -/

/-- The program, when the source parsed. -/
def Envelope.program? (e : Envelope) : Option Node :=
  match e.parse with
  | .ok p => some p
  | .error .. => none

/-- Did the frontend ACCEPT this source? Never a claim that it is valid:
early errors are static semantics the frontend does not carry. -/
def Envelope.accepted (e : Envelope) : Bool :=
  match e.parse with
  | .ok _ => true
  | .error .. => false

/- Every node kind in the tree, with multiplicity, in traversal order.

**Structurally recursive, NOT `partial`.** A `partial` definition is an
opaque constant to the kernel, so a `#guard` stated through one cannot
reduce and would silently prove nothing.  (The JSON parsers above ARE
`partial`, which is fine: they run only at elaboration time inside
`load_es_program`, never inside a `#guard`.)  The list arms are spelled
out for the same reason — `List.flatMap` with a recursive lambda is not
something the equation compiler can see through. -/
mutual

def Node.kinds : Node → List NodeKind
  | .mk k _ _ children => k :: Node.kindsOfChildren children
  | .lit .. => []
  | .unsupported .. => []

def Node.kindsOfChildren : List (String × List (Option Node)) → List NodeKind
  | [] => []
  | (_, ns) :: rest => Node.kindsOpt ns ++ Node.kindsOfChildren rest

def Node.kindsOpt : List (Option Node) → List NodeKind
  | [] => []
  | some n :: rest => Node.kinds n ++ Node.kindsOpt rest
  | none :: rest => Node.kindsOpt rest

end

/- The `Unsupported` leaves' ESTree type names, in traversal order.
Structural, for the same reason as `Node.kinds`. -/
mutual

def Node.unsupportedTypes : Node → List String
  | .mk _ _ _ children => Node.unsupportedOfChildren children
  | .lit .. => []
  | .unsupported ty _ _ => [ty]

def Node.unsupportedOfChildren : List (String × List (Option Node)) → List String
  | [] => []
  | (_, ns) :: rest => Node.unsupportedOpt ns ++ Node.unsupportedOfChildren rest

def Node.unsupportedOpt : List (Option Node) → List String
  | [] => []
  | some n :: rest => Node.unsupportedTypes n ++ Node.unsupportedOpt rest
  | none :: rest => Node.unsupportedOpt rest

end

end LeanModels.Es
