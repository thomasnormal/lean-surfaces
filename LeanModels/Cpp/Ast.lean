import Lean

namespace LeanModels.Cpp

inductive Raw where
  | null
  | bool (value : Bool)
  | number (value : String)
  | string (value : String)
  | array (values : List Raw)
  | object (fields : List (String × Raw))
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def Raw.field (raw : Raw) (name : String) : Option Raw :=
  match raw with
  | .object fields => (fields.find? fun entry => entry.1 == name).map Prod.snd
  | _ => none

def Raw.string? (raw : Raw) : Option String :=
  match raw with
  | .string value => some value
  | _ => none

def Raw.array? (raw : Raw) : Option (List Raw) :=
  match raw with
  | .array values => some values
  | _ => none

def Raw.text (raw : Raw) (name : String) : Option String :=
  (raw.field name).bind Raw.string?

structure Dependency where
  path : String
  sha256 : String
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Artifact where
  sourceFile : String
  sourceSha256 : String
  frontend : Raw
  dependencies : List Dependency
  ast : Raw
  deriving Repr, BEq, Inhabited, Lean.ToExpr

structure Declaration where
  id : String
  kind : String
  path : List Nat
  name : Option String
  lexicalParents : List String
  semanticParent : Option String
  previousDecl : Option String
  mangledName : Option String
  type : Option Raw
  location : Option Raw
  range : Option Raw
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def declaration? (raw : Raw) (parents : List String) (path : List Nat) : Option Declaration := do
  let kind ← raw.text "kind"
  if !kind.endsWith "Decl" then none else do
    let id ← raw.text "id"
    pure {
      id, kind, path, name := raw.text "name", lexicalParents := parents
      semanticParent := raw.text "parentDeclContextId"
      previousDecl := raw.text "previousDecl"
      mangledName := raw.text "mangledName", type := raw.field "type"
      location := raw.field "loc", range := raw.field "range"
    }

mutual
  def indexNode (raw : Raw) (parents : List String) (path : List Nat) : List Declaration :=
    match raw with
    | .object fields =>
        let current := declaration? raw parents path
        let nextParents := match current with
          | some declaration => parents ++ [declaration.id]
          | none => parents
        current.toList ++ indexFields fields nextParents path
    | _ => []

  def indexFields (fields : List (String × Raw)) (parents : List String)
      (path : List Nat) : List Declaration :=
    match fields with
    | [] => []
    | (name, raw) :: rest =>
        (if name == "inner" then indexArray raw parents path else []) ++
          indexFields rest parents path

  def indexArray (raw : Raw) (parents : List String) (parentPath : List Nat) : List Declaration :=
    match raw with
    | .array values => indexValues values parents parentPath 0
    | _ => []

  def indexValues (values : List Raw) (parents : List String)
      (parentPath : List Nat) (index : Nat) : List Declaration :=
    match values with
    | [] => []
    | raw :: rest =>
        indexNode raw parents (parentPath ++ [index]) ++
          indexValues rest parents parentPath (index + 1)
end

def Artifact.declarations (artifact : Artifact) : List Declaration :=
  indexNode artifact.ast [] []

def Artifact.declarationsById (artifact : Artifact) (id : String) : List Declaration :=
  artifact.declarations.filter fun declaration => declaration.id == id

end LeanModels.Cpp
