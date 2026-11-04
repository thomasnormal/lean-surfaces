import LeanModels.Circuit.Behavior

/-!
# Provenance-carrying behavioral equations

Declarative relations can accidentally place a desired conclusion inside the
behavior premise. `EquationProgram` makes the clause boundary explicit:
every clause has a classified origin, and the denotation is generated from
those clauses. Specifications remain separate predicates consumed by
`SafeUnder`.

An imported component or endpoint contract is permitted, but it cannot be
mistaken for a primitive equation: its origin is `importedContract`, and its
labels can be enumerated in an assurance report. Refinement can later replace
that clause with device, connection, initial-condition, or evolution laws.
-/

namespace LeanModels.Circuit

inductive EquationOrigin where
  | deviceLaw (component : String)
  | connectionLaw (connection : String)
  | environment (control : String)
  | initialCondition (state : String)
  | evolution (state : String)
  | importedContract (contract : String)
deriving Repr, DecidableEq, Inhabited

def EquationOrigin.importedLabel? : EquationOrigin → Option String
  | .importedContract contract => some contract
  | _ => none

def EquationOrigin.isImported (origin : EquationOrigin) : Bool :=
  origin.importedLabel?.isSome

/-- A family of equations whose identifiers are chosen by the model author.
The origin and statement are defined in one object, so a generated behavior
cannot contain an unclassified clause. -/
structure EquationProgram
    (Clause World Boundary Internal : Type) where
  origin : Clause → EquationOrigin
  equation : Clause → World → Boundary → Internal → Prop

def EquationProgram.behavior
    (program : EquationProgram Clause World Boundary Internal) :
    Behavior World Boundary Internal :=
  fun world boundary internal =>
    ∀ clause, program.equation clause world boundary internal

def EquationProgram.PhysicsOnly
    (program : EquationProgram Clause World Boundary Internal) : Prop :=
  ∀ clause, (program.origin clause).isImported = false

def EquationProgram.UsesImportedContract
    (program : EquationProgram Clause World Boundary Internal)
    (contract : String) : Prop :=
  ∃ clause, program.origin clause = .importedContract contract

/-- The report is checked against the program rather than maintained as
independent prose. -/
structure EquationManifest
    (program : EquationProgram Clause World Boundary Internal)
    (reportedImported : List String) : Prop where
  sound :
    ∀ contract, contract ∈ reportedImported →
      program.UsesImportedContract contract
  complete :
    ∀ contract, program.UsesImportedContract contract →
      contract ∈ reportedImported

theorem EquationProgram.behavior_clause
    (program : EquationProgram Clause World Boundary Internal)
    (hbehavior : program.behavior world boundary internal)
    (clause : Clause) :
    program.equation clause world boundary internal :=
  hbehavior clause

theorem EquationProgram.safe_uses_only_equations
    (program : EquationProgram Clause World Boundary Internal)
    (safe :
      SafeUnder program.behavior allowed specification)
    (hallowed : allowed world)
    (hequations :
      ∀ clause, program.equation clause world boundary internal) :
    specification world boundary internal :=
  safe world boundary internal hallowed hequations

end LeanModels.Circuit
