import LeanModels.Circuit.Elaboration
import LeanModels.Circuit.Validity

/-!
# Typed circuit assurance cases

An assurance case binds one elaborated source circuit to one relational
behavior, allowed-world set, specification, and validity domain. Its core
obligations cannot be assembled from unrelated theorem statements.
-/

namespace LeanModels.Circuit

/-- An explicit, checked connection from an elaborated source artifact to the
semantic relation used by an assurance case.

`Model` is the typed result of a source adapter.  The two equalities prevent
an assurance theorem from naming a circuit while silently proving facts about
an unrelated behavior or allowed-world set.  For analysis views that consume
the complete elaborated circuit, use `SourceBinding.identity`. -/
structure SourceBinding
    {Artifact World Boundary Internal : Type}
    (circuit : Artifact)
    (behavior : Behavior World Boundary Internal)
    (allowed : World → Prop) where
  Model : Type
  model : Model
  project : Artifact → Except String Model
  projected : project circuit = .ok model
  behaviorOf : Model → Behavior World Boundary Internal
  allowedOf : Model → World → Prop
  behavior_eq : behavior = behaviorOf model
  allowed_eq : allowed = allowedOf model

/-- Bind an analysis whose semantics consumes the whole elaborated artifact.
The source artifact occurs definitionally in both the behavior and allowed
worlds, so it cannot be exchanged for another circuit. -/
def SourceBinding.identity
    (circuit : Artifact)
    (behaviorOf : Artifact → Behavior World Boundary Internal)
    (allowedOf : Artifact → World → Prop) :
    SourceBinding circuit (behaviorOf circuit) (allowedOf circuit) where
  Model := Artifact
  model := circuit
  project := .ok
  projected := rfl
  behaviorOf := behaviorOf
  allowedOf := allowedOf
  behavior_eq := rfl
  allowed_eq := rfl

/-- Bind semantics to the successful result of a checked source adapter. -/
def SourceBinding.checked
    {Model : Type}
    (project : Artifact → Except String Model)
    (circuit : Artifact) (model : Model)
    (projected : project circuit = .ok model)
    (behaviorOf : Model → Behavior World Boundary Internal)
    (allowedOf : Model → World → Prop) :
    SourceBinding circuit (behaviorOf model) (allowedOf model) where
  Model := Model
  model := model
  project := project
  projected := projected
  behaviorOf := behaviorOf
  allowedOf := allowedOf
  behavior_eq := rfl
  allowed_eq := rfl

/-- The non-negotiable core of an assurance result. All three obligations
share the same circuit, behavior, and allowed-world predicate by
construction. Determinacy, stability, coherence, numerical refinement, and
physical-validity evidence remain additional typed certificates because they
are not meaningful for every model. -/
structure AssuranceCase
    {Artifact : Type} (circuit : Artifact)
    (behavior : Behavior World Boundary Internal)
    (allowed : World → Prop)
    (source : SourceBinding circuit behavior allowed)
    (specification domain : World → Boundary → Internal → Prop) : Prop where
  safe : SafeUnder behavior allowed specification
  realizable : RealizableUnder behavior allowed
  withinDomain : StaysWithinValidityDomain behavior allowed domain

end LeanModels.Circuit
