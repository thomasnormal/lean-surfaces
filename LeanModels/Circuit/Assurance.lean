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

/-! ## Grounding — the outer link of the non-vacuity chain

`RealizableUnder` was added so that a safety theorem could not be discharged
by an empty BEHAVIOR set.  It cannot do the same for an empty ALLOWED-WORLD
set, because it is itself guarded by `allowed world`: all three fields of
`AssuranceCase` are universally quantified over `allowed`, so an `allowed`
that no world satisfies discharges safety, realizability and domain closure
simultaneously, and `#assurance_report` prints the same lines it prints for a
real result.

Non-vacuity is therefore a CHAIN OF TWO LINKS — an inhabited world set, then
an inhabited behavior set — and `RealizableUnder` closes only the inner one.
-/

/-- At least one world is allowed.  This is the outer link: without it every
obligation in an `AssuranceCase` is satisfiable by an empty premise. -/
def GroundedUnder {World : Type} (allowed : World → Prop) : Prop :=
  ∃ world, allowed world

/-- The existential form of an assurance result: some allowed world really has
a behavior, and that behavior meets both the specification and the validity
domain.  Unlike the three universal obligations this is FALSE when `allowed`
is empty, so it is the statement that could have disagreed. -/
def ExhibitsUnder {World Boundary Internal : Type}
    (behavior : Behavior World Boundary Internal)
    (allowed : World → Prop)
    (specification domain : World → Boundary → Internal → Prop) : Prop :=
  ∃ world boundary internal,
    allowed world ∧
      behavior world boundary internal ∧
        specification world boundary internal ∧
          domain world boundary internal

/-- A grounded assurance case exhibits a witness.  One lemma converts any of
the tier's assurance cases from three universally-quantified obligations into
the existential form, given the one fact none of them currently carries. -/
theorem AssuranceCase.exhibits
    {World Boundary Internal Artifact : Type}
    {circuit : Artifact}
    {behavior : Behavior World Boundary Internal}
    {allowed : World → Prop}
    {source : SourceBinding circuit behavior allowed}
    {specification domain : World → Boundary → Internal → Prop}
    (assurance :
      AssuranceCase circuit behavior allowed source specification domain)
    (grounded : GroundedUnder allowed) :
    ExhibitsUnder behavior allowed specification domain := by
  obtain ⟨world, hworld⟩ := grounded
  obtain ⟨boundary, internal, hbehavior⟩ := assurance.realizable world hworld
  exact ⟨world, boundary, internal, hworld, hbehavior,
    assurance.safe world boundary internal hworld hbehavior,
    assurance.withinDomain world boundary internal hworld hbehavior⟩

/-- An allowed-world set pinned to a single world is grounded by that world. -/
theorem groundedUnder_eq {World : Type} (world : World) :
    GroundedUnder (fun candidate => candidate = world) :=
  ⟨world, rfl⟩

end LeanModels.Circuit
