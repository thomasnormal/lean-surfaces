/-!
# Relational circuit behavior and assurance obligations

The semantic root is an acausal relation.  Component and circuit models may
later expose solver-friendly views, but composition and assurance statements
are phrased against this relation.
-/

namespace LeanModels.Circuit

/-- A denotation relating one run world, boundary behavior, and internal
behavior.  It is deliberately not required to be functional. -/
abbrev Behavior (World Boundary Internal : Type) :=
  World → Boundary → Internal → Prop

/-- A selected partition of an acausal boundary into externally controlled
excitation and quantities that the model must solve. -/
structure InterfaceView (Boundary : Type) where
  Excitation : Type
  admits : Excitation → Boundary → Prop

/-- Every behavior in an allowed world satisfies a specification. -/
def SafeUnder (behavior : Behavior World Boundary Internal)
    (allowed : World → Prop) (specification : World → Boundary → Internal → Prop) : Prop :=
  ∀ world boundary internal,
    allowed world → behavior world boundary internal →
      specification world boundary internal

/-- At least one behavior exists in every allowed world. -/
def RealizableUnder (behavior : Behavior World Boundary Internal)
    (allowed : World → Prop) : Prop :=
  ∀ world, allowed world →
    ∃ boundary internal, behavior world boundary internal

/-- Every allowed excitation can be extended to a complete boundary and
internal behavior.  Receptivity is relative to an interface partition. -/
def ReceptiveUnder (behavior : Behavior World Boundary Internal)
    (view : InterfaceView Boundary)
    (allowed : World → view.Excitation → Prop) : Prop :=
  ∀ world excitation, allowed world excitation →
    ∃ boundary internal,
      view.admits excitation boundary ∧
      behavior world boundary internal

/-- The selected observation is the same in all behaviors of an allowed
world.  Internal states and unobserved boundary quantities may still differ. -/
def DeterminateUnder (behavior : Behavior World Boundary Internal)
    (allowed : World → Prop) (Observation : Type)
    (observe : World → Boundary → Internal → Observation) : Prop :=
  ∀ world, allowed world →
    ∀ boundary₁ internal₁ boundary₂ internal₂,
      behavior world boundary₁ internal₁ →
      behavior world boundary₂ internal₂ →
      observe world boundary₁ internal₁ =
        observe world boundary₂ internal₂

/-- Every admitted behavior remains inside the validity domain on which its
component envelopes are justified. -/
def StaysWithinValidityDomain
    (behavior : Behavior World Boundary Internal)
    (allowed : World → Prop)
    (domain : World → Boundary → Internal → Prop) : Prop :=
  SafeUnder behavior allowed domain

/-! ## Certified structured semantic views -/

/-- An exact structured view denotes precisely the same behaviors. -/
structure ExactView
    (denotation structured : Behavior World Boundary Internal) : Prop where
  sound : ∀ world boundary internal,
    denotation world boundary internal →
      structured world boundary internal
  complete : ∀ world boundary internal,
    structured world boundary internal →
      denotation world boundary internal

/-- An over-approximation contains every denotational behavior.  This is the
direction needed to prove universal safety properties. -/
structure OverApproxView
    (denotation structured : Behavior World Boundary Internal) : Prop where
  covers : ∀ world boundary internal,
    denotation world boundary internal →
      structured world boundary internal

/-- An under-approximation contains only genuine denotational behaviors.  This
is the direction needed to turn a computed witness into realizability. -/
structure UnderApproxView
    (denotation structured : Behavior World Boundary Internal) : Prop where
  realizes : ∀ world boundary internal,
    structured world boundary internal →
      denotation world boundary internal

theorem SafeUnder.of_overApprox
    {denotation structured : Behavior World Boundary Internal}
    (view : OverApproxView denotation structured)
    (safe : SafeUnder structured allowed specification) :
    SafeUnder denotation allowed specification := by
  intro world boundary internal hallowed hbehavior
  exact safe world boundary internal hallowed
    (view.covers world boundary internal hbehavior)

theorem RealizableUnder.of_underApprox
    {denotation structured : Behavior World Boundary Internal}
    (view : UnderApproxView denotation structured)
    (realizable : RealizableUnder structured allowed) :
    RealizableUnder denotation allowed := by
  intro world hallowed
  obtain ⟨boundary, internal, hbehavior⟩ := realizable world hallowed
  exact ⟨boundary, internal,
    view.realizes world boundary internal hbehavior⟩

end LeanModels.Circuit
