import LeanModels.Sv.CombAlias2
import LeanModels.Sv.CombGuard2Sound

/-!
# The alias guard is sound for control paths (WP4 round 6, lane B)

`CombAlias2.lean` refuses an `always_comb` body when, on some control path,
a statement reads a bit that is downstream — through at least one
continuous assignment of the flat design — of a bit the path writes at that
statement or later. This file proves what the walk `Stmt2.aliasViol`
guarantees, and nothing more.

## What is proved

* **`fanOut` is closed under the continuous flows** (`fanOut_closed`): an
  assignment that reads a bit of `A` or of `fanOut fl A` has its write
  windows in `fanOut fl A`. With it, every bit reachable from `A` through
  the flows — the inductive `Down fl A` — lies in `fanOut fl A`
  (`Down.mem_fanOut`), which is why a walk that finds no overlap with
  `fanOut` finds no overlap with any downstream bit (`aliasChk_none`).
* **Path safety** (`Stmt2.aliasViol_epaths`, `Stmt2.aliasAdmits_epaths`):
  take the control paths of a body as sequences of events — a READ of a
  window set (what one evaluation reads), a WRITE of a window set (what an
  assignment may write) — `Stmt2.epaths`: an assignment is read-then-write,
  an `if` reads its condition and continues with the taken branch (or past
  the missing `else`), a `case` reads its subject and then the patterns of
  the arms it passes (the arm taken, or all of them, then the default or
  nothing), a block concatenates. If the walk finds no violation then on
  EVERY path, no read of any event touches a bit downstream of the windows
  written by the events after it (`EPath.AF`), the read's own statement
  included. This is exactly the sentence "the block reads every copy only
  after the last write of its source" that the refusal rule states.
* **The design-level facts** the examples and the ∀-N families need:
  `Design2.aliasGuard` leaves a design without `always_comb`
  (`aliasGuard_of_noComb`) or without continuous assignments
  (`aliasGuard_of_noAssign`) unchanged, is idempotent
  (`aliasGuard_idem`), and every `always_comb` it keeps satisfies the path
  property for the design's own flows (`aliasGuard_sound`).

## What is NOT proved

The bridge from "no read is downstream of a later write" to "a simulator
that updates the copy inside the block's run reads the same values as one
that defers the update" — i.e. the schedule independence of an admitted
block. `Sem2.lean` has no intra-block propagation semantics (a blocking
write does not trigger the continuous assignments until the next
`combSettle2` pass), so there is nothing to prove it against; the statement
would need a new interpreter and a second copy of the self-read guard's
simulation proof (`CombGuard2Sound.lean`, `sim`). The justification stays
the measured mechanism (`docs/sv-oracle-disagreements.md`): Icarus 12.0
updates a copy synchronously inside the run, Xcelium 24.03 and Verilator
5.042 after the block suspends, and the two agree exactly when no read of a
copy precedes a write of its source.

The guard is also stronger than the paths it is stated on in one respect it
inherits from the self-read guard: conditions are treated as independent, so
a body whose only violating path is statically infeasible is refused too
(the conservative direction).
-/

namespace LeanModels.Sv

open CombGuard

/-! ## `touches` is "some bit in both" -/

theorem inter_width_ne {a b : BWin} :
    (a.inter b).2.2 ≠ 0 ↔ ∃ n i, a.Mem n i ∧ b.Mem n i := by
  constructor
  · intro h
    refine ⟨(a.inter b).1, (a.inter b).2.1, BWin.mem_inter.mp ?_⟩
    unfold BWin.Mem
    exact ⟨rfl, Nat.le_refl _, by omega⟩
  · rintro ⟨n, i, ha, hb⟩ h0
    have hm := BWin.mem_inter.mpr ⟨ha, hb⟩
    unfold BWin.Mem at hm
    obtain ⟨-, h1, h2⟩ := hm
    omega

theorem touches_iff {F R : List BWin} :
    touches F R = true ↔ ∃ n i, InSet R n i ∧ InSet F n i := by
  unfold touches
  rw [List.any_eq_true]
  constructor
  · rintro ⟨r, hr, h⟩
    rw [List.any_eq_true] at h
    obtain ⟨f, hf, h⟩ := h
    have h' : (r.inter f).2.2 ≠ 0 := by simpa using h
    obtain ⟨n, i, h1, h2⟩ := inter_width_ne.mp h'
    exact ⟨n, i, ⟨r, hr, h1⟩, ⟨f, hf, h2⟩⟩
  · rintro ⟨n, i, ⟨r, hr, h1⟩, ⟨f, hf, h2⟩⟩
    refine ⟨r, hr, ?_⟩
    rw [List.any_eq_true]
    exact ⟨f, hf, by simpa using inter_width_ne.mpr ⟨n, i, h1, h2⟩⟩

/-! ## The fan-out is closed under the flows -/

/-- The write windows of every assignment that reads a bit of `A ++ R` are
in `R`. -/
def FanClosed (fl : List AFlow) (A R : List BWin) : Prop :=
  ∀ x ∈ fl, touches (A ++ R) x.1 = true → ∀ k i, InSet x.2 k i → InSet R k i

theorem inSet_flatMap_snd {L : List AFlow} {x : AFlow} (hx : x ∈ L) {k : String} {i : Nat}
    (h : InSet x.2 k i) : InSet (L.flatMap (·.2)) k i := by
  obtain ⟨W, hW, hm⟩ := h
  exact ⟨W, List.mem_flatMap.mpr ⟨x, hx, hW⟩, hm⟩

/-- **The loop invariant of `fanAux`**: with fuel at least the number of
assignments still to fire, and every assignment already fired having its
write windows in `acc`, the result is closed under the flows. -/
theorem fanAux_closed (fl : List AFlow) (A : List BWin) :
    ∀ (n : Nat) (rem : List AFlow) (acc : List BWin),
      (∀ x ∈ rem, x ∈ fl) → rem.length ≤ n →
      (∀ x ∈ fl, x ∉ rem → ∀ k i, InSet x.2 k i → InSet acc k i) →
      FanClosed fl A (fanAux n rem A acc) := by
  intro n
  induction n with
  | zero =>
    intro rem acc _ hlen hacc x hx _ k i hk
    have hrem : rem = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hrem
    simp only [fanAux]
    exact hacc x hx (by simp) k i hk
  | succ n ih =>
    intro rem acc hsub hlen hacc
    simp only [fanAux]
    by_cases hemp : (hitsOf (A ++ acc) rem).isEmpty = true
    · rw [if_pos hemp]
      intro x hx htouch k i hk
      by_cases hxr : x ∈ rem
      · exfalso
        have hmem : x ∈ hitsOf (A ++ acc) rem := by
          simp only [hitsOf, List.mem_filter]
          exact ⟨hxr, htouch⟩
        have hnil := List.isEmpty_iff.mp hemp
        rw [hnil] at hmem
        exact absurd hmem List.not_mem_nil
      · exact hacc x hx hxr k i hk
    · rw [if_neg hemp]
      have hne : hitsOf (A ++ acc) rem ≠ [] := fun h => hemp (by simp [h])
      obtain ⟨x0, hx0⟩ := List.exists_mem_of_ne_nil _ hne
      simp only [hitsOf, List.mem_filter] at hx0
      apply ih
      · intro x hx
        simp only [missOf, List.mem_filter] at hx
        exact hsub x hx.1
      · have hlt : (missOf (A ++ acc) rem).length < rem.length := by
          simp only [missOf, List.length_filter_lt_length_iff_exists]
          exact ⟨x0, hx0.1, by simp [hx0.2]⟩
        omega
      · intro x hx hxn k i hk
        by_cases hxr : x ∈ rem
        · have ht : touches (A ++ acc) x.1 = true := by
            cases hb : touches (A ++ acc) x.1 with
            | true => rfl
            | false =>
                exfalso
                apply hxn
                simp only [missOf, List.mem_filter]
                exact ⟨hxr, by simp [hb]⟩
          have hmem : x ∈ hitsOf (A ++ acc) rem := by
            simp only [hitsOf, List.mem_filter]
            exact ⟨hxr, ht⟩
          exact inSet_append.mpr (Or.inr (inSet_flatMap_snd hmem hk))
        · exact inSet_append.mpr (Or.inl (hacc x hx hxr k i hk))

/-- **`fanOut` is closed under the continuous flows.** -/
theorem fanOut_closed (fl : List AFlow) (A : List BWin) : FanClosed fl A (fanOut fl A) :=
  fanAux_closed fl A fl.length fl [] (fun _ h => h) (Nat.le_refl _)
    (fun _ hx hxn => absurd hx hxn)

/-! ## Downstream bits -/

/-- Bit `(n, i)` is **downstream** of the windows `A` through the flows
`fl`: some assignment reads a bit of `A` (or a downstream bit) and writes
`(n, i)`. At least one hop. -/
inductive Down (fl : List AFlow) (A : List BWin) : String → Nat → Prop
  | base {x : AFlow} {m n : String} {j i : Nat} :
      x ∈ fl → InSet x.1 m j → InSet A m j → InSet x.2 n i → Down fl A n i
  | step {x : AFlow} {m n : String} {j i : Nat} :
      x ∈ fl → InSet x.1 m j → Down fl A m j → InSet x.2 n i → Down fl A n i

/-- **Every downstream bit is in the fan-out.** -/
theorem Down.mem_fanOut {fl : List AFlow} {A : List BWin} {n : String} {i : Nat}
    (h : Down fl A n i) : InSet (fanOut fl A) n i := by
  induction h with
  | base hx hr hA hw =>
      exact fanOut_closed fl A _ hx
        (touches_iff.mpr ⟨_, _, hr, inSet_append.mpr (Or.inl hA)⟩) _ _ hw
  | step hx hr _ hw ih =>
      exact fanOut_closed fl A _ hx
        (touches_iff.mpr ⟨_, _, hr, inSet_append.mpr (Or.inr ih)⟩) _ _ hw

/-- More sources, more downstream bits. -/
theorem Down.mono {fl : List AFlow} {A A' : List BWin}
    (hAA : ∀ n i, InSet A n i → InSet A' n i) {n : String} {i : Nat}
    (h : Down fl A n i) : Down fl A' n i := by
  induction h with
  | base hx hr hA hw => exact Down.base hx hr (hAA _ _ hA) hw
  | step hx hr _ hw ih => exact Down.step hx hr ih hw

/-- **The alias check, semantically**: when it finds nothing, no bit it
reads is downstream of the windows it was given. -/
theorem aliasChk_none {fl : List AFlow} {X R : List BWin} (h : aliasChk fl X R = none)
    {n : String} {i : Nat} (hr : InSet R n i) (hd : Down fl X n i) : False := by
  have h' : readsViol [] (fanOut fl X) R = none := h
  exact inSet_nil (readsViol_none h' hr hd.mem_fanOut)

/-! ## Control paths -/

/-- A path event: the window set one evaluation READS, or the window set an
assignment may WRITE. -/
inductive Ev where
  | rd (R : List BWin)
  | wr (W : List BWin)

abbrev EPath := List Ev

/-- The windows written along a path. -/
def EPath.writes : EPath → List BWin
  | [] => []
  | .rd _ :: es => EPath.writes es
  | .wr W :: es => W ++ EPath.writes es

theorem EPath.writes_append (p q : EPath) : (p ++ q).writes = p.writes ++ q.writes := by
  induction p with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | rd R => simpa [EPath.writes] using ih
    | wr W => simp [EPath.writes, ih, List.append_assoc]

/-- **Alias-free path**: every read event is free of bits downstream of the
windows written by the events after it on the path or by `after` (the rest of
the body past the path). -/
def EPath.AF (fl : List AFlow) : EPath → List BWin → Prop
  | [], _ => True
  | .rd R :: es, after =>
      (∀ n i, InSet R n i → ¬ Down fl (EPath.writes es ++ after) n i) ∧ EPath.AF fl es after
  | .wr _ :: es, after => EPath.AF fl es after

theorem EPath.AF_nil {fl : List AFlow} {after : List BWin} : EPath.AF fl [] after := trivial

theorem EPath.AF_rd {fl : List AFlow} {R : List BWin} {es : EPath} {after : List BWin} :
    EPath.AF fl (Ev.rd R :: es) after ↔
      ((∀ n i, InSet R n i → ¬ Down fl (EPath.writes es ++ after) n i) ∧ EPath.AF fl es after) :=
  Iff.rfl

theorem EPath.AF_wr {fl : List AFlow} {W : List BWin} {es : EPath} {after : List BWin} :
    EPath.AF fl (Ev.wr W :: es) after ↔ EPath.AF fl es after := Iff.rfl

/-- A smaller `after` is a weaker requirement. -/
theorem EPath.AF_anti {fl : List AFlow} {after after' : List BWin}
    (h : ∀ n i, InSet after n i → InSet after' n i) :
    ∀ (p : EPath), EPath.AF fl p after' → EPath.AF fl p after
  | [], _ => trivial
  | .rd R :: es, hp =>
      EPath.AF_rd.mpr ⟨fun n i hr hd => (EPath.AF_rd.mp hp).1 n i hr (hd.mono fun k j hk => by
        rcases inSet_append.mp hk with hk | hk
        · exact inSet_append.mpr (Or.inl hk)
        · exact inSet_append.mpr (Or.inr (h k j hk))),
        EPath.AF_anti h es (EPath.AF_rd.mp hp).2⟩
  | .wr _ :: es, hp => EPath.AF_anti h es (EPath.AF_wr.mp hp)

/-- Concatenation: the first path sees the writes of the second as `after`. -/
theorem EPath.AF_append {fl : List AFlow} {q : EPath} {A : List BWin} :
    ∀ (p : EPath), EPath.AF fl p (q.writes ++ A) → EPath.AF fl q A → EPath.AF fl (p ++ q) A
  | [], _, hq => hq
  | .rd R :: es, hp, hq => by
      rw [List.cons_append]
      refine EPath.AF_rd.mpr ⟨fun n i hr hd => ?_, EPath.AF_append es (EPath.AF_rd.mp hp).2 hq⟩
      apply (EPath.AF_rd.mp hp).1 n i hr
      rwa [EPath.writes_append, List.append_assoc] at hd
  | .wr W :: es, hp, hq => by
      rw [List.cons_append]
      exact EPath.AF_wr.mpr (EPath.AF_append es (EPath.AF_wr.mp hp) hq)

mutual
/-- The paths of a body, as event sequences (module docstring). -/
def Stmt2.epaths (wd : String → Option Nat) : Stmt2 → List EPath
  | .blockingAssign t e => [[Ev.rd (e.rdW wd ++ t.rdW wd), Ev.wr (t.mayW wd)]]
  | .nbaAssign t e => [[Ev.rd (e.rdW wd ++ t.rdW wd)]]
  | .ifStmt c a b => (a.epaths wd ++ Stmt2.optEpaths wd b).map fun p => Ev.rd (c.rdW wd) :: p
  | .block ss => Stmt2.listEpaths wd ss.toList
  | .caseStmt subj its d _ _ =>
      (CaseItem2.listEpaths wd (Stmt2.optEpaths wd d) its.toList).map fun p =>
        Ev.rd (subj.rdW wd) :: p
  | .unsupported _ _ => [[]]
termination_by structural s => s

/-- … of an optional statement (the missing branch has the empty path). -/
def Stmt2.optEpaths (wd : String → Option Nat) : Option Stmt2 → List EPath
  | none => [[]]
  | some s => s.epaths wd
termination_by structural o => o

/-- … of a sequence. -/
def Stmt2.listEpaths (wd : String → Option Nat) : List Stmt2 → List EPath
  | [] => [[]]
  | s :: ss => (s.epaths wd).flatMap fun p => (Stmt2.listEpaths wd ss).map fun q => p ++ q
termination_by structural ss => ss

/-- … of the arms of a `case` (`dP`: the default's paths, or the empty path
when there is none): reading arm `k`'s patterns, then the arm's body or the
rest of the arms. -/
def CaseItem2.listEpaths (wd : String → Option Nat) (dP : List EPath) :
    List CaseItem2 → List EPath
  | [] => dP
  | .mk pats body :: rest =>
      (body.epaths wd ++ CaseItem2.listEpaths wd dP rest).map fun p =>
        Ev.rd (Expr2.listRdW wd pats.toList) :: p
termination_by structural its => its
end

/-- The writes of a path are among a window set. -/
abbrev WSub (p : EPath) (W : List BWin) : Prop := ∀ n i, InSet p.writes n i → InSet W n i

mutual
/-- The writes of a path of `s` are among `s.mayW`. -/
theorem Stmt2.epaths_writes (wd : String → Option Nat) :
    ∀ (s : Stmt2) (p : EPath), p ∈ s.epaths wd → WSub p (s.mayW wd)
  | .blockingAssign t e, p, hp => by
      simp only [Stmt2.epaths, List.mem_singleton] at hp
      subst hp
      intro n i h
      simpa [EPath.writes, Stmt2.mayW] using h
  | .nbaAssign t e, p, hp => by
      simp only [Stmt2.epaths, List.mem_singleton] at hp
      subst hp
      intro n i h
      simp [EPath.writes] at h
  | .ifStmt c a b, p, hp => by
      simp only [Stmt2.epaths, List.mem_map, List.mem_append] at hp
      obtain ⟨q, hq | hq, rfl⟩ := hp
      · intro n i h
        have := Stmt2.epaths_writes wd a q hq n i h
        simp only [Stmt2.mayW]
        exact inSet_append.mpr (Or.inl this)
      · intro n i h
        have := Stmt2.optEpaths_writes wd b q hq n i h
        simp only [Stmt2.mayW]
        exact inSet_append.mpr (Or.inr this)
  | .block ss, p, hp => by
      simp only [Stmt2.epaths] at hp
      have := Stmt2.listEpaths_writes wd ss.toList p hp
      simpa only [Stmt2.mayW] using this
  | .caseStmt subj its d _ _, p, hp => by
      simp only [Stmt2.epaths, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      intro n i h
      exact CaseItem2.listEpaths_writes wd (Stmt2.optEpaths wd d) (Stmt2.optMayW wd d)
        (fun q hq => Stmt2.optEpaths_writes wd d q hq) its.toList q hq n i h
  | .unsupported _ _, p, hp => by
      simp only [Stmt2.epaths, List.mem_singleton] at hp
      subst hp
      intro n i h
      simp [EPath.writes] at h
termination_by structural s => s

theorem Stmt2.optEpaths_writes (wd : String → Option Nat) :
    ∀ (o : Option Stmt2) (p : EPath), p ∈ Stmt2.optEpaths wd o → WSub p (Stmt2.optMayW wd o)
  | none, p, hp => by
      simp only [Stmt2.optEpaths, List.mem_singleton] at hp
      subst hp
      intro n i h
      simp [EPath.writes] at h
  | some s, p, hp => Stmt2.epaths_writes wd s p hp
termination_by structural o => o

theorem Stmt2.listEpaths_writes (wd : String → Option Nat) :
    ∀ (ss : List Stmt2) (p : EPath), p ∈ Stmt2.listEpaths wd ss → WSub p (Stmt2.listMayW wd ss)
  | [], p, hp => by
      simp only [Stmt2.listEpaths, List.mem_singleton] at hp
      subst hp
      intro n i h
      simp [EPath.writes] at h
  | s :: ss, p, hp => by
      simp only [Stmt2.listEpaths, List.mem_flatMap, List.mem_map] at hp
      obtain ⟨p1, hp1, p2, hp2, rfl⟩ := hp
      intro n i h
      rw [EPath.writes_append] at h
      simp only [Stmt2.listMayW]
      rcases inSet_append.mp h with h | h
      · exact inSet_append.mpr (Or.inl (Stmt2.epaths_writes wd s p1 hp1 n i h))
      · exact inSet_append.mpr (Or.inr (Stmt2.listEpaths_writes wd ss p2 hp2 n i h))
termination_by structural ss => ss

theorem CaseItem2.listEpaths_writes (wd : String → Option Nat) (dP : List EPath) (D : List BWin)
    (hd : ∀ q ∈ dP, WSub q D) :
    ∀ (its : List CaseItem2) (p : EPath), p ∈ CaseItem2.listEpaths wd dP its →
      WSub p (CaseItem2.listMayW wd its ++ D)
  | [], p, hp => by
      simp only [CaseItem2.listEpaths] at hp
      intro n i h
      simp only [CaseItem2.listMayW, List.nil_append]
      exact hd p hp n i h
  | .mk pats body :: rest, p, hp => by
      simp only [CaseItem2.listEpaths, List.mem_map, List.mem_append] at hp
      obtain ⟨q, hq | hq, rfl⟩ := hp
      · intro n i h
        have := Stmt2.epaths_writes wd body q hq n i h
        simp only [CaseItem2.listMayW, CaseItem2.mayW, List.append_assoc]
        exact inSet_append.mpr (Or.inl this)
      · intro n i h
        have := CaseItem2.listEpaths_writes wd dP D hd rest q hq n i h
        simp only [CaseItem2.listMayW, CaseItem2.mayW, List.append_assoc]
        exact inSet_append.mpr (Or.inr this)
termination_by structural its => its
end

/-- A three-way alternation is `none` exactly when its parts are. -/
theorem orElse3_eq_none {α : Type} {x y z : Option α} :
    (x <|> y <|> z) = none ↔ x = none ∧ y = none ∧ z = none := by
  cases x <;> cases y <;> cases z <;> simp [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

mutual
/-- **Path safety.** If the walk finds no alias read in `s` given the windows
`A` written after it, then on every control path of `s` no read is downstream
of a window written at or after it (on the path, or in `A`). -/
theorem Stmt2.aliasViol_epaths (wd : String → Option Nat) (fl : List AFlow) :
    ∀ (s : Stmt2) (A : List BWin), s.aliasViol wd fl A = none →
      ∀ p ∈ s.epaths wd, EPath.AF fl p A
  | .blockingAssign t e, A, hv, p, hp => by
      simp only [Stmt2.aliasViol] at hv
      simp only [Stmt2.epaths, List.mem_singleton] at hp
      subst hp
      refine EPath.AF_rd.mpr ⟨fun n i hr hd => aliasChk_none hv hr ?_, ?_⟩
      · simpa [EPath.writes] using hd
      · exact EPath.AF_wr.mpr EPath.AF_nil
  | .nbaAssign t e, A, hv, p, hp => by
      simp only [Stmt2.aliasViol] at hv
      simp only [Stmt2.epaths, List.mem_singleton] at hp
      subst hp
      refine EPath.AF_rd.mpr ⟨fun n i hr hd => aliasChk_none hv hr ?_, EPath.AF_nil⟩
      simpa [EPath.writes] using hd
  | .ifStmt c a b, A, hv, p, hp => by
      simp only [Stmt2.aliasViol, orElse3_eq_none] at hv
      obtain ⟨hvc, hva, hvb⟩ := hv
      simp only [Stmt2.epaths, List.mem_map, List.mem_append] at hp
      obtain ⟨q, hq | hq, rfl⟩ := hp
      · refine EPath.AF_rd.mpr ⟨fun n i hr hd => aliasChk_none hvc hr (hd.mono ?_),
          Stmt2.aliasViol_epaths wd fl a A hva q hq⟩
        intro k j hk
        rcases inSet_append.mp hk with hk | hk
        · exact inSet_append.mpr (Or.inl (inSet_append.mpr
            (Or.inl (Stmt2.epaths_writes wd a q hq k j hk))))
        · exact inSet_append.mpr (Or.inr hk)
      · refine EPath.AF_rd.mpr ⟨fun n i hr hd => aliasChk_none hvc hr (hd.mono ?_),
          Stmt2.optAliasViol_epaths wd fl b A hvb q hq⟩
        intro k j hk
        rcases inSet_append.mp hk with hk | hk
        · exact inSet_append.mpr (Or.inl (inSet_append.mpr
            (Or.inr (Stmt2.optEpaths_writes wd b q hq k j hk))))
        · exact inSet_append.mpr (Or.inr hk)
  | .block ss, A, hv, p, hp => by
      simp only [Stmt2.aliasViol] at hv
      simp only [Stmt2.epaths] at hp
      exact Stmt2.listAliasViol_epaths wd fl ss.toList A hv p hp
  | .caseStmt subj its d _ _, A, hv, p, hp => by
      simp only [Stmt2.aliasViol, orElse_eq_none] at hv
      obtain ⟨hvs, hvi⟩ := hv
      simp only [Stmt2.epaths, List.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      refine EPath.AF_rd.mpr ⟨fun n i hr hd => aliasChk_none hvs hr (hd.mono ?_),
        CaseItem2.listAliasViol_epaths wd fl A (Stmt2.optMayW wd d) (Stmt2.optAliasViol wd fl A d)
          (Stmt2.optEpaths wd d)
          (fun h q hq => Stmt2.optAliasViol_epaths wd fl d A h q hq)
          (fun q hq => Stmt2.optEpaths_writes wd d q hq) its.toList hvi q hq⟩
      intro k j hk
      rcases inSet_append.mp hk with hk | hk
      · exact inSet_append.mpr (Or.inl
          (CaseItem2.listEpaths_writes wd (Stmt2.optEpaths wd d) (Stmt2.optMayW wd d)
            (fun q hq => Stmt2.optEpaths_writes wd d q hq) its.toList q hq k j hk))
      · exact inSet_append.mpr (Or.inr hk)
  | .unsupported _ _, A, hv, p, hp => by
      simp only [Stmt2.epaths, List.mem_singleton] at hp
      subst hp
      exact EPath.AF_nil
termination_by structural s => s

theorem Stmt2.optAliasViol_epaths (wd : String → Option Nat) (fl : List AFlow) :
    ∀ (o : Option Stmt2) (A : List BWin), Stmt2.optAliasViol wd fl A o = none →
      ∀ p ∈ Stmt2.optEpaths wd o, EPath.AF fl p A
  | none, A, hv, p, hp => by
      simp only [Stmt2.optEpaths, List.mem_singleton] at hp
      subst hp
      exact EPath.AF_nil
  | some s, A, hv, p, hp => Stmt2.aliasViol_epaths wd fl s A hv p hp
termination_by structural o => o

theorem Stmt2.listAliasViol_epaths (wd : String → Option Nat) (fl : List AFlow) :
    ∀ (ss : List Stmt2) (A : List BWin), Stmt2.listAliasViol wd fl A ss = none →
      ∀ p ∈ Stmt2.listEpaths wd ss, EPath.AF fl p A
  | [], A, hv, p, hp => by
      simp only [Stmt2.listEpaths, List.mem_singleton] at hp
      subst hp
      exact EPath.AF_nil
  | s :: ss, A, hv, p, hp => by
      simp only [Stmt2.listAliasViol, orElse_eq_none] at hv
      obtain ⟨hvs, hvss⟩ := hv
      simp only [Stmt2.listEpaths, List.mem_flatMap, List.mem_map] at hp
      obtain ⟨p1, hp1, p2, hp2, rfl⟩ := hp
      refine EPath.AF_append p1 ?_ ?_
      · refine EPath.AF_anti ?_ p1 (Stmt2.aliasViol_epaths wd fl s (Stmt2.listMayW wd ss ++ A) hvs p1 hp1)
        intro k j hk
        rcases inSet_append.mp hk with hk | hk
        · exact inSet_append.mpr (Or.inl (Stmt2.listEpaths_writes wd ss p2 hp2 k j hk))
        · exact inSet_append.mpr (Or.inr hk)
      · exact Stmt2.listAliasViol_epaths wd fl ss A hvss p2 hp2
termination_by structural ss => ss

theorem CaseItem2.listAliasViol_epaths (wd : String → Option Nat) (fl : List AFlow)
    (A dA : List BWin) (dV : Option BWin) (dP : List EPath)
    (hdP : dV = none → ∀ q ∈ dP, EPath.AF fl q A) (hdW : ∀ q ∈ dP, WSub q dA) :
    ∀ (its : List CaseItem2), CaseItem2.listAliasViol wd fl A dA dV its = none →
      ∀ p ∈ CaseItem2.listEpaths wd dP its, EPath.AF fl p A
  | [], hv, p, hp => by
      simp only [CaseItem2.listAliasViol] at hv
      simp only [CaseItem2.listEpaths] at hp
      exact hdP hv p hp
  | .mk pats body :: rest, hv, p, hp => by
      simp only [CaseItem2.listAliasViol, orElse3_eq_none] at hv
      obtain ⟨hvp, hvb, hvr⟩ := hv
      simp only [CaseItem2.listEpaths, List.mem_map, List.mem_append] at hp
      obtain ⟨q, hq | hq, rfl⟩ := hp
      · refine EPath.AF_rd.mpr ⟨fun n i hr hd => aliasChk_none hvp hr (hd.mono ?_),
          Stmt2.aliasViol_epaths wd fl body A hvb q hq⟩
        intro k j hk
        rcases inSet_append.mp hk with hk | hk
        · exact inSet_append.mpr (Or.inl (inSet_append.mpr (Or.inl (inSet_append.mpr
            (Or.inl (Stmt2.epaths_writes wd body q hq k j hk))))))
        · exact inSet_append.mpr (Or.inr hk)
      · refine EPath.AF_rd.mpr ⟨fun n i hr hd => aliasChk_none hvp hr (hd.mono ?_),
          CaseItem2.listAliasViol_epaths wd fl A dA dV dP hdP hdW rest hvr q hq⟩
        intro k j hk
        rcases inSet_append.mp hk with hk | hk
        · have := CaseItem2.listEpaths_writes wd dP dA hdW rest q hq k j hk
          rcases inSet_append.mp this with h | h
          · exact inSet_append.mpr (Or.inl (inSet_append.mpr (Or.inl (inSet_append.mpr
              (Or.inr h)))))
          · exact inSet_append.mpr (Or.inl (inSet_append.mpr (Or.inr h)))
        · exact inSet_append.mpr (Or.inr hk)
termination_by structural its => its
end

/-- **The guard's admission, as path safety**: a body the walk admits from an
empty written-after set has no path with a read downstream of a write at or
after it. -/
theorem Stmt2.aliasAdmits_epaths {wd : String → Option Nat} {fl : List AFlow} {body : Stmt2}
    (h : body.aliasAdmits wd fl = true) : ∀ p ∈ body.epaths wd, EPath.AF fl p [] :=
  Stmt2.aliasViol_epaths wd fl body [] (Option.isNone_iff_eq_none.mp h)

/-! ## A design without continuous assignments has nothing to refuse -/

theorem aliasChk_nil (X R : List BWin) : aliasChk [] X R = none := by
  unfold aliasChk readsViol
  simp only [fanOut, List.length_nil, fanAux]
  rw [List.findSome?_eq_none_iff]
  intro r _
  rfl


mutual
theorem Stmt2.aliasViol_nil (wd : String → Option Nat) :
    ∀ (s : Stmt2) (A : List BWin), s.aliasViol wd [] A = none
  | .blockingAssign t e, A => by simp only [Stmt2.aliasViol]; exact aliasChk_nil _ _
  | .nbaAssign t e, A => by simp only [Stmt2.aliasViol]; exact aliasChk_nil _ _
  | .ifStmt c a b, A => by
      simp only [Stmt2.aliasViol, aliasChk_nil, Stmt2.aliasViol_nil wd a A,
        Stmt2.optAliasViol_nil wd b A]
      rfl
  | .block ss, A => by
      simp only [Stmt2.aliasViol]
      exact Stmt2.listAliasViol_nil wd ss.toList A
  | .caseStmt subj its d _ _, A => by
      simp only [Stmt2.aliasViol, aliasChk_nil,
        CaseItem2.listAliasViol_nil wd A (Stmt2.optMayW wd d) (Stmt2.optAliasViol wd [] A d)
          (Stmt2.optAliasViol_nil wd d A) its.toList]
      rfl
  | .unsupported _ _, _ => by simp only [Stmt2.aliasViol]
termination_by structural s => s

theorem Stmt2.optAliasViol_nil (wd : String → Option Nat) :
    ∀ (o : Option Stmt2) (A : List BWin), Stmt2.optAliasViol wd [] A o = none
  | none, _ => rfl
  | some s, A => Stmt2.aliasViol_nil wd s A
termination_by structural o => o

theorem Stmt2.listAliasViol_nil (wd : String → Option Nat) :
    ∀ (ss : List Stmt2) (A : List BWin), Stmt2.listAliasViol wd [] A ss = none
  | [], _ => rfl
  | s :: ss, A => by
      simp only [Stmt2.listAliasViol, Stmt2.aliasViol_nil wd s, Stmt2.listAliasViol_nil wd ss A]
      rfl
termination_by structural ss => ss

theorem CaseItem2.listAliasViol_nil (wd : String → Option Nat) (A dA : List BWin)
    (dV : Option BWin) (hdV : dV = none) :
    ∀ (its : List CaseItem2), CaseItem2.listAliasViol wd [] A dA dV its = none
  | [] => hdV
  | .mk pats body :: rest => by
      simp only [CaseItem2.listAliasViol, aliasChk_nil, Stmt2.aliasViol_nil wd body A,
        CaseItem2.listAliasViol_nil wd A dA dV hdV rest]
      rfl
termination_by structural its => its
end

/-! ## The design-level facts -/

/-- The flows of a design with no continuous assignment are empty. -/
theorem aliasFlows_nil_of_noAssign {wd : String → Option Nat} {ps : List Process2}
    (h : ∀ p ∈ ps, ∀ t e, p ≠ .assign t e) : aliasFlows wd ps = [] := by
  unfold aliasFlows
  rw [List.flatMap_eq_nil_iff]
  intro p hp
  cases p with
  | assign t e => exact absurd rfl (h _ hp t e)
  | _ => rfl

/-- **A design without continuous assignments is its own guard**: no
`always_comb` can read a copy of anything. This covers the hand-built
designs of `Comb2ProcExample.lean` (every `always_comb` design the proof API
lowers), at every width. -/
theorem Design2.aliasGuard_of_noAssign {m : Design2}
    (h : ∀ p ∈ m.processes.toList, ∀ t e, p ≠ .assign t e) : m.aliasGuard = m :=
  Design2.aliasGuard_of_admits fun b _ => by
    rw [aliasFlows_nil_of_noAssign h]
    exact Stmt2.aliasViol_nil _ _ _

/-- Every `always_comb` the guard keeps satisfies the path property for the
design's own flows. -/
theorem Design2.aliasGuard_sound (m : Design2) (b : Stmt2)
    (h : Process2.alwaysComb b ∈ m.aliasGuard.processes.toList) :
    ∀ p ∈ b.epaths m.combWd, EPath.AF (aliasFlows m.combWd m.processes.toList) p [] := by
  rw [Design2.aliasGuard_processes, List.mem_map] at h
  obtain ⟨q, hq, hqb⟩ := h
  cases q with
  | alwaysComb b' =>
      simp only [aliasGuardProc] at hqb
      split at hqb
      · cases hqb
      · rename_i hnone
        cases hqb
        exact Stmt2.aliasViol_epaths _ _ _ [] hnone
  | alwaysFF c b' => simp [aliasGuardProc] at hqb
  | alwaysPlain c b' => simp [aliasGuardProc] at hqb
  | assign t e => simp [aliasGuardProc] at hqb
  | alwaysFFR c r b' => simp [aliasGuardProc] at hqb
  | unsupported k t => simp [aliasGuardProc] at hqb

theorem flatMap_map_eq {α γ : Type} (f : α → α) (g : α → List γ) (hfg : ∀ a, g (f a) = g a)
    (l : List α) : (l.map f).flatMap g = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.map_cons, List.flatMap_cons, hfg, ih]

theorem aliasGuardProc_aflow (mname : String) (wd : String → Option Nat) (fl : List AFlow)
    (p : Process2) : Process2.aflow wd (aliasGuardProc mname wd fl p) = Process2.aflow wd p := by
  cases p with
  | alwaysComb b =>
      cases hv : b.aliasViol wd fl [] with
      | none => rw [aliasGuardProc_of_admits hv]
      | some W => rw [aliasGuardProc_of_viol hv]; rfl
  | _ => rfl

theorem aliasGuardProc_idem (mname : String) (wd : String → Option Nat) (fl : List AFlow)
    (p : Process2) :
    aliasGuardProc mname wd fl (aliasGuardProc mname wd fl p) = aliasGuardProc mname wd fl p := by
  cases p with
  | alwaysComb b =>
      cases hv : b.aliasViol wd fl [] with
      | none => rw [aliasGuardProc_of_admits hv, aliasGuardProc_of_admits hv]
      | some W => rw [aliasGuardProc_of_viol hv]; rfl
  | _ => rfl

theorem Design2.eq_of_parts {x y : Design2} (h1 : x.name = y.name) (h2 : x.decls = y.decls)
    (h3 : x.processes = y.processes) : x = y := by
  cases x; cases y; simp_all

/-- **The guard is idempotent**: a second pass finds the same flows (the
guard only turns `always_comb` processes into loud ones, neither of which is
a continuous assignment) and admits what the first admitted. -/
theorem Design2.aliasGuard_idem (m : Design2) : m.aliasGuard.aliasGuard = m.aliasGuard := by
  have hfl : aliasFlows m.combWd m.aliasGuard.processes.toList =
      aliasFlows m.combWd m.processes.toList := by
    unfold aliasFlows
    rw [Design2.aliasGuard_processes]
    exact flatMap_map_eq _ _ (aliasGuardProc_aflow _ _ _) _
  refine Design2.eq_of_parts rfl rfl ?_
  have e1 : m.aliasGuard.aliasGuard.processes = m.aliasGuard.processes.map
      (aliasGuardProc m.name m.combWd (aliasFlows m.combWd m.aliasGuard.processes.toList)) := rfl
  rw [e1, hfl]
  apply Array.ext'
  rw [Array.toList_map, Design2.aliasGuard_processes, List.map_map]
  apply List.map_congr_left
  intro p _
  exact aliasGuardProc_idem _ _ _ p

/-! ## Axiom pins

Standard axioms only; the `#guard_msgs` wrappers make the build fail if any
of these drifts. -/

/--
info: 'LeanModels.Sv.fanOut_closed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fanOut_closed

/--
info: 'LeanModels.Sv.Down.mem_fanOut' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Down.mem_fanOut

/--
info: 'LeanModels.Sv.Stmt2.aliasViol_epaths' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Stmt2.aliasViol_epaths

/--
info: 'LeanModels.Sv.Stmt2.aliasAdmits_epaths' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Stmt2.aliasAdmits_epaths

/--
info: 'LeanModels.Sv.Design2.aliasGuard_of_noAssign' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Design2.aliasGuard_of_noAssign

/--
info: 'LeanModels.Sv.Design2.aliasGuard_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Design2.aliasGuard_sound

/--
info: 'LeanModels.Sv.Design2.aliasGuard_idem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Design2.aliasGuard_idem

/--
info: 'LeanModels.Sv.fanAux_closed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fanAux_closed

/--
info: 'LeanModels.Sv.aliasFlows_nil_of_noAssign' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms aliasFlows_nil_of_noAssign

end LeanModels.Sv
