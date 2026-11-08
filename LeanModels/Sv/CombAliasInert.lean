import LeanModels.Sv.ProcNoQualified
import LeanModels.Sv.CombAlias2Sound
import LeanModels.Sv.Comb2Proc

/-!
# The `always_comb` alias guard is inert on the designs the comb tactics read

Since ls-sv 7c9b7ac59 ("apply alias guard to semantic families") a design family `X.sem N` is
`PDesign.instantiateGDAlias2 X.pdesign [↑N]`, the unguarded instantiation under `Design2.aliasGuard`
(`CombAlias2.lean`): an `always_comb` whose body reads a continuous copy of a variable it writes later on the
same path becomes a loud `AlwaysComb:alias-read` process. The comb tactics (`sv_structure`, `sv_interface`,
`sv_equations`, their `always_comb` forms and `sv_exhaustive`) apply theorems stated at the unguarded family
`PDesign.instantiateGD2`, so they need `X.sem N = X.pdesign.instantiateGD2 [↑N]`. This module proves that
equation at EVERY parameter point from a static check on the parametric design, decided once on the literal
`X.pdesign` (nothing is assumed):

* `PDesign.aliasInert d`: no process and no generate item of `d` is an `always_comb` (the guard touches only
  `always_comb` processes, `Design2.aliasGuard_of_noComb`), or none is a continuous assignment (then the design has
  no continuous flow and no body can read a copy, `Design2.aliasGuard_of_noAssign`);
* `PDesign.instantiateGDAlias2_of_aliasInert`: `d.aliasInert = true → d.instantiateGDAlias2 args =
  d.instantiateGD2 args`, for all `args`.

The instantiation step is `allProcs_instantiateGD2`: a property of `Process2` that every loud `unsupported`
process has and that the instantiation of every source process passing a check `f` has, holds for every process of
`d.instantiateGD2 args` (the shape of `NoQ.sem_noQ`, `ProcNoQualified.lean`, generic in the property).

Where the design is known to lower (`hl : (X.sem N).lowerComb = some d'`, what the `always_comb` forms of
`sv_interface` and `sv_equations` take), no check is needed at all: an `always_comb` the guard refuses becomes an
`unsupported` process, which does not lower (`PDesign.instantiateGDAlias2_of_lowerComb`). The one remaining case is
the `always_comb` form of `sv_structure`, which must PROVE the lowering: for a design with BOTH an `always_comb`
and a continuous assignment, whether a body reads a copy of what it writes depends on the windows at the parameter
point, which this module does not decide; the tactic refuses such a design with a message that says so.
-/

namespace LeanModels.Sv
namespace AliasInert

/-! ## The static check -/

mutual
/-- Every process of a generate item (every branch, every loop body) passes `f`. -/
def genAll (f : PProcess → Bool) : GenItem → Bool
  | .process p => f p
  | .genFor _ _ _ _ _ _ b => gensAll f b
  | .genIf _ t e => gensAll f t && gensAll f e
  | _ => true
/-- `genAll` of a generate item list. -/
def gensAll (f : PProcess → Bool) : List GenItem → Bool
  | [] => true
  | it :: rest => genAll f it && gensAll f rest
end

/-- Every process and every generate item of the parametric design passes `f`. -/
def pdAll (f : PProcess → Bool) (d : PDesign) : Bool := d.processes.all f && gensAll f d.generates

/-- The process is not an `always_comb`. -/
def procNoComb : PProcess → Bool
  | .alwaysComb _ => false
  | _ => true

/-- The process is not a continuous assignment. -/
def procNoAssign : PProcess → Bool
  | .assign .. | .assignL .. => false
  | _ => true

/-! ## Instantiation keeps a process property -/

theorem itersAll {P : Process2 → Prop} {env : IEnv} {elems : List (String × Nat)} {F : Nat} {g : String}
    {body : List GenItem}
    (hb : ∀ env ps, expandList2 env elems F body = .ok ps → ∀ p ∈ ps, P p) :
    ∀ (vs : List Int) ps, expandIters2 env elems F g vs body = .ok ps → ∀ p ∈ ps, P p
  | [], ps, h => by
      rw [expandIters2_nil] at h; cases h; exact fun p hp => (List.not_mem_nil hp).elim
  | v :: vs, ps, h => by
      rw [expandIters2_cons] at h
      simp only [Res.bind_eq_ok] at h
      obtain ⟨a, ha, b, hb', hab⟩ := h
      cases hab
      exact fun p hp => (List.mem_append.mp hp).elim (hb _ a ha p) (itersAll hb vs b hb' p)

mutual
theorem genAll_expand {P : Process2 → Prop} {f : PProcess → Bool} (hU : ∀ k m, P (.unsupported k m))
    (hI : ∀ q, f q = true → ∀ env elems, P (instProcess2 env elems q))
    {elems : List (String × Nat)} {F : Nat} : ∀ (it : GenItem) (env : IEnv) ps,
    genAll f it = true → it.expand2 env elems F = .ok ps → ∀ p ∈ ps, P p
  | .process p, env, ps, h, he => by
      rw [GenItem.expand2_process] at he; cases he
      intro q hq; rw [List.mem_singleton] at hq; subst hq; exact hI p h env elems
  | .unsupported .., _, ps, _, he => by
      rw [GenItem.expand2_unsupported] at he; cases he
      intro q hq; rw [List.mem_singleton] at hq; subst hq; exact hU _ _
  | .inst i, _, ps, _, he => by
      rw [GenItem.expand2] at he; cases he
      intro q hq; rw [List.mem_singleton] at hq; subst hq; exact hU _ _
  | .genIf c t e, env, ps, h, he => by
      simp only [genAll, Bool.and_eq_true] at h
      rw [GenItem.expand2] at he
      split at he
      · cases he
      · split at he
        · exact gensAll_expand hU hI t _ ps h.1 he
        · exact gensAll_expand hU hI e _ ps h.2 he
  | .genFor l g i b s rc body, env, ps, h, he => by
      rw [GenItem.expand2] at he
      split at he
      · simp only [Res.bind_eq_ok] at he
        obtain ⟨vs, -, he⟩ := he
        exact itersAll (fun env ps h' => gensAll_expand hU hI body env ps h h') vs ps he
      all_goals cases he
theorem gensAll_expand {P : Process2 → Prop} {f : PProcess → Bool} (hU : ∀ k m, P (.unsupported k m))
    (hI : ∀ q, f q = true → ∀ env elems, P (instProcess2 env elems q))
    {elems : List (String × Nat)} {F : Nat} : ∀ (l : List GenItem) (env : IEnv) ps,
    gensAll f l = true → expandList2 env elems F l = .ok ps → ∀ p ∈ ps, P p
  | [], _, ps, _, he => by
      rw [expandList2_nil] at he; cases he; exact fun p hp => (List.not_mem_nil hp).elim
  | it :: rest, env, ps, h, he => by
      simp only [gensAll, Bool.and_eq_true] at h
      rw [expandList2_cons] at he
      simp only [Res.bind_eq_ok] at he
      obtain ⟨a, ha, b, hb, hab⟩ := he
      cases hab
      exact fun p hp => (List.mem_append.mp hp).elim (genAll_expand hU hI it env a h.1 ha p)
        (gensAll_expand hU hI rest env b h.2 hb p)
end

/-- **A process property through the instantiation**: a property of `Process2` that every loud `unsupported`
process has (`hU`), and that the instantiation of every source process passing `f` has (`hI`), holds for every
process of `d.instantiateGD2 args` when every process and generate item of `d` passes `f`. -/
theorem allProcs_instantiateGD2 {P : Process2 → Prop} {f : PProcess → Bool} (hU : ∀ k m, P (.unsupported k m))
    (hI : ∀ q, f q = true → ∀ env elems, P (instProcess2 env elems q))
    {d : PDesign} (hd : pdAll f d = true) (args : List Int) :
    ∀ p ∈ (d.instantiateGD2 args).processes.toList, P p := by
  simp only [pdAll, Bool.and_eq_true, List.all_eq_true] at hd
  have h : ∀ p ∈ (d.instantiateD2 args).processes.toList, P p := by
    unfold PDesign.instantiateD2
    split
    · rename_i m hm
      obtain ⟨-, env, decls, elems, gens, -, -, -, h4, rfl⟩ := PDesign.instantiate2_eq_ok_iff.mp hm
      simp only [PDesign.assemble2_processes, List.mem_append, List.mem_map]
      rintro p ((⟨q, hq', rfl⟩ | hp) | ⟨_, -, rfl⟩)
      · exact hI q (hd.1 q hq') _ _
      · exact gensAll_expand hU hI _ _ _ hd.2 h4 p hp
      · exact hU _ _
    all_goals
      intro p hp
      simp only [Design2.errorDesign, List.toList_toArray, List.mem_singleton] at hp
      subst hp
      exact hU _ _
  rw [PDesign.instantiateGD2_eq_driverGuard]
  simp only [PDesign.driverGuard, Design2.driverGuard]
  split
  · exact h
  · intro p hp
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact h p hp
    · exact hU _ _

/-- Only a source `always_comb` instantiates to an `always_comb`. -/
theorem inst_noComb (q : PProcess) (hq : procNoComb q = true) (env : IEnv) (elems : List (String × Nat)) :
    ∀ b, instProcess2 env elems q ≠ .alwaysComb b := by
  intro b
  cases q <;> simp only [procNoComb, Bool.false_eq_true] at hq <;> simp only [instProcess2] <;>
    (try split) <;> simp

/-- Only a source continuous assignment instantiates to a continuous assignment. -/
theorem inst_noAssign (q : PProcess) (hq : procNoAssign q = true) (env : IEnv) (elems : List (String × Nat)) :
    ∀ t e, instProcess2 env elems q ≠ .assign t e := by
  intro t e
  cases q <;> simp only [procNoAssign, Bool.false_eq_true] at hq <;> simp only [instProcess2, combGuardProc] <;>
    (try split) <;> (try split) <;> simp

end AliasInert

open AliasInert

/-- **The static check**: no `always_comb` anywhere in the parametric design, or no continuous assignment
anywhere. Decided on the literal `X.pdesign`. -/
def PDesign.aliasInert (d : PDesign) : Bool := pdAll procNoComb d || pdAll procNoAssign d

/-- **The alias guard is inert at every parameter point** of a design that passes `PDesign.aliasInert`: the
semantic family `X.sem N` is the unguarded family the comb theorems are stated for. -/
theorem PDesign.instantiateGDAlias2_of_aliasInert {d : PDesign} (h : d.aliasInert = true) (args : List Int) :
    d.instantiateGDAlias2 args = d.instantiateGD2 args := by
  unfold PDesign.instantiateGDAlias2
  simp only [PDesign.aliasInert, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Design2.aliasGuard_of_noComb
      (allProcs_instantiateGD2 (P := fun p => ∀ b, p ≠ .alwaysComb b) (fun _ _ _ => by simp)
        inst_noComb h args)
  · exact Design2.aliasGuard_of_noAssign
      (allProcs_instantiateGD2 (P := fun p => ∀ t e, p ≠ .assign t e) (fun _ _ _ _ => by simp)
        inst_noAssign h args)

/-! ## A guarded design that lowers

Where the design in hand is known to LOWER (`hl : (X.sem N).lowerComb = some d'`, the hypothesis of the
`always_comb` forms of `sv_interface` and `sv_equations`), no static check is needed: the guard turns an
`always_comb` it refuses into an `unsupported` process, which does not lower, so a guarded design that lowers was
its own guard. This covers every design, an `always_comb` beside a continuous assignment included. -/

theorem AliasInert.lowerProcs_some {d : Design2} : ∀ (ps : List Process2) {qs : List Process2},
    d.lowerProcs ps = some qs → ∀ p ∈ ps, ∃ r, p.lowerComb d = some r
  | [], _, _, p, hp => absurd hp List.not_mem_nil
  | p :: ps, qs, h, x, hx => by
      unfold Design2.lowerProcs at h
      cases hp : p.lowerComb d with
      | none => simp [hp] at h
      | some r =>
          cases hr : d.lowerProcs ps with
          | none => simp [hp, hr] at h
          | some rs =>
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨r, hp⟩
              · exact AliasInert.lowerProcs_some ps hr x hx

/-- **A guarded design that lowers is its own guard.** -/
theorem Design2.aliasGuard_of_lowerComb {m d' : Design2} (h : m.aliasGuard.lowerComb = some d') :
    m.aliasGuard = m := by
  have hps : ∃ qs, m.aliasGuard.lowerProcs m.aliasGuard.processes.toList = some qs := by
    unfold Design2.lowerComb at h
    cases hq : m.aliasGuard.lowerProcs m.aliasGuard.processes.toList with
    | none => simp [hq] at h
    | some qs => exact ⟨qs, rfl⟩
  obtain ⟨qs, hqs⟩ := hps
  have hall := AliasInert.lowerProcs_some _ hqs
  apply Design2.aliasGuard_of_admits
  intro b hb
  have hmem : aliasGuardProc m.name m.combWd (aliasFlows m.combWd m.processes.toList) (.alwaysComb b) ∈
      m.aliasGuard.processes.toList := by
    rw [Design2.aliasGuard_processes]
    exact List.mem_map.mpr ⟨_, hb, rfl⟩
  obtain ⟨r, hr⟩ := hall _ hmem
  cases hv : b.aliasViol m.combWd (aliasFlows m.combWd m.processes.toList) [] with
  | none => rfl
  | some W =>
      rw [aliasGuardProc_of_viol hv] at hr
      simp [Process2.lowerComb] at hr

/-- … for the semantic family: `X.sem N` lowers, so it is the unguarded family. -/
theorem PDesign.instantiateGDAlias2_of_lowerComb {d : PDesign} {args : List Int} {d' : Design2}
    (h : (d.instantiateGDAlias2 args).lowerComb = some d') :
    d.instantiateGDAlias2 args = d.instantiateGD2 args :=
  Design2.aliasGuard_of_lowerComb h

/-! ## Pins -/

/--
info: 'LeanModels.Sv.PDesign.instantiateGDAlias2_of_aliasInert' depends on axioms: [propext, Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PDesign.instantiateGDAlias2_of_aliasInert

/--
info: 'LeanModels.Sv.PDesign.instantiateGDAlias2_of_lowerComb' depends on axioms: [propext, Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PDesign.instantiateGDAlias2_of_lowerComb

end LeanModels.Sv
