import LeanModels.Sv.Kernel.Core1Edge
import LeanModels.Sv.Adequacy

/-!
# The clocking discipline, and the audit of `clockExpand` (X4) (`LeanModels.Sv.Kernel`)

Experiment X4 of `svgolf/design/architecture/ARCH-NOTE.md` §7, second half. **Status: derived from
E** (a predicate on E's environment, a list of slot entries as in `Obs_E0`).

`Disciplined edge clk inputs env` (ARCH-NOTE §4.3, "the clocking discipline"; the active-edge
parameter is the lead's ruling on debt D-X1k): in every slot where `clk` makes its ACTIVE edge
(`edge`: `isPosedge` for a rising-edge clock, `isNegedge` for a falling-edge one), no other input of
`inputs` changes. Put the reset among `inputs`: then a reset never
changes in a clock-edge slot (held across the edge when it is synchronous), and an asynchronous
reset falls in a slot of its own, which is where R-EDGE (`Core1Edge.lean`) sees it fire. E-core
has no `initial` blocks, so ARCH-NOTE's third clause (no time-zero race with `initial` code) has
nothing to say yet.

A rising clock is read from the environment alone (`inputAt`: the last binding up to the slot;
`none` is the start value, read as `x`, E's all-x start).

`clockExpand_disciplined`: the harness's `clockExpand` (`Adequacy.lean`) satisfies the
rising-edge discipline (`Disciplined isPosedge`, the first instance) for every stimulus and every
input list. Each cycle becomes a clock-low slot, which
carries the stimulus entry, and a clock-high slot, which repeats it with only the clock changed.
-/

namespace LeanModels.Sv.Kernel

set_option autoImplicit false

/-- The value input `n` holds after slot `t`'s input events: its last binding up to slot `t`
(`none`: never bound, the start value). -/
def inputAt (env : List SvState) (n : String) : Nat → Option LVec
  | 0 => SvState.lookup ((env[0]?).getD []) n
  | t + 1 => (SvState.lookup ((env[t + 1]?).getD []) n).or (inputAt env n t)

/-- Its value before slot `t`'s input events. -/
def inputBefore (env : List SvState) (n : String) : Nat → Option LVec
  | 0 => none
  | t + 1 => inputAt env n t

/-- Bit 0 of an optional value, `x` when absent (`SvState.bit0`'s convention). -/
def bit0Of : Option LVec → Logic
  | some v => v.bits[0]?.getD .lx
  | none => .lx

/-- `clk` makes the edge `edge` in slot `t` (LRM 9.4.2, on bit 0). -/
def edgeAt (edge : Logic → Logic → Bool) (env : List SvState) (clk : String) (t : Nat) : Bool :=
  edge (bit0Of (inputBefore env clk t)) (bit0Of (inputAt env clk t))

/-- **The clocking discipline**: in every slot where `clk` makes its active edge `edge`, no other
input of `inputs` changes. -/
def Disciplined (edge : Logic → Logic → Bool) (clk : String) (inputs : List String)
    (env : List SvState) : Prop :=
  ∀ t, edgeAt edge env clk t = true → ∀ n ∈ inputs, n ≠ clk →
    inputAt env n t = inputBefore env n t

/-- The two slots `clockExpand` makes of stimulus entry `c`. -/
theorem clockExpand_get (clk : String) : ∀ (stim : List SvState) (c : Nat),
    (clockExpand clk stim)[2 * c]? = (stim[c]?).map (fun inp => SvState.set inp clk (LVec.ofNat 1 0)) ∧
    (clockExpand clk stim)[2 * c + 1]? =
      (stim[c]?).map (fun inp => SvState.set inp clk (LVec.ofNat 1 1))
  | [], c => by simp [clockExpand]
  | inp :: rest, 0 => by simp [clockExpand]
  | inp :: rest, c + 1 => by
      obtain ⟨ih₁, ih₂⟩ := clockExpand_get clk rest c
      have hcons : clockExpand clk (inp :: rest) =
          SvState.set inp clk (LVec.ofNat 1 0) :: SvState.set inp clk (LVec.ofNat 1 1) ::
            clockExpand clk rest := by
        simp [clockExpand]
      rw [hcons, show 2 * (c + 1) = 2 * c + 1 + 1 by omega,
        show 2 * c + 1 + 1 + 1 = 2 * c + 1 + 1 + 1 from rfl]
      simp only [List.getElem?_cons_succ, List.getElem?_cons_succ]
      exact ⟨ih₁, ih₂⟩

theorem Option.or_or_self {α : Type} (a b : Option α) : a.or (a.or b) = a.or b := by
  cases a <;> rfl

/-- **The harness's stimulus is disciplined.** `clockExpand` satisfies the clocking discipline for
every stimulus and every input list: the slot where the clock rises repeats the stimulus entry of
the slot before it, with only the clock changed. -/
theorem clockExpand_disciplined (clk : String) (inputs : List String) (stim : List SvState) :
    Disciplined isPosedge clk inputs (clockExpand clk stim) := by
  intro t hrise n _ hn
  have hdm : t = 2 * (t / 2) + t % 2 := (Nat.div_add_mod t 2).symm
  generalize t / 2 = c at hdm
  rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
  · -- a clock-low slot: the clock does not rise there
    exfalso
    rw [h0, Nat.add_zero] at hdm
    subst hdm
    obtain ⟨hlow, -⟩ := clockExpand_get clk stim c
    simp only [edgeAt] at hrise
    cases hc : stim[c]? with
    | none =>
        -- beyond the stimulus: the clock holds
        cases c with
        | zero =>
            simp [inputAt, inputBefore, hlow, hc, bit0Of] at hrise
            cases hrise
        | succ c =>
            have : inputAt (clockExpand clk stim) clk (2 * (c + 1)) =
                inputAt (clockExpand clk stim) clk (2 * c + 1) := by
              rw [show 2 * (c + 1) = 2 * c + 1 + 1 by omega]
              simp only [inputAt]
              rw [show 2 * c + 1 + 1 = 2 * (c + 1) by omega, hlow, hc]
              rfl
            rw [show inputBefore (clockExpand clk stim) clk (2 * (c + 1)) =
                inputAt (clockExpand clk stim) clk (2 * c + 1) by
                  rw [show 2 * (c + 1) = 2 * c + 1 + 1 by omega]; rfl, this, isPosedge_self] at hrise
            cases hrise
    | some inp =>
        have hnow : inputAt (clockExpand clk stim) clk (2 * c) = some (LVec.ofNat 1 0) := by
          cases c with
          | zero => simp [inputAt, hlow, hc]
          | succ c =>
              rw [show 2 * (c + 1) = 2 * c + 1 + 1 by omega]
              simp only [inputAt]
              rw [show 2 * c + 1 + 1 = 2 * (c + 1) by omega, hlow, hc]
              simp
        rw [hnow] at hrise
        cases c with
        | zero => simp [inputBefore, bit0Of] at hrise; cases hrise
        | succ c =>
            obtain ⟨-, hhigh⟩ := clockExpand_get clk stim c
            have hprev : stim[c]?.isSome := by
              cases hc' : stim[c]? with
              | none =>
                  have : stim.length ≤ c := List.getElem?_eq_none_iff.mp hc'
                  have : c + 1 < stim.length := (List.getElem?_eq_some_iff.mp hc).1
                  omega
              | some _ => rfl
            obtain ⟨inp', hc'⟩ := Option.isSome_iff_exists.mp hprev
            have hbefore : inputBefore (clockExpand clk stim) clk (2 * (c + 1)) =
                some (LVec.ofNat 1 1) := by
              rw [show 2 * (c + 1) = 2 * c + 1 + 1 by omega]
              simp only [inputBefore, inputAt]
              rw [hhigh, hc']
              simp
            rw [hbefore] at hrise
            simp [bit0Of] at hrise
            cases hrise
  · -- a clock-high slot: it repeats the entry of the slot before, the clock aside
    rw [h1] at hdm
    subst hdm
    obtain ⟨hlow, hhigh⟩ := clockExpand_get clk stim c
    simp only [inputBefore, inputAt]
    rw [hhigh]
    cases hc : stim[c]? with
    | none => rfl
    | some inp =>
        simp only [Option.map_some, Option.getD_some]
        rw [SvState.lookup_set_ne _ _ (Ne.symm hn)]
        have hlowAt : inputAt (clockExpand clk stim) n (2 * c) =
            (SvState.lookup inp n).or
              (match c with
               | 0 => none
               | c' + 1 => inputAt (clockExpand clk stim) n (2 * c' + 1)) := by
          cases c with
          | zero =>
              simp [inputAt, hlow, hc, SvState.lookup_set_ne _ _ (Ne.symm hn)]
          | succ c' =>
              rw [show 2 * (c' + 1) = 2 * c' + 1 + 1 by omega]
              simp only [inputAt]
              rw [show 2 * c' + 1 + 1 = 2 * (c' + 1) by omega, hlow, hc]
              simp [SvState.lookup_set_ne _ _ (Ne.symm hn)]
        rw [hlowAt, Option.or_or_self]

/-! ## Axioms -/

#print axioms clockExpand_get
#print axioms clockExpand_disciplined

end LeanModels.Sv.Kernel
