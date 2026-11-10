import LeanModels.Sv.Kernel.Obs_E0

/-!
# Fuelled E executors

`exec` and `exec1` are deliberately small X-layer instruments: the E
semantics is the inductive `Steps`/`Steps1` closure and has no fuel.  These
drivers put a finite budget around that closure for differential harnesses.
Each returned row keeps both the opened and closed configuration, so the
soundness lemmas expose the exact E slot judgment rather than treating a
timeout as a refusal or a value.
-/

namespace LeanModels.Sv.Kernel

set_option autoImplicit false

abbrev E0Row := Config × Config

def execE0 (E : Elab) (ch : Choice) (fuel : Nat) (c : Config) : Res Config :=
  match exec E ch fuel c with
  | .closed c' => .ok c'
  | .outOfBudget _ => .timeout
  | .refused r => .unsupported r.observable.2

def runE0Tail (E : Elab) (ch : Choice) (fuel : Nat) :
    Config → List SvState → Res (List E0Row)
  | c, [] => .ok []
  | c, entry :: rest =>
      let start := Config.nextSlot E c entry
      match execE0 E ch fuel start with
      | .ok closed =>
          match runE0Tail E ch fuel closed rest with
          | .ok rows => .ok ((start, closed) :: rows)
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

/-- Run one finite input batch through E-core-0's test executor. -/
def runE0 (E : Elab) (ch : Choice) (fuel : Nat) (env : List SvState) :
    Res (List E0Row) :=
  match env with
  | [] => .ok []
  | entry :: rest =>
      let start := Config.start E entry
      match execE0 E ch fuel start with
      | .ok closed =>
          match runE0Tail E ch fuel closed rest with
          | .ok rows => .ok ((start, closed) :: rows)
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

theorem execE0_sound {E : Elab} {ch : Choice} {fuel : Nat} {c c' : Config}
    (h : execE0 E ch fuel c = .ok c') : SlotCloses E ch c c' := by
  unfold execE0 at h
  cases he : exec E ch fuel c with
  | closed d => simp [he] at h; cases h; exact exec_sound he
  | outOfBudget d => simp [he] at h
  | refused r => simp [he] at h

theorem runE0_sound {E : Elab} {ch : Choice} {fuel : Nat} {env : List SvState}
    {rows : List E0Row} (h : runE0 E ch fuel env = .ok rows) :
    ∀ row ∈ rows, SlotCloses E ch row.1 row.2 := by
  have tail_sound : ∀ (c : Config) (es : List SvState) (rs : List E0Row),
      runE0Tail E ch fuel c es = .ok rs →
      ∀ row ∈ rs, SlotCloses E ch row.1 row.2 := by
    intro c es
    induction es generalizing c with
    | nil =>
        intro rs h row hr
        simp [runE0Tail] at h
        subst rs
        simp at hr
    | cons e es ih =>
        intro rs h row hr
        simp only [runE0Tail] at h
        cases he : execE0 E ch fuel (Config.nextSlot E c e) with
        | timeout => simp [he] at h
        | unsupported msg => simp [he] at h
        | ok c' =>
            simp only [he] at h
            cases ht : runE0Tail E ch fuel c' es with
            | timeout => simp [ht] at h
            | unsupported msg => simp [ht] at h
            | ok rs' =>
                simp only [ht, Res.ok.injEq] at h
                cases h
                simp only [List.mem_cons] at hr
                rcases hr with rfl | hr
                · exact execE0_sound he
                · exact ih c' rs' ht row hr
  cases env with
  | nil => simp [runE0] at h; subst h; simp
  | cons entry rest =>
      simp only [runE0] at h
      cases he : execE0 E ch fuel (Config.start E entry) with
      | timeout => simp [he] at h
      | unsupported msg => simp [he] at h
      | ok c0 =>
          simp only [he] at h
          cases ht : runE0Tail E ch fuel c0 rest with
          | timeout => simp [ht] at h
          | unsupported msg => simp [ht] at h
          | ok rs =>
              simp only [ht, Res.ok.injEq] at h
              cases h
              intro row hr
              simp only [List.mem_cons] at hr
              rcases hr with rfl | hr
              · exact execE0_sound he
              · exact tail_sound c0 rest rs ht row hr

end LeanModels.Sv.Kernel
