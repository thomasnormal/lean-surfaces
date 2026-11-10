import LeanModels.Sv.Kernel.ArrayE
import LeanModels.Sv.Kernel.RunE

/-!
# Multi-slot array-backed E-core-0 driver

`execE0Array`/`runE0Array` are the fast X-layer route for E-core-0.  They use
the array-backed microstep executor from `ArrayE`; the result and soundness
surface match `RunE`, while `execArray_sound` keeps the authoritative
`SlotCloses` judgment in the proof.
-/

namespace LeanModels.Sv.Kernel

set_option autoImplicit false

def execE0Array (E : Elab) (ch : Choice) (fuel : Nat) (c : Config) : Res Config :=
  match execArray E ch fuel c with
  | .closed c' => .ok c'
  | .outOfBudget _ => .timeout
  | .refused r => .unsupported r.observable.2

def runE0ArrayTail (E : Elab) (ch : Choice) (fuel : Nat) :
    Config → List SvState → Res (List E0Row)
  | _, [] => .ok []
  | c, entry :: rest =>
      let start := Config.nextSlot E c entry
      match execE0Array E ch fuel start with
      | .ok closed =>
          match runE0ArrayTail E ch fuel closed rest with
          | .ok rows => .ok ((start, closed) :: rows)
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

def runE0Array (E : Elab) (ch : Choice) (fuel : Nat) (env : List SvState) :
    Res (List E0Row) :=
  match env with
  | [] => .ok []
  | entry :: rest =>
      let start := Config.start E entry
      match execE0Array E ch fuel start with
      | .ok closed =>
          match runE0ArrayTail E ch fuel closed rest with
          | .ok rows => .ok ((start, closed) :: rows)
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

theorem execE0Array_sound {E : Elab} {ch : Choice} {fuel : Nat} {c c' : Config}
    (h : execE0Array E ch fuel c = .ok c') : SlotCloses E ch c c' := by
  unfold execE0Array at h
  cases he : execArray E ch fuel c with
  | closed d => simp [he] at h; cases h; exact execArray_sound he
  | outOfBudget d => simp [he] at h
  | refused r => simp [he] at h

theorem runE0Array_sound {E : Elab} {ch : Choice} {fuel : Nat} {env : List SvState}
    {rows : List E0Row} (h : runE0Array E ch fuel env = .ok rows) :
    ∀ row ∈ rows, SlotCloses E ch row.1 row.2 := by
  have tail_sound : ∀ (c : Config) (es : List SvState) (rs : List E0Row),
      runE0ArrayTail E ch fuel c es = .ok rs →
      ∀ row ∈ rs, SlotCloses E ch row.1 row.2 := by
    intro c es
    induction es generalizing c with
    | nil =>
        intro rs h row hr
        simp [runE0ArrayTail] at h
        subst rs
        simp at hr
    | cons e es ih =>
        intro rs h row hr
        simp only [runE0ArrayTail] at h
        cases he : execE0Array E ch fuel (Config.nextSlot E c e) with
        | timeout => simp [he] at h
        | unsupported msg => simp [he] at h
        | ok c' =>
            simp only [he] at h
            cases ht : runE0ArrayTail E ch fuel c' es with
            | timeout => simp [ht] at h
            | unsupported msg => simp [ht] at h
            | ok rs' =>
                simp only [ht, Res.ok.injEq] at h
                cases h
                simp only [List.mem_cons] at hr
                rcases hr with rfl | hr
                · exact execE0Array_sound he
                · exact ih c' rs' ht row hr
  cases env with
  | nil => simp [runE0Array] at h; subst h; simp
  | cons entry rest =>
      simp only [runE0Array] at h
      cases he : execE0Array E ch fuel (Config.start E entry) with
      | timeout => simp [he] at h
      | unsupported msg => simp [he] at h
      | ok c0 =>
          simp only [he] at h
          cases ht : runE0ArrayTail E ch fuel c0 rest with
          | timeout => simp [ht] at h
          | unsupported msg => simp [ht] at h
          | ok rs =>
              simp only [ht, Res.ok.injEq] at h
              cases h
              intro row hr
              simp only [List.mem_cons] at hr
              rcases hr with rfl | hr
              · exact execE0Array_sound he
              · exact tail_sound c0 rest rs ht row hr

end LeanModels.Sv.Kernel
