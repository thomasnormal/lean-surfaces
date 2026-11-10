import LeanModels.Sv.Kernel.Core1Obs

/-! Fuelled X-layer driver for the E-core-1 edge fragment. -/

namespace LeanModels.Sv.Kernel

set_option autoImplicit false

abbrev E1Row := Config1 × Config1

def execE1 (E : Elab1) (ch : Choice) (fuel : Nat) (c : Config1) : Res Config1 :=
  match exec1 E ch fuel c with
  | .closed c' => .ok c'
  | .outOfBudget _ => .timeout
  | .refused msg => .unsupported msg

def runE1Tail (E : Elab1) (ch : Choice) (fuel : Nat) (clk : String) :
    Config1 → List SvState → Res (List E1Row)
  | c, [] => .ok []
  | c, entry :: rest =>
      let start := Config1.nextSlot E c (slotEntry1 clk [entry] 0)
      match execE1 E ch fuel start with
      | .ok closed =>
          match runE1Tail E ch fuel clk closed rest with
          | .ok rows => .ok ((start, closed) :: rows)
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

/-- Run one finite cycle batch through E-core-1's test executor. -/
def runE1 (E : Elab1) (ch : Choice) (fuel : Nat) (clk : String)
    (env : List SvState) : Res (List E1Row) :=
  match env with
  | [] => .ok []
  | entry :: rest =>
      let start := Config1.nextSlot E (Config1.init E) (slotEntry1 clk [entry] 0)
      match execE1 E ch fuel start with
      | .ok closed =>
          match runE1Tail E ch fuel clk closed rest with
          | .ok rows => .ok ((start, closed) :: rows)
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg

theorem execE1_sound {E : Elab1} {ch : Choice} {fuel : Nat} {c c' : Config1}
    (h : execE1 E ch fuel c = .ok c') : SlotCloses1 E ch c c' := by
  unfold execE1 at h
  cases he : exec1 E ch fuel c with
  | closed d => simp [he] at h; cases h; exact exec1_sound he
  | outOfBudget d => simp [he] at h
  | refused msg => simp [he] at h

theorem runE1_sound {E : Elab1} {ch : Choice} {fuel : Nat} {clk : String}
    {env : List SvState} {rows : List E1Row}
    (h : runE1 E ch fuel clk env = .ok rows) :
    ∀ row ∈ rows, SlotCloses1 E ch row.1 row.2 := by
  have tail_sound : ∀ (c : Config1) (es : List SvState) (rs : List E1Row),
      runE1Tail E ch fuel clk c es = .ok rs →
      ∀ row ∈ rs, SlotCloses1 E ch row.1 row.2 := by
    intro c es
    induction es generalizing c with
    | nil =>
        intro rs h row hr
        simp [runE1Tail] at h
        subst rs
        simp at hr
    | cons e es ih =>
        intro rs h row hr
        simp only [runE1Tail] at h
        cases he : execE1 E ch fuel (Config1.nextSlot E c (slotEntry1 clk [e] 0)) with
        | timeout => simp [he] at h
        | unsupported msg => simp [he] at h
        | ok c' =>
            simp only [he] at h
            cases ht : runE1Tail E ch fuel clk c' es with
            | timeout => simp [ht] at h
            | unsupported msg => simp [ht] at h
            | ok rs' =>
                simp only [ht, Res.ok.injEq] at h
                cases h
                simp only [List.mem_cons] at hr
                rcases hr with rfl | hr
                · exact execE1_sound he
                · exact ih c' rs' ht row hr
  cases env with
  | nil => simp [runE1] at h; subst h; simp
  | cons entry rest =>
      simp only [runE1] at h
      cases he : execE1 E ch fuel
          (Config1.nextSlot E (Config1.init E) (slotEntry1 clk [entry] 0)) with
      | timeout => simp [he] at h
      | unsupported msg => simp [he] at h
      | ok c0 =>
          simp only [he] at h
          cases ht : runE1Tail E ch fuel clk c0 rest with
          | timeout => simp [ht] at h
          | unsupported msg => simp [ht] at h
          | ok rs =>
              simp only [ht, Res.ok.injEq] at h
              cases h
              intro row hr
              simp only [List.mem_cons] at hr
              rcases hr with rfl | hr
              · exact execE1_sound he
              · exact tail_sound c0 rest rs ht row hr

end LeanModels.Sv.Kernel
