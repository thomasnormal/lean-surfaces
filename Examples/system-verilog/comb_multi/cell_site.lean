import LeanModels.Sv.CombProcSummary
import LeanModels.Sv.PinAxioms

/-!
# The two-window cell lowers, at a symbolic `N` and every bit `k < N`, through `lower_body_site` (WP-G S1b gate c4)

`add_proc_m.sv`'s bit cell is ONE `always_comb` body that writes `c[i+1]` (an `if/else` over `p[i]`) and `s[i]`
(`p[i] ^ c[i]`). `CombProc.multiSegs?` reads it as two segments; this file instantiates it at `i = k` in ANY
instantiation environment of the adder `apDesign N` (the widths of the declarations, the one-bit elements) and shows,
through the several-window `lower_site` of `CombProcBody.lean` (`lower_body_site`), that the lowering of the
instantiated process is ONE assign of both windows, `{c[k+1], s[k]} = {…, …}`, for every `N` and every `k < N`: the
template-level counterpart of `carry_lowers` (`CombProc.lean`) for a body of several windows.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombProc

namespace Examples.«system-verilog».comb_multi.cell_site

/-- The two segments of the cell, as the recognizer reads them. -/
def cellSegs : List (Acc × PTR) :=
  [(.bit "c" ⟨[("i", 1)], 1, []⟩,
      .ite (.bitSel (.ident "p") (.genvarRef "i")) [.bit "p" ⟨[("i", 1)], 0, []⟩]
        (.leafL carryLhs (.bitSel (.ident "c") (.genvarRef "i")) [.bit "c" ⟨[("i", 1)], 0, []⟩])
        (.leafL carryLhs (.bitSel (.ident "a") (.genvarRef "i")) [.bit "a" ⟨[("i", 1)], 0, []⟩])),
    (.bit "s" ⟨[("i", 1)], 0, []⟩,
      .leafL sumLhs
        (.binary (.m0 .xor) (.bitSel (.ident "p") (.genvarRef "i")) (.bitSel (.ident "c") (.genvarRef "i")))
        [.bit "p" ⟨[("i", 1)], 0, []⟩, .bit "c" ⟨[("i", 1)], 0, []⟩])]

/-- The recognizer reads `cellBody` as exactly these two segments (evaluated by the kernel). -/
theorem cellSegs_ok : multiSegs? apDecls cellBody = .ok cellSegs := by
  rfl


/-! ## The instantiation context of the adder -/

/-- The valuation: the genvar `i` is the bit `k`. -/
def cellσ (k : Nat) : String → Int := fun n => if n = "i" then (k : Int) else 0

/-- The elements the cell reads and writes are single bits. -/
def cellEW : String → Option Nat := fun n => if n = "a" ∨ n = "c" ∨ n = "p" ∨ n = "s" then some 1 else none

/-- The declared widths of `apDesign N`, as a function. -/
def cellDW (N : Nat) : String → Nat := fun n => ((apDesign N).declWidth n).getD 0

theorem ap_declWidth_a (N : Nat) : (apDesign N).declWidth "a" = some N := by simp [Design2.declWidth, apDesign]
theorem ap_declWidth_p (N : Nat) : (apDesign N).declWidth "p" = some N := by simp [Design2.declWidth, apDesign]
theorem ap_declWidth_s (N : Nat) : (apDesign N).declWidth "s" = some N := by simp [Design2.declWidth, apDesign]

/-- A bit access `n[i + c]` of the cell at `i = k`: its window is `(n, k + c, 1)`. -/
theorem win_cellBit (k : Nat) (dw : String → Nat) (n : String) (c : Int) :
    (Acc.bit n ⟨[("i", 1)], c, []⟩).win (cellσ k) dw = (n, ((k : Int) + c).toNat, 1) := by
  simp [Acc.win, Acc.lo, Aff.eval, Aff.evalTerms, cellσ]

theorem accOK_cellBit (N k : Nat) (n : String) (c : Int) (hn : ((apDesign N).declWidth n).isSome = true)
    (he : n = "a" ∨ n = "c" ∨ n = "p" ∨ n = "s") (hc : 0 ≤ (k : Int) + c) :
    AccOK (cellσ k) (apDesign N).declWidth (fun _ => none) cellEW ["i"] (.bit n ⟨[("i", 1)], c, []⟩) := by
  refine ⟨hn, ⟨?_, ?_⟩, ?_⟩
  · simpa [Aff.eval, Aff.evalTerms, cellσ] using hc
  · simp [cellEW, he]
  · intro x hx m hm
    simp only [Acc.affs, List.mem_singleton] at hx
    subst hx
    simpa [Aff.names] using hm

/-- **The two-window cell lowers to ONE assign of both windows**, for every `N`, every bit `k < N` and every
instantiation environment of the adder that binds `i` to `k` and knows the one-bit elements. -/
theorem cell_lowers_site (N k : Nat) (hk : k < N) (E : IEnv) (elems : List (String × Nat))
    (hi : E.vals.lookup "i" = some (k : Int))
    (hwd : ∀ n, E.widths.lookup n = (apDesign N).declWidth n)
    (hel : ∀ n, (n = "a" ∨ n = "c" ∨ n = "p" ∨ n = "s") → elems.lookup n = some 1) :
    Process2.lowerComb (apDesign N) (instProcess2 E elems (.alwaysComb cellBody)) =
      some (.assign (.concat [.slice "c" (k + 1) 1, .slice "s" k 1])
        (.concat (cellSegs.map fun s => (s.2.pt.low E elems 1).low 1).toArray)) := by
  have C : Ctx (cellσ k) E elems (apDesign N).declWidth (fun _ => none) cellEW ["i"] :=
    { agree := by
        intro n hn
        rw [List.mem_singleton] at hn
        subst hn
        simp [cellσ, IEnv.intVal?, hi]
      widths := hwd
      elemsG := by intro n ds h; simp at h
      elems := by
        intro n hn
        apply hel
        by_cases h : n = "a" ∨ n = "c" ∨ n = "p" ∨ n = "s"
        · exact h
        · simp [cellEW, h] at hn
      dims := by intro n ds h; simp at h }
  have hdw : ∀ n, ((apDesign N).declWidth n).isSome = true →
      (apDesign N).declWidth n = some (cellDW N n) := by
    intro n hn
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hn
    simp [cellDW, hw]
  obtain ⟨ss, hbss, hbody, hsok, -⟩ := multiSegs?_spec apDecls cellBody cellSegs cellSegs_ok
  have hok : ∀ s ∈ cellSegs, s.2.Ok apDecls s.1 := hsok
  have hwin : cellSegs.map (fun s => s.1.win (cellσ k) (cellDW N)) = [("c", k + 1, 1), ("s", k, 1)] := by
    simp only [cellSegs, List.map_cons, List.map_nil, win_cellBit]
    simp
  have hat : ∀ s ∈ cellSegs, AccOK (cellσ k) (apDesign N).declWidth (fun _ => none) cellEW ["i"] s.1 := by
    intro s hs
    simp only [cellSegs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact accOK_cellBit N k "c" 1 (by simp [Design2.declWidth, apDesign]) (by simp) (by omega)
    · exact accOK_cellBit N k "s" 0 (by simp [ap_declWidth_s]) (by simp) (by omega)
  have hrd : ∀ s ∈ cellSegs, ∀ a ∈ s.2.rds,
      AccOK (cellσ k) (apDesign N).declWidth (fun _ => none) cellEW ["i"] a := by
    intro s hs a ha
    simp only [cellSegs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · simp only [PTR.rds, List.mem_append, List.mem_singleton] at ha
      rcases ha with (rfl | rfl) | rfl
      · exact accOK_cellBit N k "p" 0 (by simp [ap_declWidth_p]) (by simp) (by omega)
      · exact accOK_cellBit N k "c" 0 (by simp [Design2.declWidth, apDesign]) (by simp) (by omega)
      · exact accOK_cellBit N k "a" 0 (by simp [ap_declWidth_a]) (by simp) (by omega)
    · simp only [PTR.rds, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact accOK_cellBit N k "p" 0 (by simp [ap_declWidth_p]) (by simp) (by omega)
      · exact accOK_cellBit N k "c" 0 (by simp [Design2.declWidth, apDesign]) (by simp) (by omega)
  have hin : ∀ s ∈ cellSegs,
      (s.1.win (cellσ k) (cellDW N) |>.2.1) + (s.1.win (cellσ k) (cellDW N) |>.2.2) ≤ cellDW N s.1.name := by
    intro s hs
    simp only [cellSegs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · simp [win_cellBit, cellDW, Acc.name, Design2.declWidth, apDesign]; omega
    · simp [win_cellBit, cellDW, Acc.name, ap_declWidth_s]; omega
  have hpos : ∀ s ∈ cellSegs, 0 < (s.1.win (cellσ k) (cellDW N)).2.2 := by
    intro s hs
    simp only [cellSegs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp [win_cellBit]
  have hself : ∀ s ∈ cellSegs, ∀ a ∈ s.2.rds, ∀ s' ∈ cellSegs,
      (a.rd (cellσ k)).overlaps (s'.1.win (cellσ k) (cellDW N)) = false := by
    intro s hs a ha s' hs'
    simp only [cellSegs, List.mem_cons, List.not_mem_nil, or_false] at hs hs'
    rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl <;>
      simp [PTR.rds, win_cellBit, Acc.rd, Acc.lo, Aff.eval, Aff.evalTerms, cellσ, ReadWin.overlaps,
        Win.overlaps] at ha ⊢ <;>
      rcases ha with rfl | rfl | rfl <;>
      simp [Acc.rd, Acc.lo, Aff.eval, Aff.evalTerms, cellσ, ReadWin.overlaps, Win.overlaps]
  have hdisj : Win.allDisjoint (cellSegs.map fun s => s.1.win (cellσ k) (cellDW N)) = true := by
    rw [hwin]
    simp [Win.allDisjoint, Win.overlaps]
  have hL := lower_body_site C (dw := cellDW N) hdw (d := apDesign N) (fun n => rfl) (ds := apDecls)
    cellSegs hat hin hok hrd hself hpos hdisj
  have hproc : instProcess2 E elems (.alwaysComb cellBody) =
      instProcess2 E elems (.alwaysComb (bodyP2 cellSegs)) := by rw [hbss, hbody]
  rw [hproc, hL, hwin]
  have hw1 : ∀ s ∈ cellSegs, (s.1.win (cellσ k) (cellDW N)).2.2 = 1 := by
    intro s hs
    simp only [cellSegs, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simp [win_cellBit]
  have hmap : (cellSegs.map fun s =>
      (s.2.pt.low E elems (s.1.win (cellσ k) (cellDW N)).2.2).low (s.1.win (cellσ k) (cellDW N)).2.2) =
      cellSegs.map fun s => (s.2.pt.low E elems 1).low 1 :=
    List.map_congr_left fun s hs => by rw [hw1 s hs]
  rw [hmap]
  simp [Win.lhs]

#pin_axioms cellSegs_ok win_cellBit accOK_cellBit cell_lowers_site

end Examples.«system-verilog».comb_multi.cell_site
