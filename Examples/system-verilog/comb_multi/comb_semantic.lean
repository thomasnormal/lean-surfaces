import Examples.«system-verilog».comb_multi.gen
import LeanModels.Sv.CombProcStmt

/-!
# The lowering of a body that writes two windows (WP-G S1b, gate a)

`add_proc_m.sv`'s bit cell is ONE `always_comb` body with two written windows, `c[i+1]` (an `if/else` tree) and
`s[i]` (an assignment). `CombProcStmt.lean` proves the semantic core for any list of such segments (`Seg`):

* `symExec_body`: the symbolic execution of the body is the entries of its segments in order;
* `combAdmits_body`: the self-read guard admits it;
* `lower_body_plain` / `lower_body`: `Process2.lowerComb` of it IS the single assign `{W₀, …, Wₖ} = {E₀, …, Eₖ}`.

Here the statement meets the real design:

* `cell_lowers`: for EVERY bit `i` and every design that declares `c`, `s` wide enough and the names `a`, `p`, `c`,
  the lowering of the cell body `cellSegs i` is the assign `{c[i+1], s[i]} = {…, …}` (symbolic `i`);
* at `N = 2` the instantiated design's `always_comb` processes ARE the bodies `cellSegs 0` and `cellSegs 1`, and the
  design's own `Design2.lowerComb` replaces them by exactly `cellAssign 0` and `cellAssign 1` (`#guard`s on the real
  `add_proc_m.sem 2`: `sem` is compiled code, the kernel cannot reduce it, so a concrete-width fact about the real
  design is a `#guard`, as everywhere in these examples).

The summary (`sv_structure`) does not read such a body yet (gate c): this file is about the semantics.
-/

open LeanModels.Sv LeanModels.Sv.CombProc
open Examples.«system-verilog».comb_multi.gen

namespace Examples.«system-verilog».comb_multi.comb_semantic

/-- The two segments of the bit cell `i`: the carry `if (p[i]) c[i+1] = c[i]; else c[i+1] = a[i];` over the
window `c[i+1]`, and the sum `s[i] = p[i] ^ c[i];` over `s[i]`. -/
def cellSegs (i : Nat) : List Seg :=
  [⟨.slice "c" (i + 1) 1, ("c", i + 1, 1),
      .ite (.slice (.ident "p") i 1) (.leaf (.slice (.ident "c") i 1)) (.leaf (.slice (.ident "a") i 1))⟩,
   ⟨.slice "s" i 1, ("s", i, 1),
      .leaf (.binary .xor (.slice (.ident "p") i 1) (.slice (.ident "c") i 1))⟩]

/-- The single assign the cell body lowers to: `{c[i+1], s[i]} = {p[i] ? c[i] : a[i], p[i] ^ c[i]}`. -/
def cellAssign (i : Nat) : Process2 :=
  .assign (.concat [Win.lhs ("c", i + 1, 1), Win.lhs ("s", i, 1)])
    (.concat #[Expr2.joinIte (Expr2.ifGuard (.slice (.ident "p") i 1))
        (.resize 1 (.slice (.ident "c") i 1)) (.resize 1 (.slice (.ident "a") i 1)),
      .resize 1 (.binary .xor (.slice (.ident "p") i 1) (.slice (.ident "c") i 1))])

/-- The static facts of the cell, for any design that declares the signals wide enough. -/
theorem cell_bodyOk (d : Design2) (wd : String → Option Nat) (i wc ws : Nat)
    (hc : d.declWidth "c" = some wc) (hwc : i + 2 ≤ wc) (hs : d.declWidth "s" = some ws)
    (hws : i + 1 ≤ ws) (ha : "a" ∈ d.symNames) (hp : "p" ∈ d.symNames) (hcn : "c" ∈ d.symNames) :
    BodyOk d wd (cellSegs i) := by
  have hseg : ∀ sg ∈ cellSegs i, SegOk d (bodyWins (cellSegs i)) sg := by
    intro sg hsg
    simp only [cellSegs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hsg
    rcases hsg with rfl | rfl
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [Lhs2.symWin, Lhs2.window?, hc]; omega
      · simp [PTree.wf, Expr2.wfB, Expr2.unsupportedFree, Expr2.idents, ha, hp, hcn]
      · simp [PTree.idxFree, Expr2.idxFree]
      · intro V hV
        simp only [bodyWins, cellSegs, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hV
        rcases hV with rfl | rfl <;>
          simp [PTree.noRead, Expr2.reads, Expr2.sliceReads, ReadWin.apart, ReadWin.pos,
            ReadWin.overlaps, Win.overlaps] <;> omega
      · simp [bodyWins, cellSegs]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [Lhs2.symWin, Lhs2.window?, hs]; omega
      · simp [PTree.wf, Expr2.wfB, Expr2.unsupportedFree, Expr2.idents, hp, hcn]
      · simp [PTree.idxFree, Expr2.idxFree]
      · intro V hV
        simp only [bodyWins, cellSegs, List.map_cons, List.map_nil, List.mem_cons,
          List.not_mem_nil, or_false] at hV
        rcases hV with rfl | rfl <;>
          simp [PTree.noRead, Expr2.reads, Expr2.sliceReads, ReadWin.apart, ReadWin.pos,
            ReadWin.overlaps, Win.overlaps] <;> omega
      · simp [bodyWins, cellSegs]
  refine ⟨?_, ?_, hseg, ?_, ?_⟩
  · simp [bodyWins, cellSegs]
  · simp [bodyWins, cellSegs, Win.allDisjoint, Win.overlaps]
  · intro sg hsg
    simp only [cellSegs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hsg
    rcases hsg with rfl | rfl <;> simp [Lhs2.mayW, Win.lhs]
  · intro sg hsg
    simp only [cellSegs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hsg
    rcases hsg with rfl | rfl <;> simp [Lhs2.rdW]

/-- **The lowering of the bit cell is the two-window assign**, for every bit `i`. -/
theorem cell_lowers (d : Design2) (i wc ws : Nat)
    (hc : d.declWidth "c" = some wc) (hwc : i + 2 ≤ wc) (hs : d.declWidth "s" = some ws)
    (hws : i + 1 ≤ ws) (ha : "a" ∈ d.symNames) (hp : "p" ∈ d.symNames) (hcn : "c" ∈ d.symNames) :
    Process2.lowerComb d (.alwaysComb (bodyStmt (cellSegs i))) = some (cellAssign i) := by
  have hok := cell_bodyOk d (fun _ => none) i wc ws hc hwc hs hws ha hp hcn
  exact lower_body_plain d (cellSegs i) (bodyWins (cellSegs i)) hok.pos hok.disj hok.seg
    (fun sg hsg => (hok.seg sg hsg).nr)

/-- … and the guard admits the body (so the instantiated process is the body itself). -/
theorem cell_admitted (d : Design2) (wd : String → Option Nat) (i wc ws : Nat)
    (hc : d.declWidth "c" = some wc) (hwc : i + 2 ≤ wc) (hs : d.declWidth "s" = some ws)
    (hws : i + 1 ≤ ws) (ha : "a" ∈ d.symNames) (hp : "p" ∈ d.symNames) (hcn : "c" ∈ d.symNames) :
    (bodyStmt (cellSegs i)).combAdmits wd = true :=
  combAdmits_body d wd (cellSegs i) (cell_bodyOk d wd i wc ws hc hwc hs hws ha hp hcn)

private def isComb : Process2 → Bool
  | .alwaysComb _ => true
  | _ => false

private def isTwoWindow : Process2 → Bool
  | .assign (.concat [_, _]) _ => true
  | _ => false

/- The real design (`sem` is compiled code, not kernel-reducible: the concrete-width check of the instantiated
design is a `#guard`, like every other fact about `X.sem N` in these examples). At `N = 2` the design's two
`always_comb` processes ARE the bodies `cellSegs 0` and `cellSegs 1` … -/
#guard (((add_proc_m.sem 2).processes.toList.filter isComb).map fun p => (repr p).pretty) ==
  [(repr (Process2.alwaysComb (bodyStmt (cellSegs 0)))).pretty,
   (repr (Process2.alwaysComb (bodyStmt (cellSegs 1)))).pretty]

/- … and the design's own lowering (`Design2.lowerComb`) replaces them by exactly the assigns `cell_lowers`
predicts (`cellAssign 0`, `cellAssign 1`), in place. -/
#guard ((add_proc_m.sem 2).lowerComb.map fun d =>
    (d.processes.toList.filter isTwoWindow).map fun p => (repr p).pretty) ==
  some [(repr (cellAssign 0)).pretty, (repr (cellAssign 1)).pretty]

/- The statically checkable side conditions hold at `N = 2` (declared widths, names). -/
#guard ((add_proc_m.sem 2).declWidth "c" == some 3) && ((add_proc_m.sem 2).declWidth "s" == some 2) &&
  ["a", "p", "c"].all fun n => decide (n ∈ (add_proc_m.sem 2).symNames)

end Examples.«system-verilog».comb_multi.comb_semantic
