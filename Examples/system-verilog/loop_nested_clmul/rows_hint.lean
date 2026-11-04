import LeanModels.Sv.Loop2Clmul

/-!
# `sv_loop_rows` on the nested `clmul`: the printed recurrence, pinned verbatim

`sv_loop_rows` (`LeanModels/Sv/Loop2Frag.lean`, the recursive recognizer) on the instantiated body
`p = '0; for i < N: for j < N: p[i+j] = p[i+j] ^ (a[i] & b[j])` introduces the loop's recurrence
over its trips: `row st i` is `p` before outer trip `i` (from the start state `st`), and since the
outer trip is itself a loop, `row_in st i j` is `p` before its inner trip `j`. Each comes with its
start, one step per trip as a plain equation on values (`sig st x` reads a signal the body does not
write), the link between the levels, the width, and the link to the body's meaning (`body_step`,
the function whose run Bridge S takes over `run2` and `CombTask.satisfiedAt_obs_of_frag` over E). No fuel, no `Denotes`, no block plumbing, no settle in the goal. A change of the
vocabulary or of the normal form of the step is a visible diff here.
-/

open LeanModels.Sv LeanModels.Sv.Loop2 LeanModels.Sv.Loop2.Clmul

namespace Examples.«system-verilog».loop_nested_clmul.rows_hint

/--
trace: N W : Nat
row : SvState → Nat → LVec
row_init : ∀ (st : SvState), row st 0 = (LVec.replicate W Logic.l0).resizeU (sig st "p").width
row_width : ∀ (st : SvState) (k : Nat), (row st k).width = (sig st "p").width
body_step : ∀ (st : SvState), Stmt2.step "p" st (clmulBody N W) (sig st "p") = row st N
row_in : SvState → Nat → Nat → LVec
row_in_init : ∀ (st : SvState) (i : Nat), row_in st i 0 = row st i
row_in_step :
  ∀ (st : SvState) (i j : Nat),
    row_in st i (j + 1) =
      (row_in st i j).insertAt (i + j)
        ((evalBinOp BinOp.xor ((row_in st i j).extract (i + j) 1)
              (evalBinOp BinOp.and ((sig st "a").extract i 1) ((sig st "b").extract j 1))).resizeU
          1)
row_next : ∀ (st : SvState) (i : Nat), row st (i + 1) = row_in st i N
⊢ True
-/
#guard_msgs (whitespace := lax) in
example (N W : Nat) : True := by
  sv_loop_rows (body := clmulBody N W) [clmulTrip, tripExpr]
  trace_state
  trivial

end Examples.«system-verilog».loop_nested_clmul.rows_hint
