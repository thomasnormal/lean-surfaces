import LeanModels.Sv.Loop2Frag
import LeanModels.Sv.XorSum

/-!
# The nested `clmul` loop, proved through the loop library (WS3, G1) — *provisional over `run2`*

**The design-specific definitions** of the nested `clmul` proof: the instantiated body, its
declarations and the double XOR sum. The proof itself is `svgolf/design/loop/g1/ClmulNested.lean`;
these definitions live under `LeanModels` only so that the printed-recurrence pin
(`Examples/system-verilog/loop_nested_clmul/rows_hint.lean`) can import them too.

```systemverilog
always_comb begin
  p = '0;
  for (int i = 0; i < N; i++)
    for (int j = 0; j < N; j++)
      p[i+j] = p[i+j] ^ (a[i] & b[j]);
end
```

* `clmulBody N W` is the instantiated body: the one-level `initLoop` shape whose trip is itself a
  loop (`sv_loop_sem` proves `sem N` is it; `sv_loop_rows` reads it as an outer and an inner row).
* `cx` is the double XOR sum the rows compute on known inputs.
-/

namespace LeanModels.Sv.Loop2.Clmul

open LeanModels.Sv LeanModels.Sv.Loop2 LeanModels.Sv.XorSum

/-! ## The instantiated body -/

/-- The right-hand side of trip `(i, j)`: `p[i+j] ^ (a[i] & b[j])`. -/
def tripExpr (i j : Nat) : Expr2 :=
  .binary .xor (.slice (.ident "p") (i + j) 1)
    (.binary .and (.slice (.ident "a") i 1) (.slice (.ident "b") j 1))

/-- Outer trip `i`: the inner loop over `j`. -/
def clmulTrip (N i : Nat) : Stmt2 :=
  .block #[.block ((List.range N).map fun j =>
    .block #[.blockingAssign (.slice "p" (i + j) 1) (tripExpr i j)]).toArray]

/-- The instantiated body: `p = '0` at `p`'s declared width `W`, then the nest. -/
def clmulBody (N W : Nat) : Stmt2 := initLoop "p" (LVec.replicate W .l0) N (clmulTrip N)

/-- The instantiated declarations: `a`, `b` (inputs, `N` bits), `p` (output, `W` bits). -/
def clmulDecls (N W : Nat) : Array Decl :=
  #[{ name := "a", width := N, isInput := true }, { name := "b", width := N, isInput := true },
    { name := "p", width := W, isOutput := true }]

/-! ## The arithmetic -/

/-- The double XOR sum of the product's coefficient `m` after `k` outer trips. -/
def cx (N : Nat) (x y : BitVec N) (k m : Nat) : Bool :=
  bx (fun i => bx (fun j => decide (i + j = m) && x.getLsbD i && y.getLsbD j) N) k

end LeanModels.Sv.Loop2.Clmul

