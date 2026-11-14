import Lean
import LeanModels.Sv.CombViewDiag
import LeanModels.Sv.CombCoreSimp
import LeanModels.Sv.CombViewPlain
import LeanModels.Sv.CombViewGroup
import LeanModels.Sv.CombShared
import LeanModels.Sv.CombAliasInert
import LeanModels.Sv.CombSigned

/-!
# `sv_structure` / `sv_structure?`: the structural stage of the `sv_comb` tactic (v0)

```
theorem ripple_comb (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_add.sem N) := by
  sv_structure
  -- leaves ONLY the driver-window disjointness and in-range goals, as compact `∀`s
theorem ripple_acyclic (N : Nat) (hN : 1 ≤ N) : Acyclic (ripple_add.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  -- leaves the in-range / disjointness goals and the rank-decrease goals
theorem mul_acyclic (N : Nat) (hN : 1 ≤ N) : Acyclic (mul_n.sem N) := by
  sv_structure (lexRank := fun | .plain 0 => (0, 1, 0) | … | .fam "g_bit" 0 [i, j] => (i.toNat, j.toNat + 1, 1) …)
  -- the rank is a LEXICOGRAPHIC key (row, column, phase) over site identities
theorem mul_acyclic' (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (mul_n.sem N)) : Acyclic (mul_n.sem N) := by
  sv_structure using hc (lexRank := …)   -- the in-range and one-driver goals are not asked again
theorem ripple_struct (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_add.sem N) ∧ Acyclic (ripple_add.sem N) := by
  sv_structure (rank := rippleRank …)   -- ONE round of obligations for both (WP-P): `obtain ⟨hc, ha⟩ := ripple_struct N hN`
sv_structure?            -- prints the families, site identities and the required rank relation
```

What it does: reads the design off the goal (`X.sem N` is `PDesign.instantiateGDAlias2 X.pdesign [↑N]`, the
`always_comb` alias guard over `PDesign.instantiateGD2 X.pdesign [↑N]`; the goal is restated at the latter, the guard
shown inert by a static check, `CombAliasInert.lean`), runs the recognizer `PDesign.summary` (a refusal is an error
with the specific reason, naming the site), applies the theorem `comb_view`/`acyclic_view` (whose hypotheses are
CHECKED by `rfl` and `decide`: the parameter stage, the structural facts, the fuel; at a symbolic `int` parameter
the exact 32-bit reading of the parameters is checked against the summary's valuation from the range premises in
context, `closeHag`), normalizes the player
obligations, and returns them. It never discharges the in-range, disjointness or rank goals of a
design with a generate loop or a parameter. Before returning them it SAMPLES them at small `N` (for the
message only): a genuine violation is reported with the offending sites instead of an unprovable goal.

**Flat netlists (WP-P3b).** When EVERY site is plain (no generate loop) and the design has no free
parameter, the four obligations (`hauto`, `hin`, `hdisj`, `hrank`) are closed statements about the site
list, and the tactic DECIDES them (`closeByDecide`, through `CombViewPlain.lean`) instead of normalizing
them with `simp`, whose cost is quadratic in the number of sites for the one-driver and rank
obligations (4 min and a failure at 113 sites; about 12 s and 120 M heartbeats now, linear). Nothing is
left to the player in that case (not even the rank goals `rank[4] < rank[5]`). A design with a loop or a
parameter, or a closed statement that is false (it then falls back to the normalization and its goals),
behaves exactly as before.

**Many sites (WP-LIN).** On a design that is NOT flat (a parameter or a generate loop) the one-driver and rank
obligations were quadratic in the number of sites under `simp` as well (thousands of heartbeats at 11 / 21 / 41 plain sites:
one-driver 16 187 / 45 372 / 161 430, rank 35 726 / 112 829 / 403 666): `DisjObl` states `DisjOne` for EVERY pair of sites
and `RankObl'` filters ALL sites for the writers of every read, while only sites that write the SAME signal can fail
to be disjoint or ranked (two windows of different signals never overlap). The tactic therefore first restricts those two
obligations to the related sites (`groupStructureGoal`): it lists, natively and without `simp`, the pairs of sites that
write one signal (`sameNamePairs`) and, for every read, the writers of the signal it reads (`rdWriters`), assigns the
lemma of `CombViewGroup.lean` (`disjObl_of_groups`, `rankObl'_of_groups`: the original obligation asked on the listed
sites only, nesting kept) whose `rfl` hypothesis the kernel checks once, and hands THAT goal to the usual normalization.
The goals that come out are the same ones, in the same order, and no simp list gained a name; if the listing fails for
any reason, or the design has fewer than `groupMinSites` (four) sites, the original goal is normalized as before. `set_option sv_comb.profile true` logs the heartbeats each
obligation's normalization costs (thousands), the diagnostic these figures came from.

**The shared obligations (perf, 2026-11-04).** On the triple `CombDesign D ∧ Acyclic D ∧ SharedObl X.pdesign [N]`
(`CombShared.lean`) the tactic proves the bundle and packages the `auto` and `inRange` obligations it normalized anyway, so
that `sv_equations` can take them from the context instead of normalizing them a second time (`comb_acyclic_shared_view`,
`comb_lex_shared_view`; the obligations returned are those of the bundle).
-/

open Lean Elab Tactic Meta

open LeanModels.Sv.CombView

/-- `set_option sv_comb.profile true`: the sv_comb tactics log, per obligation, the heartbeats (in thousands) its
normalization costs (WP-LIN: a diagnostic for the cost of a design with many sites; off by default, no cost). -/
register_option sv_comb.profile : Bool := {
  defValue := false
  descr := "sv_comb tactics: log the heartbeats the normalization of each obligation costs" }

/-- Run the normalization of the obligation `nm`; with `sv_comb.profile` set, log what it cost. -/
def svObProfile (nm : String) (act : TacticM Unit) : TacticM Unit := do
  if sv_comb.profile.get (← getOptions) then
    let b ← IO.getNumHeartbeats
    act
    let a ← IO.getNumHeartbeats
    logInfo m!"sv_comb profile: {nm} {(a - b) / 1000}k heartbeats"
  else act

/-- `set_option sv_comb.group_report true`: the sv_comb tactics say, per obligation, how large the list of related sites is that
the grouped route restricted it to (WP-LIN: deterministic, so a test can pin it; a design that took the original route says
nothing). -/
register_option sv_comb.group_report : Bool := {
  defValue := false
  descr := "sv_comb tactics: report the size of the grouped list each obligation was restricted to" }

/-- Say `msg` when `sv_comb.group_report` is set. -/
def svGroupReport (msg : String) : Lean.Meta.MetaM Unit := do
  if sv_comb.group_report.get (← Lean.getOptions) then Lean.logInfo msg

unsafe def evalSummary (pd : Expr) : MetaM (Except String Summary) := do
  let ty := mkApp2 (mkConst ``Except [Level.zero, Level.zero]) (mkConst ``String)
    (mkConst ``LeanModels.Sv.CombView.Summary)
  evalExpr (Except String Summary) ty (mkApp (mkConst ``LeanModels.Sv.PDesign.summary) pd)


unsafe def evalArgs (e : Expr) : MetaM (List Int) :=
  evalExpr (List Int) (mkApp (mkConst ``List [Level.zero]) (mkConst ``Int)) e


unsafe def evalRank (e : Expr) : MetaM (SiteId → Nat) :=
  evalExpr (SiteId → Nat)
    (Lean.mkForall `x BinderInfo.default (mkConst ``LeanModels.Sv.CombView.SiteId) (mkConst ``Nat)) e

unsafe def evalLex (e : Expr) : MetaM (SiteId → Key) :=
  evalExpr (SiteId → Key)
    (Lean.mkForall `x BinderInfo.default (mkConst ``LeanModels.Sv.CombView.SiteId)
      (mkConst ``LeanModels.Sv.CombView.Key)) e


namespace LeanModels.Sv.CombView

/-- `X.sem N` is the alias-guarded family `PDesign.instantiateGDAlias2 X.pdesign [↑N]` (since ls-sv 7c9b7ac59;
before it, and in a goal stated at it, the unguarded `PDesign.instantiateGD2 X.pdesign [↑N]`): unfold until one of
them shows. The third component is `true` for the guarded family, which the tactics first rewrite to the unguarded
one the comb theorems are stated for (`aliasInertEq`). -/
partial def findGD2A (e : Lean.Expr) (fuel : Nat) : MetaM (Option (Lean.Expr × Lean.Expr × Bool)) := do
  let e ← whnfCore e
  if e.isAppOfArity ``LeanModels.Sv.PDesign.instantiateGDAlias2 2 then
    return some (e.getAppArgs[0]!, e.getAppArgs[1]!, true)
  if e.isAppOfArity ``LeanModels.Sv.PDesign.instantiateGD2 2 then
    return some (e.getAppArgs[0]!, e.getAppArgs[1]!, false)
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    match ← unfoldDefinition? e with
    | some e' => findGD2A e' fuel
    | none => return none

/-- `X.sem N` of a design WITH module instances is `PDesign.instantiateHDAlias2 X.pdesign X.plib [↑N]`
(`PDesign.instantiateHD2` under the alias guard, `Hier2.lean`); the `sv_comb` tactics have no summary for it
(WP-I, step I0: say so instead of "cannot read a family"). -/
partial def isHD2Family (e : Lean.Expr) (fuel : Nat) : MetaM Bool := do
  let e ← whnfCore e
  if e.isAppOfArity `LeanModels.Sv.PDesign.instantiateHD2 3 ||
      e.isAppOfArity `LeanModels.Sv.PDesign.instantiateHDAlias2 3 then
    return true
  match fuel with
  | 0 => return false
  | fuel + 1 =>
    match ← unfoldDefinition? e with
    | some e' => isHD2Family e' fuel
    | none => return false

/-- The refusal of a design that instantiates modules, by a tactic that does not read one (`sv_structure` and
`sv_equations` read a design whose instances are all at module level through its flat twin, `CombHier.lean`; the
`always_comb` forms and `sv_interface` do not yet). -/
def hierarchyRefusal (tac : String) : String :=
  s!"{tac}: this design instantiates modules, and `{tac}` does not read module instances yet (`sv_structure` and " ++
  "`sv_equations` read a design whose instances are all at module level through its flat twin, `CombHier.lean`). " ++
  "The loader, the scorer and the post-synthesis check accept such a design. The stage can be proved by hand " ++
  "(`Examples/system-verilog/ripple_fa` is a worked by-hand proof of a hierarchical adder)"

/-! ### The exact 32-bit `int` reading of the parameters at a symbolic point (`hag`)

The instantiation binds an `int` parameter at `canonInt 32 true v` and an `int` localparam at its width-exact value
(`PDesign.paramEnv2`, `int32 := true`), while the summary's valuation `s.val args` is the unbounded integer. At
concrete arguments the two agree by `rfl`; at a symbolic one they agree where every value is in the signed 32-bit
range, which the tactics show from the hypotheses in context (`closeHag`). -/

theorem canonInt32_of_bounds {v : Int} (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) :
    canonInt 32 true v = v :=
  canonInt32_of_range ⟨h1, h2⟩

/-- `Int.emod` as the `%` that `omega` reads (the instantiation's conversion of a constant to a width, `convertConst`, takes
the operand modulo `2 ^ w` with `Int.emod`: `$clog2 (N)` reads `N` at its 32-bit type). -/
theorem emod_eq_hmod (a b : Int) : Int.emod a b = a % b := rfl

/-! The 32-bit `int` value depends only on the low 32 bits (`canonInt 32 true v` is `v` modulo `2^32`, read as a
two's-complement number), so a wrapped operand of `+`, `-`, `*` or unary `-` (IEEE 1800-2023 §11.4.3: the low bits of a
sum, difference or product depend only on the low bits of the operands) may be unwrapped under the wrap of the result.
The tactics use these to bring the instantiation's value of a localparam, wrapped at every node (`evalIntExact`), to one
wrap around the summary's tree, which the range premises then remove: `(1 << (E - 1)) - 1` at `E = 32` wraps `2^31` to
`-2^31`, and `-2^31 - 1` back to `2^31 - 1`, the summary's value. -/

theorem canonInt32_congr {a b : Int} (h : a % 4294967296 = b % 4294967296) :
    canonInt 32 true a = canonInt 32 true b := by
  have h' : a.emod ((2 : Int) ^ 32) = b.emod ((2 : Int) ^ 32) := h
  simp only [canonInt, h']

theorem canonInt32_emod (a : Int) : canonInt 32 true a % 4294967296 = a % 4294967296 := by
  unfold canonInt
  simp only [Int.reducePow, Nat.reduceSub, Bool.true_and, decide_true, emod_eq_hmod]
  split <;> omega

theorem canonInt32_add_l (a b : Int) : canonInt 32 true (canonInt 32 true a + b) = canonInt 32 true (a + b) :=
  canonInt32_congr (by have := canonInt32_emod a; omega)
theorem canonInt32_add_r (a b : Int) : canonInt 32 true (a + canonInt 32 true b) = canonInt 32 true (a + b) :=
  canonInt32_congr (by have := canonInt32_emod b; omega)
theorem canonInt32_sub_l (a b : Int) : canonInt 32 true (canonInt 32 true a - b) = canonInt 32 true (a - b) :=
  canonInt32_congr (by have := canonInt32_emod a; omega)
theorem canonInt32_sub_r (a b : Int) : canonInt 32 true (a - canonInt 32 true b) = canonInt 32 true (a - b) :=
  canonInt32_congr (by have := canonInt32_emod b; omega)
theorem canonInt32_mul_l (a b : Int) : canonInt 32 true (canonInt 32 true a * b) = canonInt 32 true (a * b) :=
  canonInt32_congr (by rw [Int.mul_emod, canonInt32_emod a, ← Int.mul_emod])
theorem canonInt32_mul_r (a b : Int) : canonInt 32 true (a * canonInt 32 true b) = canonInt 32 true (a * b) :=
  canonInt32_congr (by rw [Int.mul_emod, canonInt32_emod b, ← Int.mul_emod])
theorem canonInt32_neg (a : Int) : canonInt 32 true (-canonInt 32 true a) = canonInt 32 true (-a) :=
  canonInt32_congr (by have := canonInt32_emod a; omega)
theorem canonInt32_idem (a : Int) : canonInt 32 true (canonInt 32 true a) = canonInt 32 true a :=
  canonInt32_congr (canonInt32_emod a)


/-! The facts about `2 ^ t` (a shift of a localparam, `CE.shl`/`shr`/`ashr`) that the tactics hand to `omega`, which reads
`2 ^ t` and `x / 2 ^ t` as atoms: a bound of the exponent gives a bound of the power (`addPowFacts`), and a division by a
power keeps the sign of the dividend and does not grow it. -/

theorem two_pow_le_lit {t c : Nat} (m : Int) (h : t ≤ c) (hm : (2 : Int) ^ c = m) : (2 : Int) ^ t ≤ m := by
  subst hm
  have h1 := Nat.pow_le_pow_right (n := 2) (by decide) h
  have e1 : ((2 ^ t : Nat) : Int) = (2 : Int) ^ t := by simp
  have e2 : ((2 ^ c : Nat) : Int) = (2 : Int) ^ c := by simp
  rw [← e1, ← e2]
  exact Int.ofNat_le.mpr h1

theorem lit_le_two_pow {t c : Nat} (m : Int) (h : c ≤ t) (hm : (2 : Int) ^ c = m) : m ≤ (2 : Int) ^ t := by
  subst hm
  have h1 := Nat.pow_le_pow_right (n := 2) (by decide) h
  have e1 : ((2 ^ t : Nat) : Int) = (2 : Int) ^ t := by simp
  have e2 : ((2 ^ c : Nat) : Int) = (2 : Int) ^ c := by simp
  rw [← e1, ← e2]
  exact Int.ofNat_le.mpr h1

theorem ediv_two_pow_nonneg {x : Int} (t : Nat) (h : 0 ≤ x) : 0 ≤ x / 2 ^ t ∧ x / 2 ^ t ≤ x := by
  have hp : (0 : Int) < 2 ^ t := Int.pow_pos (by decide)
  exact ⟨Int.ediv_nonneg h (by omega), Int.ediv_le_self _ h⟩

theorem ediv_two_pow_neg {x : Int} (t : Nat) (h : x < 0) : x ≤ x / 2 ^ t ∧ x / 2 ^ t < 0 := by
  have hp : (1 : Int) ≤ 2 ^ t := by
    have h1 := Nat.one_le_two_pow (n := t)
    have e1 : ((2 ^ t : Nat) : Int) = (2 : Int) ^ t := by simp
    rw [← e1]
    omega
  constructor
  · rw [Int.le_ediv_iff_mul_le (by omega)]
    have h2 : x * 2 ^ t ≤ x * 1 := Int.mul_le_mul_of_nonpos_left (by omega) hp
    omega
  · exact Int.ediv_neg_of_neg_of_pos h (by omega)

/-- … and, whatever the sign of the dividend, it lies between the dividend and zero. -/
theorem ediv_two_pow_between (x : Int) (t : Nat) : min x 0 ≤ x / 2 ^ t ∧ x / 2 ^ t ≤ max x 0 := by
  by_cases h : 0 ≤ x
  · have := ediv_two_pow_nonneg t h
    omega
  · have := ediv_two_pow_neg t (show x < 0 by omega)
    omega

/-- The instantiation's `>>>` of an `int` (`Int.fdiv` by a power of two) is the floor division `/`. -/
theorem fdiv_two_pow (a : Int) (t : Nat) : a.fdiv (2 ^ t) = a / 2 ^ t := by
  rw [Int.fdiv_eq_ediv]
  have h : (0 : Int) ≤ 2 ^ t := by
    have : (0 : Int) < 2 ^ t := Int.pow_pos (by decide)
    omega
  simp [h]

/-- … and by any non-negative divisor (a literal power, once the tactics' `simp` has computed it). -/
theorem fdiv_of_nonneg (a : Int) {b : Int} (h : 0 ≤ b) : a.fdiv b = a / b := by
  rw [Int.fdiv_eq_ediv]
  simp [h]

/-- A division by `2 ^ t` is no larger than the division by a smaller power `m = 2 ^ c` (`c ≤ t`) of a non-negative
dividend: what puts a right shift by at least one bit of a 32-bit pattern (below `2^32`) in the signed range. -/
theorem ediv_two_pow_le_lit {x : Int} {t c : Nat} (m : Int) (hx : 0 ≤ x) (h : c ≤ t) (hm : (2 : Int) ^ c = m) :
    x / 2 ^ t ≤ x / m := by
  subst hm
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  have e1 : (2 : Int) ^ t = ((2 ^ t : Nat) : Int) := by simp
  have e2 : (2 : Int) ^ c = ((2 ^ c : Nat) : Int) := by simp
  rw [e1, e2, ← Int.natCast_ediv, ← Int.natCast_ediv]
  exact Int.ofNat_le.mpr (Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) h) (Nat.two_pow_pos c))

/-- The 32-bit range of a wrapped value. -/
theorem canonInt32_bounds (x : Int) : -2147483648 ≤ canonInt 32 true x ∧ canonInt 32 true x < 2147483648 :=
  Loop2.int32_inInt32 x

/-! **`>>` reads the 32-bit pattern** (IEEE 1800-2023 §11.4.10: the vacated bits of the logical shift are zeros). The
instantiation computes the pattern of the 32-bit value `a` of its left operand as `if a < 0 then a + 2^32 else a`
(`evalIntExactRec`), the summary as `a % 2^32` (`CE.eval`): the same number, for a value in the signed range
(`shr_pattern_of_bounds`, its hypotheses `omega`'s) and for every wrapped value (`shr_pattern_canon`). The instance is a
variable of both, so they rewrite the `if` whatever instance the evaluation left in it. -/

theorem shr_pattern_of_bounds {a : Int} [Decidable (a < 0)] (h1 : -2147483648 ≤ a) (h2 : a < 2147483648) :
    (if a < 0 then a + 4294967296 else a) = a % 4294967296 := by
  split <;> omega

theorem shr_pattern_canon (x : Int) [Decidable (canonInt 32 true x < 0)] :
    (if canonInt 32 true x < 0 then canonInt 32 true x + 4294967296 else canonInt 32 true x) = x % 4294967296 := by
  have h1 := canonInt32_emod x
  have h2 := canonInt32_bounds x
  split <;> omega

/-- `hag` one name at a time (the head of the parameter list). -/
theorem hag_cons {f g : String → Option Int} {n : String} {ns : List String}
    (h : f n = g n) (t : ns.map f = ns.map g) : (n :: ns).map f = (n :: ns).map g := by
  rw [List.map_cons, List.map_cons, h, t]

/-- `$clog2` of a positive value is below it (`clog2 1 = 0`, and `clog2 n = log2 (n - 1) + 1 < n`): the fact that puts
`$clog2(N) + 1` in the 32-bit range wherever `N` is. The tactics hand it to `omega` with `clog2_le` for every `clog2`
of a range goal (`addClog2Facts`). -/
theorem clog2_zero_or_lt (n : Nat) : n = 0 ∨ LeanModels.Sv.clog2 n < n := by
  unfold LeanModels.Sv.clog2
  by_cases h : n ≤ 1
  · simp only [h, ↓reduceIte]; omega
  · simp only [h, ↓reduceIte]
    right
    have h2 : n - 1 ≠ 0 := by omega
    have := (Nat.log2_lt h2).2 (Nat.lt_two_pow_self (n := n - 1))
    omega

/-- `$clog2 n ≤ c` wherever `n ≤ 2 ^ c` (the ceiling logarithm is the least such `c`): a NUMERIC bound of a `$clog2`
atom, which `addClog2Facts` states for the least `c` that `omega` shows, so that a power `2 ** L` of a `$clog2` localparam
`L` gets its own bound (`addPowFacts`). -/
theorem clog2_le_of_le_two_pow {n c : Nat} (h : n ≤ 2 ^ c) : LeanModels.Sv.clog2 n ≤ c := by
  unfold LeanModels.Sv.clog2
  by_cases h1 : n ≤ 1
  · simp only [h1, ↓reduceIte]; omega
  · simp only [h1, ↓reduceIte]
    have h2 : n - 1 ≠ 0 := by omega
    have : (n - 1).log2 < c := (Nat.log2_lt h2).2 (by omega)
    omega

/-- The power of a literal base `b ≥ 1` (`b ** t`, `CE.pow`) is monotone in the exponent: a bound of the exponent gives
a bound of the power (`addPowFacts`, for a base other than 2; `two_pow_le_lit` is the base-2 instance). -/
theorem lit_pow_le_lit {b : Int} (hb : 1 ≤ b) {t c : Nat} (m : Int) (h : t ≤ c) (hm : b ^ c = m) : b ^ t ≤ m := by
  subst hm
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : Int) ≤ b by omega)
  have h1 := Nat.pow_le_pow_right (n := n) (by omega) h
  have e1 : ((n ^ t : Nat) : Int) = (n : Int) ^ t := by simp
  have e2 : ((n ^ c : Nat) : Int) = (n : Int) ^ c := by simp
  rw [← e1, ← e2]
  exact Int.ofNat_le.mpr h1

theorem lit_le_lit_pow {b : Int} (hb : 1 ≤ b) {t c : Nat} (m : Int) (h : c ≤ t) (hm : b ^ c = m) : m ≤ b ^ t := by
  subst hm
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : Int) ≤ b by omega)
  have h1 := Nat.pow_le_pow_right (n := n) (by omega) h
  have e1 : ((n ^ t : Nat) : Int) = (n : Int) ^ t := by simp
  have e2 : ((n ^ c : Nat) : Int) = (n : Int) ^ c := by simp
  rw [← e1, ← e2]
  exact Int.ofNat_le.mpr h1

/-- The 1-bit unsigned reading of a value (`convertConst 1 1 false`, a comparison's result): its parity. -/
theorem canonInt_one_false (v : Int) : canonInt 1 false v = v % 2 := by
  unfold canonInt
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Int.reducePow]
  rfl

/-- **A decision the parameter stage cannot settle, lifted into the value** (`closeParamEnv`): an evaluation step `r` of an
`Except` type that is stuck on the instance of `p` (the condition of a `?:` over a symbolic parameter, IEEE 1800-2023
§11.4.11) returns `x` where `p` holds and `y` where it does not, so it is `.ok (if p then x else y)`. Both cases are
evaluated (the instance decided either way), so the `if` is the instantiation's own value, not a reading of it. -/
theorem eq_ok_ite_of_cases {ε α : Type} {r : Except ε α} (p : Prop) [Decidable p] {x y : α}
    (h1 : p → r = .ok x) (h2 : ¬ p → r = .ok y) : r = .ok (if p then x else y) := by
  by_cases h : p
  · rw [ite_eq_left h]; exact h1 h
  · rw [ite_eq_right h]; exact h2 h

/-- (Defined after every lemma it names: a quoted name that does not resolve where the quotation is elaborated is
kept hygienic and never resolves, and the `try` around `simp` would hide that.)
**A bound of a wrapped value** (`-2147483648 ≤ x`, `x < 2147483648`) from the hypotheses in context: the wrapped values
INSIDE `x` first (`canonInt32_of_bounds`, each discharged by `omega`: the instantiation wraps every literal, constant read and
intermediate result of an `int` expression, IEEE 1800-2023 §11.4, §11.6.1, §11.8.1), `Int.tdiv`/`Int.tmod` of a
non-negative numerator as `/`/`%`, `Int.emod` as `%`, the literal powers and shift factors computed, then `omega`. -/
def int32Bound : Lean.Elab.Tactic.TacticM Unit := do
  Lean.Elab.Tactic.evalTactic (← `(tactic| ((try simp (disch := omega) only [Int.ofNat_eq_natCast, Int.toNat_natCast,
      Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg, Int.reduceToNat, Int.reduceMod, Int.reducePow,
      Int.reduceMul, LeanModels.Sv.CombView.fdiv_two_pow, LeanModels.Sv.CombView.fdiv_of_nonneg,
      LeanModels.Sv.CombView.canonInt32_add_l, LeanModels.Sv.CombView.canonInt32_add_r,
      LeanModels.Sv.CombView.canonInt32_sub_l, LeanModels.Sv.CombView.canonInt32_sub_r, LeanModels.Sv.CombView.canonInt32_mul_l,
      LeanModels.Sv.CombView.canonInt32_mul_r, LeanModels.Sv.CombView.canonInt32_neg, LeanModels.Sv.CombView.canonInt32_idem,
      LeanModels.Sv.CombView.emod_eq_hmod, LeanModels.Sv.CombView.shr_pattern_of_bounds,
      LeanModels.Sv.CombView.shr_pattern_canon, LeanModels.Sv.CombView.canonInt32_of_bounds]) <;> omega)))

/-- **A decision of the parameter stage** (`p` or `¬ p`, the proposition of a stuck `Decidable` instance: the sign test of
`$clog2`'s argument or of a shift amount) from the hypotheses in context: `int32Bound` with the conversion of a constant to
its type unfolded (`convertConst`, the form the instance's proposition keeps), its widths computed. -/
def int32Decide : Lean.Elab.Tactic.TacticM Unit := do
  Lean.Elab.Tactic.evalTactic (← `(tactic| ((try simp (disch := omega) only [LeanModels.Sv.convertConst,
      Nat.max_self, Bool.and_self, ↓reduceIte, Int.ofNat_eq_natCast, Int.toNat_natCast,
      Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg, Int.reduceToNat, Int.reduceMod, Int.reducePow,
      Int.reduceMul, LeanModels.Sv.CombView.fdiv_two_pow, LeanModels.Sv.CombView.fdiv_of_nonneg,
      LeanModels.Sv.CombView.canonInt32_add_l, LeanModels.Sv.CombView.canonInt32_add_r,
      LeanModels.Sv.CombView.canonInt32_sub_l, LeanModels.Sv.CombView.canonInt32_sub_r, LeanModels.Sv.CombView.canonInt32_mul_l,
      LeanModels.Sv.CombView.canonInt32_mul_r, LeanModels.Sv.CombView.canonInt32_neg, LeanModels.Sv.CombView.canonInt32_idem,
      LeanModels.Sv.CombView.emod_eq_hmod, LeanModels.Sv.CombView.shr_pattern_of_bounds,
      LeanModels.Sv.CombView.shr_pattern_canon, LeanModels.Sv.CombView.canonInt32_of_bounds]) <;> omega)))

/-- **`int32Decide`, the hypotheses normalized too** (the fallback of the parameter stage's decisions): the same rewrites,
twice, at every hypothesis and the goal, then `omega`. A fact the tactics put in context about a `$clog2` atom
(`clog2_le`, `clog2_zero_or_lt`, `clog2_le_of_le_two_pow`) names the argument in the form the instantiation computes
(`convertConst` of every operand); a decision on the VALUE of `$clog2` (the sign test of the exponent of `2 ** L`, of a
shift by `L`) names it so too, and the rewrites bring both to the same atom (`clog2 (↑N + 1).toNat`). The second pass
sees the first pass's hypotheses (a bound of the goal's wrapped value needs the normalized fact). -/
def int32DecideAll : Lean.Elab.Tactic.TacticM Unit := do
  for _ in [0:2] do
    if (← Lean.Elab.Tactic.getGoals).isEmpty then return
    Lean.Elab.Tactic.evalTactic (← `(tactic| (try simp (disch := omega) only [LeanModels.Sv.convertConst,
      Nat.max_self, Bool.and_self, ↓reduceIte, Int.ofNat_eq_natCast, Int.toNat_natCast,
      Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg, Int.reduceToNat, Int.reduceMod, Int.reducePow,
      Int.reduceMul, LeanModels.Sv.CombView.fdiv_two_pow, LeanModels.Sv.CombView.fdiv_of_nonneg,
      LeanModels.Sv.CombView.canonInt32_add_l, LeanModels.Sv.CombView.canonInt32_add_r,
      LeanModels.Sv.CombView.canonInt32_sub_l, LeanModels.Sv.CombView.canonInt32_sub_r, LeanModels.Sv.CombView.canonInt32_mul_l,
      LeanModels.Sv.CombView.canonInt32_mul_r, LeanModels.Sv.CombView.canonInt32_neg, LeanModels.Sv.CombView.canonInt32_idem,
      LeanModels.Sv.CombView.emod_eq_hmod, LeanModels.Sv.CombView.shr_pattern_of_bounds,
      LeanModels.Sv.CombView.shr_pattern_canon, LeanModels.Sv.CombView.canonInt32_of_bounds] at *)))
  unless (← Lean.Elab.Tactic.getGoals).isEmpty do
    Lean.Elab.Tactic.evalTactic (← `(tactic| omega))

end LeanModels.Sv.CombView

/-- The free variables of an expression. -/
private partial def fvarsOf (e : Expr) : Array FVarId := Id.run do
  let mut acc : Array FVarId := #[]
  repeat
    match e.find? (fun x => x.isFVar && !acc.contains x.fvarId!) with
    | some x => acc := acc.push x.fvarId!
    | none => break
  return acc

/-- Lower bounds `c ≤ N` / `c < N` of the Nat variables of the arguments, from the context. -/
private def lowerBounds (fvs : Array FVarId) : MetaM Nat := do
  let mut lb := 1
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let check (small big : Expr) (strict : Bool) : MetaM Nat := do
      if big.isFVar && fvs.contains big.fvarId! then
        match ← Meta.evalNat small with
        | some c => return (if strict then c + 1 else c)
        | none => return 0
      else return 0
    if t.isAppOfArity ``LE.le 4 then
      lb := max lb (← check t.getAppArgs[2]! t.getAppArgs[3]! false)
    else if t.isAppOfArity ``LT.lt 4 then
      lb := max lb (← check t.getAppArgs[2]! t.getAppArgs[3]! true)
    else if t.isAppOfArity ``GE.ge 4 then
      lb := max lb (← check t.getAppArgs[3]! t.getAppArgs[2]! false)
    else if t.isAppOfArity ``GT.gt 4 then
      lb := max lb (← check t.getAppArgs[3]! t.getAppArgs[2]! true)
  return lb

/-- Name of a constant the summary was read from, to unfold it in the normalization. -/
private def headConst? (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ => some n
  | _ => none

-- COPY NOTE (literal simp list, kept in step by hand): `sv_norm_core` is one of six copies of the same
-- vocabulary: `sv_norm_core` (CombViewTactic.lean), `sv_eq_norm_at` and `sv_eq_norm` (CombEqTactic.lean),
-- `svL_norm_core`, `svL_eq_norm_at` and `svL_eq_norm` (CombProcTactic.lean). The L copies are the plain ones plus
-- the names of the procedural sites (skeletons, `NoSelfRead`, `EqsL`, ...); the `_at` copies act at a hypothesis,
-- the others at the goal. A lemma added to one list belongs in its siblings unless the difference is intended and
-- stated here. The multi-window copies `svL_eq_norm_multi_at` and `svL_eq_norm_multi` (CombProcTactic.lean) are
-- `svL_eq_norm_at` and `svL_eq_norm` plus the skeleton vocabulary; they name this note and each other.
set_option maxRecDepth 4096 in
/-- The normalization of the obligation `Prop`s: unfold the summary functions, evaluate the
affine forms, name the windows. -/
macro "sv_norm_core" : tactic =>
  `(tactic| (simp (config := { maxSteps := 4000000 }) only [LeanModels.Sv.CombView.Summary.AutoObl, LeanModels.Sv.CombView.Summary.lsites, LeanModels.Sv.CombView.Aff.add,
      LeanModels.Sv.CombView.Aff.var, LeanModels.Sv.CombView.Aff.const, List.append_nil,
      Int.zero_add, LeanModels.Sv.CombView.Aff.sub, LeanModels.Sv.CombView.Aff.neg,
      LeanModels.Sv.CombView.Aff.negTerms, LeanModels.Sv.CombView.Aff.negQs, Int.reduceNeg, Int.reduceAdd,
      List.nil_append, Nat.zero_add, Nat.reduceAdd,
      LeanModels.Sv.CombView.Aff.scale, LeanModels.Sv.CombView.Aff.scaleTerms, LeanModels.Sv.CombView.Aff.scaleQs, Int.mul_one,
      Int.mul_zero, List.map_cons, List.map_nil,
      List.cons_append, List.flatMap_cons, LeanModels.Sv.CombView.TFam.lsites,
      LeanModels.Sv.CombView.TFam.itemLs, LeanModels.Sv.CombView.Hdr.name, Option.getD_some,
      List.flatMap_nil, List.mem_cons, List.not_mem_nil,
      or_false, Int.ofNat_eq_natCast, List.zip_cons_cons,
      List.zip_nil_right, LeanModels.Sv.CombView.Summary.InR, LeanModels.Sv.CombView.Aff.eval,
      LeanModels.Sv.CombView.Summary.dm, LeanModels.Sv.CombView.Summary.find, LeanModels.Sv.CombView.findDecl,
      forall_eq_or_imp, LeanModels.Sv.CombView.Loops.all, forall_eq,
      LeanModels.Sv.CombView.Aff.evalTerms, LeanModels.Sv.CombView.Aff.evalQs, Int.add_zero, Std.le_refl,
      String.reduceBEq, Bool.false_eq_true, not_false_eq_true,
      List.find?_cons_of_neg, BEq.rfl, List.find?_cons_of_pos,
      List.length_cons, List.length_nil, Nat.zero_lt_succ,
      getElem?_pos, List.getElem_cons_zero, LeanModels.Sv.CombView.σL,
      List.lookup_cons_self, Int.one_mul, true_and,
      false_implies, implies_true, Int.zero_le_ofNat,
      Nat.lt_add_one, List.getElem_cons_succ, and_true,
      LeanModels.Sv.CombView.Hdr.Rng, LeanModels.Sv.CombView.bindσ, String.reduceEq,
      ↓reduceIte, and_imp, Int.add_le_add_iff_right,
      Int.natCast_nonneg, and_self, LeanModels.Sv.CombView.Summary.DimNum,
      LeanModels.Sv.CombView.Summary.hdrPaths, Option.some.injEq, List.filterMap_cons_some,
      List.filterMap_nil, List.filterMap_cons_none, Int.natAbs_natCast,
      List.sum_cons, List.sum_nil, Nat.add_zero,
      Int.toNat_le, Int.natCast_add, Int.cast_ofNat_Int,
      Int.sub_zero, and_self_right, and_self_left,
      LeanModels.Sv.CombView.Summary.InRangeObl, LeanModels.Sv.CombView.Summary.InWin, LeanModels.Sv.CombView.Summary.dw,
      LeanModels.Sv.CombView.DeclT.width, Option.map_some, LeanModels.Sv.CombView.dimsW,
      Nat.mul_one, LeanModels.Sv.CombView.Summary.DisjObl, List.pairwise_cons,
      LeanModels.Sv.CombView.Summary.DisjOne, LeanModels.Sv.CombView.LSite.id, ne_eq,
      LeanModels.Sv.CombView.Acc.win, LeanModels.Sv.CombView.Acc.lo, LeanModels.Sv.CombView.Acc.wid,
      Int.toNat_natCast_add_one, LeanModels.Sv.CombView.SiteId.plain.injEq, Nat.zero_ne_one,
      LeanModels.Sv.Win.overlaps_eq_false, or_self, true_or,
      imp_self, reduceCtorEq, Int.toNat_natCast,
      not_true_eq_false, false_or, forall_const,
      Nat.reduceEqDiff, LeanModels.Sv.CombView.SiteId.fam.injEq, List.cons.injEq,
      List.cons_ne_self, and_false, false_and,
      List.ne_cons_self, Nat.succ_ne_self, List.Pairwise.nil,
      not_and, LeanModels.Sv.CombView.Summary.LexObl, LeanModels.Sv.CombView.Summary.RankObl',
      LeanModels.Sv.CombView.Summary.writersOf, LeanModels.Sv.CombView.Acc.name, List.mem_filter,
      beq_iff_eq, LeanModels.Sv.ReadWin.overlaps, LeanModels.Sv.CombView.Acc.rd,
      LeanModels.Sv.CombView.KLt, Nat.lt_irrefl, imp_false,
      Bool.not_eq_true, LeanModels.Sv.Win.overlaps_eq_true, Nat.lt_add_right_iff_pos,
      Nat.lt_add_left_iff_pos, Int.sub_add_cancel, Int.toNat_lt',
      Int.ofNat_toNat, LeanModels.Sv.CombView.Summary.RankObl, LeanModels.Sv.CombView.rippleRank,
      LeanModels.Sv.CombView.Summary.val, LeanModels.Sv.CombView.lpEnv, List.lookup_cons, List.lookup_nil,
      LeanModels.Sv.CombView.CE.eval]))

/-- `sv_norm [f, g]`: the normalization, with the player's own rank/key definitions `f`, `g`
unfolded. -/
syntax "sv_norm" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

/-- The truncating `/` and `%` of a localparam's definition (`Int.tdiv`, `Int.tmod`: C semantics, what
the elaborated design computes) as the floor `/` and `%` that `omega` understands, where the
numerator is provably non-negative from the hypotheses in context (`hN : 1 ≤ N`). A numerator that
may be negative stays as `Int.tdiv`/`Int.tmod` in the goal (they really differ there). A no-op for a
design without localparams. -/
macro "sv_lp_norm" : tactic =>
  `(tactic| (try simp (disch := omega) only [Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg]))

/-- … on a hypothesis. -/
macro "sv_lp_norm_at" h:ident : tactic =>
  `(tactic| (try simp (disch := omega) only [Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg] at $h:ident))

macro_rules
  | `(tactic| sv_norm) => `(tactic| (sv_norm_core; sv_lp_norm; try sv_simp))
  | `(tactic| sv_norm [$ids,*]) =>
      `(tactic| (sv_norm_core; sv_lp_norm; (try simp (config := { maxSteps := 4000000 }) only [$ids,*]); try sv_simp))

set_option maxRecDepth 4096 in
/-- **Row-major bookkeeping, explicitly.** The 2-D windows of a packed array `x[R-1:0][W-1:0]` are
flat offsets `rmN W r c = r * W + c`, and every obligation about two of them (disjointness of two
cells, a cell inside a row or a part of a row, the overlap of a read with a write) is a comparison of
two such offsets. `sv_rowmajor` rewrites those comparisons into lexicographic comparisons of
`(row, column)` with the library lemmas `rmN_add_col` (a window's end is the offset of its end
column), `rmN_lt_iff` and `rmN_le_iff` (row-major order IS lexicographic order, for columns inside
the row); their side conditions (indices nonnegative, columns inside the row) are discharged by
`omega` from the loop bounds in the context. What it leaves is linear: finish with `omega`. It is
NOT part of `sv_structure`: the player calls it, on goals that mention `rmN`. -/
macro "sv_rowmajor" : tactic =>
  `(tactic| (try simp (disch := omega) only [LeanModels.Sv.CombView.rmN_add_col,
      LeanModels.Sv.CombView.rmN_lt_iff, LeanModels.Sv.CombView.rmN_le_iff] at *))

/-- **Close a decidable structural fact without an auxiliary lemma** (WP-P). `decide +kernel` turns the
fact into an auxiliary theorem and adds it to the environment synchronously, and in the asynchronous
elaboration of a file that addition waits for the kernel check of EVERY earlier declaration: the
`hok`/`hfrag` goals of a late theorem (`sv_interface`, `solution`) then sat idle for as long as the
heaviest earlier theorem took to elaborate (measured: 31 s of a 34 s `mul_wallace` interface theorem,
112 s of a 118 s `mul_tree` one, for a step that costs 0.3 s). Here the proposition is evaluated NATIVELY at
tactic time (`evalExpr` on `Decidable.decide`, milliseconds, with the tactic's own error when it is false),
and the goal is assigned `of_decide_eq_true _ _ (Eq.refl true)` directly: no environment change, so no
wait; the kernel evaluates the decision once, when it checks the enclosing theorem (the same work the
auxiliary lemma did, in the theorem's own asynchronous check). -/
unsafe def closeByDecide (g : MVarId) (what : String) : MetaM Unit := do
  let p ← instantiateMVars (← g.getType)
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let d := mkApp2 (mkConst ``Decidable.decide) p inst
  let b ← evalExpr Bool (mkConst ``Bool) d
  unless b do throwError "{what}"
  g.assign (mkApp3 (mkConst ``of_decide_eq_true) p inst (← mkEqRefl (mkConst ``Bool.true)))

/-- **Deep recursion for the tactics' own work** (WP-P3b). A netlist of a hundred or more sites makes the
`simp` normalizations of the obligations recurse once per site (a right-nested conjunction of one fact
per site), and Lean's default `maxRecDepth` (512) stops them with `maximum recursion depth has been
reached` long before the work is large: the player had to write `set_option maxRecDepth 100000 in`
before the theorem. The tactics run their own steps with `maxRecDepth` raised to 100000 (the value
the references used), scoped to the tactic call through `Core.Context`: nothing in the player's file
changes, and a limit the player set higher is kept. -/
def withDeepRec {α : Type} (x : TacticM α) : TacticM α :=
  withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) x


/-- **Decide the obligation of a flat netlist** (WP-P3b). `g` is an obligation goal (`s.DisjObl σ`,
`s.CoverObl σ`, …) of the summary `s`; `lem` is the `…_of_plain` lemma that reduces it to a closed, decidable
statement about the site list (`CombViewPlain.lean`, `CombEqPlain.lean`). When every site of `s` is plain and
the goal mentions no free variable or metavariable (no parameter), the lemma is applied and its premises are
closed with `closeByDecide`; the result is `true` and `g` is closed. Anything else, including a premise that is
false, restores the state and returns `false`: the caller takes the normalization route, unchanged. -/
unsafe def tryClosePlain (s : LeanModels.Sv.CombView.Summary) (g : MVarId) (lem : Name) (what : String) :
    TacticM Bool := do
  unless s.lsites.all fun ls => ls.hdrs.isEmpty do return false
  let ty ← instantiateMVars (← g.getType)
  if ty.hasFVar || ty.hasExprMVar then return false
  let saved ← saveState
  try
    let gs ← g.apply (← mkConstWithFreshMVarLevels lem)
    for g' in gs do closeByDecide g' what
    setGoals []
    return true
  catch _ =>
    saved.restore
    return false

/-- The elements of a list expression, by weak head normalization of its spine (WP-LIN). -/
partial def listElemExprs (e : Expr) : MetaM (Array Expr) := do
  let mut acc : Array Expr := #[]
  let mut cur ← whnf e
  repeat
    match cur.getAppFnArgs with
    | (``List.cons, #[_, x, xs]) =>
        acc := acc.push (← instantiateMVars x).headBeta
        cur ← whnf xs
    | (``List.nil, _) => break
    | _ => throwError "sv_comb: cannot read a list expression element by element"
  return acc

namespace LeanModels.Sv.CombView

/-- **The alias guard, out of the way** (ls-sv 7c9b7ac59): the equation `D = pd.instantiateGD2 args` for the design
`D` of the goal, which unfolds to the guarded family `pd.instantiateGDAlias2 args`. The static check
`PDesign.aliasInert pd` (`CombAliasInert.lean`) is decided natively and by the kernel (`closeByDecide`); a design with
an `always_comb` beside a continuous assignment fails it, and the tactic `tac` refuses the design, saying why. -/
unsafe def aliasInertEq (tac : String) (D pd args : Lean.Expr) : MetaM Lean.Expr := do
  let hqTy ← mkEq (mkApp (mkConst ``LeanModels.Sv.PDesign.aliasInert) pd) (mkConst ``Bool.true)
  let hq ← mkFreshExprMVar hqTy
  try closeByDecide hq.mvarId! "not inert"
  catch _ =>
    throwError "{tac}: the design family applies the `always_comb` alias guard (`X.sem N` is `PDesign.instantiateGDAlias2`, `CombAlias2.lean`), and the comb theorems are stated for the unguarded family `PDesign.instantiateGD2`. Without a lowering in hand the tactics show that the guard keeps every process only for a design with no `always_comb` or with no continuous `assign` (`PDesign.aliasInert`, `CombAliasInert.lean`); this design has both (the `always_comb` form of `sv_structure` shows the guard inert from the summary's names, `Summary.aliasOk`, `CombProcAlias.lean`; where `hl : (X.sem N).lowerComb = some d'` is in context, `sv_interface` and `sv_equations` read the guard off it)"
  let D' := mkApp2 (mkConst ``LeanModels.Sv.PDesign.instantiateGD2) pd args
  let pf := mkApp3 (mkConst ``LeanModels.Sv.PDesign.instantiateGDAlias2_of_aliasInert) pd
    (← instantiateMVars hq) args
  mkExpectedTypeHint pf (← mkEq D D')

/-- The equation `D = pd.instantiateGD2 args` from `hl : D.lowerComb = some d'`, for `D` the guarded family
`pd.instantiateGDAlias2 args`: a guarded design that lowers is its own guard
(`PDesign.instantiateGDAlias2_of_lowerComb`); no static check, every design. -/
def aliasLowerEq (D pd args hl : Lean.Expr) : MetaM Lean.Expr := do
  let some (_, _, rhs) := (← instantiateMVars (← inferType hl)).eq?
    | throwError "sv_comb: internal error: the lowering hypothesis is not an equation"
  unless rhs.isAppOfArity ``Option.some 2 do
    throwError "sv_comb: internal error: the lowering hypothesis is not `… = some d'`"
  let pf := mkAppN (mkConst ``LeanModels.Sv.PDesign.instantiateGDAlias2_of_lowerComb) #[pd, args, rhs.appArg!, hl]
  mkExpectedTypeHint pf (← mkEq D (mkApp2 (mkConst ``LeanModels.Sv.PDesign.instantiateGD2) pd args))

/-- Replace the design `D` by `D'` in the target of `g` along `hA : D = D'` (every occurrence). -/
def rewriteDesign (g : MVarId) (hA : Lean.Expr) : MetaM MVarId := do
  let r ← g.rewrite (← instantiateMVars (← g.getType)) hA
  unless r.mvarIds.isEmpty do throwError "sv_comb: internal error: the design rewrite left goals"
  g.replaceTargetEq r.eNew r.eqProof

/-- A hypothesis `h : T[D]` as a proof of `T[D']`, along `hA : D = D'` (unchanged when `T` does not mention `D`). -/
def transportDesign (h D hA : Lean.Expr) : MetaM Lean.Expr := do
  let T ← instantiateMVars (← inferType h)
  let Tabs ← kabstract T D
  unless Tabs.hasLooseBVars do return h
  let some (_, _, D') := (← instantiateMVars (← inferType hA)).eq?
    | throwError "sv_comb: internal error: the design equation is not an equation"
  let motive := Lean.mkLambda `x .default (← inferType D) Tabs
  let eq ← mkCongrArg motive hA
  mkExpectedTypeHint (← mkEqMP eq h) (Tabs.instantiate1 D')

/-- `2 ^ (b % 2^32).toNat` for the term `b` of a shift amount: the factor of a shift (`CE.eval`). -/
def shPowOf (b : Lean.Expr) : MetaM Lean.Expr := do
  let t ← mkAppM ``Int.toNat #[← mkAppM ``HMod.hMod #[b, toExpr (4294967296 : Int)]]
  mkAppM ``HPow.hPow #[toExpr (2 : Int), t]

/-- The summary's valuation of a localparam definition as a term over the terms `m` of the names before it
(`CE.eval`, operation for operation), so that it is definitionally `s.val args n`. -/
partial def ceTerm (m : List (String × Lean.Expr)) : CE → MetaM Lean.Expr
  | .lit v => pure (toExpr v)
  | .ref n => pure ((m.lookup n).getD (toExpr (0 : Int)))
  | .add a b => do mkAppM ``HAdd.hAdd #[← ceTerm m a, ← ceTerm m b]
  | .sub a b => do mkAppM ``HSub.hSub #[← ceTerm m a, ← ceTerm m b]
  | .mul a b => do mkAppM ``HMul.hMul #[← ceTerm m a, ← ceTerm m b]
  | .divK a k => do mkAppM ``Int.tdiv #[← ceTerm m a, toExpr k]
  | .modK a k => do mkAppM ``Int.tmod #[← ceTerm m a, toExpr k]
  | .clog2 a => do
      let n ← mkAppM ``LeanModels.Sv.clog2 #[← mkAppM ``Int.toNat #[← ceTerm m a]]
      mkAppOptM ``Nat.cast #[mkConst ``Int, none, n]
  | .clog2S a => do
      let n ← mkAppM ``LeanModels.Sv.clog2 #[← mkAppM ``Int.toNat #[← ceTerm m a]]
      let c ← mkAppOptM ``Nat.cast #[mkConst ``Int, none, n]
      pure (mkApp3 (mkConst ``LeanModels.Sv.canonInt) (toExpr (32 : Nat)) (toExpr true) c)
  | .shl a b => do mkAppM ``HMul.hMul #[← ceTerm m a, ← shPowOf (← ceTerm m b)]
  | .shr a b => do
      mkAppM ``HDiv.hDiv #[← mkAppM ``HMod.hMod #[← ceTerm m a, toExpr (4294967296 : Int)], ← shPowOf (← ceTerm m b)]
  | .ashr a b => do
      let w := mkApp3 (mkConst ``LeanModels.Sv.canonInt) (toExpr (32 : Nat)) (toExpr true) (← ceTerm m a)
      mkAppM ``HDiv.hDiv #[w, ← shPowOf (← ceTerm m b)]
  | .pow a b => do mkAppM ``HPow.hPow #[← ceTerm m a, ← mkAppM ``Int.toNat #[← ceTerm m b]]
  | .cmp k a b => do
      let x ← ceTerm m a
      let y ← ceTerm m b
      let one := toExpr (1 : Int)
      let zero := toExpr (0 : Int)
      match k with
      | .lt => mkAppM ``ite #[← mkAppM ``LT.lt #[x, y], one, zero]
      | .le => mkAppM ``ite #[← mkAppM ``LE.le #[x, y], one, zero]
      | .gt => mkAppM ``ite #[← mkAppM ``LT.lt #[y, x], one, zero]
      | .ge => mkAppM ``ite #[← mkAppM ``LE.le #[y, x], one, zero]
      | .eq => mkAppM ``ite #[← mkEq x y, one, zero]
      | .ne => mkAppM ``ite #[← mkEq x y, zero, one]
  | .cond c a b => do
      mkAppM ``ite #[← mkEq (← ceTerm m c) (toExpr (0 : Int)), ← ceTerm m b, ← ceTerm m a]

/-- The arguments `a` of the `clog2 a` subterms of `e` (closed under no binder). -/
partial def clog2Args (e : Lean.Expr) : Array Lean.Expr :=
  match e with
  | .app f a =>
      (if e.isAppOfArity ``LeanModels.Sv.clog2 1 && !a.hasLooseBVars then #[a] else #[]) ++ clog2Args f ++
        clog2Args a
  | .lam _ t b _ | .forallE _ t b _ => clog2Args t ++ clog2Args b
  | .letE _ t v b _ => clog2Args t ++ clog2Args v ++ clog2Args b
  | .mdata _ b | .proj _ _ b => clog2Args b
  | _ => #[]

/-- `a` and the forms the tactics' `simp` sets give it (`Int.ofNat n` as `↑n`, then `(↑n).toNat` as `n`): `omega` reads
`clog2 a` as an atom up to syntax, so a fact is stated for each. -/
def clog2Variants (a : Lean.Expr) : Array Lean.Expr :=
  let cast (x : Lean.Expr) : Lean.Expr :=
    mkApp3 (mkConst ``Nat.cast [Level.zero]) (mkConst ``Int) (mkConst ``instNatCastInt) x
  let a1 := a.replace fun x => if x.isAppOfArity ``Int.ofNat 1 then some (cast x.appArg!) else none
  let a2 := a1.replace fun x =>
    if x.isAppOfArity ``Int.toNat 1 && x.appArg!.isAppOfArity ``Nat.cast 3 then some x.appArg!.appArg! else none
  #[a, a1, a2]

/-- Put `clog2_le a` and `clog2_zero_or_lt a` in the context of the main goal for every `clog2 a` of the terms `es`, for
`omega` (which reads `clog2 a` as an atom). -/
def addClog2Facts (es : Array Lean.Expr) : TacticM Unit := do
  let mut seen : Array Lean.Expr := #[]
  for e in es do
    for a in (clog2Args (← instantiateMVars e)).flatMap clog2Variants do
      if seen.contains a then continue
      seen := seen.push a
      let g ← getMainGoal
      let h1 := mkApp (mkConst ``LeanModels.Sv.CombView.clog2_le) a
      let h2 := mkApp (mkConst ``LeanModels.Sv.CombView.clog2_zero_or_lt) a
      let g ← g.assert `hclog2_le (← inferType h1) h1
      let (_, g) ← g.intro1P
      let g ← g.assert `hclog2_lt (← inferType h2) h2
      let (_, g) ← g.intro1P
      replaceMainGoal [g]

/-- The exponents `t` of the `(2 : Int) ^ t` subterms of `e`, and the pairs `(x, t)` of its `x / 2 ^ t` (closed under no
binder). -/
partial def powArgs (e : Lean.Expr) : Array Lean.Expr × Array (Lean.Expr × Lean.Expr) :=
  let here : Array Lean.Expr × Array (Lean.Expr × Lean.Expr) :=
    if e.isAppOfArity ``HPow.hPow 6 && !e.hasLooseBVars && e.getArg! 0 == mkConst ``Int &&
        e.getArg! 1 == mkConst ``Nat then (#[e.getArg! 5], #[])
    else if e.isAppOfArity ``HDiv.hDiv 6 && !e.hasLooseBVars && e.getArg! 0 == mkConst ``Int &&
        (e.getArg! 5).isAppOfArity ``HPow.hPow 6 then (#[], #[(e.getArg! 4, (e.getArg! 5).getArg! 5)])
    else (#[], #[])
  let sub : Array Lean.Expr × Array (Lean.Expr × Lean.Expr) :=
    match e with
    | .app f a =>
        let (p1, d1) := powArgs f
        let (p2, d2) := powArgs a
        (p1 ++ p2, d1 ++ d2)
    | .mdata _ b | .proj _ _ b => powArgs b
    | _ => (#[], #[])
  (here.1 ++ sub.1, here.2 ++ sub.2)

/-- The pairs `(b, t)` of the `b ^ t` subterms of `e` of type `Int` with a `Nat` exponent (closed under no binder): the
powers whose bounds `addPowFacts` states, of the base `2` (the shifts) or another literal base (`CE.pow`). -/
partial def powBases (e : Lean.Expr) : Array (Lean.Expr × Lean.Expr) :=
  let here : Array (Lean.Expr × Lean.Expr) :=
    if e.isAppOfArity ``HPow.hPow 6 && !e.hasLooseBVars && e.getArg! 0 == mkConst ``Int &&
        e.getArg! 1 == mkConst ``Nat then #[(e.getArg! 4, e.getArg! 5)]
    else #[]
  let sub : Array (Lean.Expr × Lean.Expr) :=
    match e with
    | .app f a => powBases f ++ powBases a
    | .mdata _ b | .proj _ _ b => powBases b
    | _ => #[]
  here ++ sub

/-- A proof of `p` by `omega` in the context of the main goal, if there is one (the goal list is restored). -/
def omegaProves (p : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let st ← saveState
  let gs ← getGoals
  let g ← getMainGoal
  let m ← g.withContext (mkFreshExprSyntheticOpaqueMVar p)
  setGoals [m.mvarId!]
  try
    evalTactic (← `(tactic| omega))
    if (← getGoals).isEmpty then
      -- keep the state: the proof may use auxiliary lemmas `omega` added to the environment
      let pf ← instantiateMVars m
      setGoals gs
      return some pf
    st.restore
    return none
  catch _ =>
    st.restore
    return none

/-- Assert the proof `pf` in the context of the main goal. -/
def assertMain (n : Name) (pf : Lean.Expr) : TacticM Unit := do
  let g ← getMainGoal
  let g ← g.assert n (← inferType pf) pf
  let (_, g) ← g.intro1P
  replaceMainGoal [g]

/-- Assert the proof `mk` builds IN the context of the main goal (a proof by `omegaProves` may use a fact asserted
before it, a hypothesis of that context only). -/
def assertMainM (n : Name) (mk : MetaM Lean.Expr) : TacticM Unit := do
  let pf ← (← getMainGoal).withContext mk
  assertMain n pf

/-- **Put power facts in the context of the main goal** for `omega`, which reads `2 ^ t` and `x / 2 ^ t` as atoms (the
shifts of a localparam, `CE.shl`/`shr`/`ashr`, and the instantiation's own): for every `(2 : Int) ^ t` of the terms `es`,
`2 ^ c ≤ 2 ^ t`, and `2 ^ t ≤ 2 ^ d` (both as literals), for the greatest `c` and the least `d` in `[0, 64]` with
`c ≤ t ≤ d` provable by `omega` from the hypotheses in context; for every `x / 2 ^ t` whose sign `omega` decides, the
quotient has that sign and is no further from zero than `x` (`ediv_two_pow_nonneg`, `ediv_two_pow_neg`; where the sign is
not decided, between `x` and zero, `ediv_two_pow_between`), and, for a
non-negative `x` and `c ≥ 1`, no larger than `x / 2 ^ c` (`ediv_two_pow_le_lit`: a right shift by at least one bit of a
32-bit pattern is in the signed range). Every fact is proved; none is assumed. -/
def addPowFacts (es : Array Lean.Expr) : TacticM Unit := do
  let mut seenP : Array (Lean.Expr × Lean.Expr) := #[]
  let mut seenD : Array (Lean.Expr × Lean.Expr) := #[]
  -- the greatest lower bound found for each exponent of a power of two, with its proof
  let mut lows : Array (Lean.Expr × Nat × Lean.Expr) := #[]
  let le (a b : Lean.Expr) : MetaM Lean.Expr := mkAppM ``LE.le #[a, b]
  let powLit (c : Nat) : MetaM (Lean.Expr × Lean.Expr) := do
    let m : Int := 2 ^ c
    let hm ← mkExpectedTypeHint (← mkEqRefl (toExpr m))
      (← mkEq (← mkAppM ``HPow.hPow #[toExpr (2 : Int), toExpr c]) (toExpr m))
    pure (toExpr m, hm)
  -- `b ^ c` of the literal base `b` (the term as the goal has it, so that the fact names the goal's atom)
  let powLitB (b : Lean.Expr) (k : Int) (c : Nat) : MetaM (Lean.Expr × Lean.Expr) := do
    let m : Int := k ^ c
    let hm ← mkExpectedTypeHint (← mkEqRefl (toExpr m)) (← mkEq (← mkAppM ``HPow.hPow #[b, toExpr c]) (toExpr m))
    pure (toExpr m, hm)
  -- the numeric bound of every `$clog2` atom (`clog2_le_of_le_two_pow`, the least `c ≤ 64` with `a ≤ 2 ^ c` that `omega`
  -- shows): the exponent of a power of a `$clog2` localparam (`2 ** L`, `CE.pow`) is bounded by it
  let mut seenC : Array Lean.Expr := #[]
  for e in es do
    for a in (clog2Args (← instantiateMVars e)).flatMap clog2Variants do
      if seenC.contains a then continue
      seenC := seenC.push a
      let le2 (c : Nat) : MetaM Lean.Expr := mkAppM ``LE.le #[a, toExpr (2 ^ c : Nat)]
      if (← omegaProves (← le2 64)).isSome then
        let mut lo := 0
        let mut hi := 64
        while lo < hi do
          let mid := (lo + hi) / 2
          if (← omegaProves (← le2 mid)).isSome then hi := mid else lo := mid + 1
        if let some h ← omegaProves (← le2 hi) then
          let pf ← (← getMainGoal).withContext do
            let h' ← mkExpectedTypeHint h (← mkAppM ``LE.le #[a, ← mkAppM ``HPow.hPow #[toExpr (2 : Nat), toExpr hi]])
            mkAppOptM ``LeanModels.Sv.CombView.clog2_le_of_le_two_pow #[a, toExpr hi, h']
          assertMain `hclog2_num pf
  for e in es do
    let eI ← instantiateMVars e
    let (_, ds) := powArgs eI
    for (b, t) in powBases eI do
      if seenP.any (fun (b', t') => b' == b && t' == t) then continue
      seenP := seenP.push (b, t)
      -- the base: `2` (the shifts and `2 ** e`) or another literal `k ≥ 1` (`3 ** e`); a base that is no literal gets the
      -- facts of `2 ^ t`, as before the literal bases were read (they name another atom, and claim nothing about it)
      let k := (← getIntValue? b).getD 2
      unless 1 ≤ k do continue
      let hb? ← if k == 2 then pure none else omegaProves (← le (toExpr (1 : Int)) b)
      if k != 2 && hb?.isNone then continue
      -- the least upper bound in `[0, 64]`, by bisection
      if (← omegaProves (← le t (toExpr (64 : Nat)))).isSome then
        let mut lo := 0
        let mut hi := 64
        while lo < hi do
          let mid := (lo + hi) / 2
          if (← omegaProves (← le t (toExpr mid))).isSome then hi := mid else lo := mid + 1
        if let some h ← omegaProves (← le t (toExpr hi)) then
          if k == 2 then
            let (m, hm) ← powLit hi
            assertMainM `hpow_le (mkAppOptM ``LeanModels.Sv.CombView.two_pow_le_lit #[t, toExpr hi, m, h, hm])
          else if let some hb := hb? then
            let (m, hm) ← powLitB b k hi
            assertMainM `hpow_le
              (mkAppOptM ``LeanModels.Sv.CombView.lit_pow_le_lit #[b, hb, t, toExpr hi, m, h, hm])
      -- the greatest lower bound in `[0, 64]`
      let mut lo := 0
      let mut hi := 64
      while lo < hi do
        let mid := (lo + hi + 1) / 2
        if (← omegaProves (← le (toExpr mid) t)).isSome then lo := mid else hi := mid - 1
      let h ← match ← omegaProves (← le (toExpr lo) t) with
        | some h => pure h
        | none => mkAppM ``Nat.zero_le #[t]
      if k == 2 then
        let (m, hm) ← powLit lo
        assertMainM `hpow_ge (mkAppOptM ``LeanModels.Sv.CombView.lit_le_two_pow #[t, toExpr lo, m, h, hm])
        lows := lows.push (t, lo, h)
      else if let some hb := hb? then
        let (m, hm) ← powLitB b k lo
        assertMainM `hpow_ge (mkAppOptM ``LeanModels.Sv.CombView.lit_le_lit_pow #[b, hb, t, toExpr lo, m, h, hm])
    for (x, t) in ds do
      if seenD.any (fun (x', t') => x' == x && t' == t) then continue
      seenD := seenD.push (x, t)
      if let some h ← omegaProves (← mkAppM ``LE.le #[toExpr (0 : Int), x]) then
        assertMainM `hdiv_pow (mkAppM ``LeanModels.Sv.CombView.ediv_two_pow_nonneg #[t, h])
        if let some (_, c, hc) := lows.find? (fun (t', _, _) => t' == t) then
          if 1 ≤ c then
            let (m, hm) ← powLit c
            assertMainM `hdiv_pow_le
              (mkAppOptM ``LeanModels.Sv.CombView.ediv_two_pow_le_lit #[x, t, toExpr c, m, h, hc, hm])
      else if let some h ← omegaProves (← mkAppM ``LT.lt #[x, toExpr (0 : Int)]) then
        assertMainM `hdiv_pow (mkAppM ``LeanModels.Sv.CombView.ediv_two_pow_neg #[t, h])
      else
        assertMainM `hdiv_pow (mkAppM ``LeanModels.Sv.CombView.ediv_two_pow_between #[x, t])

/-- The arguments `x` of the `canonInt 32 true x` subterms of `e` that mention a free variable, innermost first (refusal
text only). -/
partial def canonArgs (e : Lean.Expr) : Array Lean.Expr :=
  match e with
  | .app f a =>
      let sub := canonArgs f ++ canonArgs a
      if e.isAppOfArity ``LeanModels.Sv.canonInt 3 && a.hasFVar && !a.hasLooseBVars then sub.push a else sub
  | .mdata _ b | .proj _ _ b => canonArgs b
  | _ => #[]

/-- (Refusal text only.) `e` with its 32-bit wraps dropped, the way the summary reads it. -/
def unwrapShow (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun x => do
    if x.isAppOfArity ``LeanModels.Sv.canonInt 3 then return .done x.appArg! else return .continue)

/-- (Refusal text only.) The first wrapped value of `e` (innermost first) that `int32Bound` cannot place in the signed
32-bit range in the context of `g`. The state is restored. -/
def firstUnplaced (g : MVarId) (e : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let st ← saveState
  try
    for x in canonArgs (← instantiateMVars e) do
      let pfFn := mkApp (mkConst ``LeanModels.Sv.CombView.canonInt32_of_bounds) x
      let (bs, _, _) ← g.withContext do forallMetaTelescopeReducing (← inferType pfFn)
      for b in bs do
        let ty ← instantiateMVars (← inferType b)
        let m ← g.withContext (mkFreshExprSyntheticOpaqueMVar ty)
        setGoals [m.mvarId!]
        let ok ← try
            addClog2Facts #[x]
            addPowFacts #[x]
            int32Bound
            pure (← getGoals).isEmpty
          catch _ => pure false
        unless ok do
          st.restore
          return some x
    st.restore
    return none
  catch _ =>
    st.restore
    return none

/-- The valuation of the summary's constants as terms over the arguments (`ceTerm`, definitionally `s.val args n`). -/
unsafe def valTerms (sv : Summary) (args : Lean.Expr) : MetaM (List (String × Lean.Expr)) := do
  let argEs ← listElemExprs (← instantiateMVars args)
  let mut m : List (String × Lean.Expr) := (sv.params.zip argEs.toList).reverse
  for (n, c) in sv.lps do
    m := (n, ← ceTerm m c) :: m
  return m

/-- **Close an agreement goal** `names.map (fun n => env.intVal? n) = names.map g`: for each name, the environment's
value (by unification) against the term `val n` (definitionally `g n`), with the `canonInt` removal of `closeHag`. -/
unsafe def closeHagWith (tac : String) (g : MVarId) (names : List String) (val : String → Lean.Expr)
    (diag : String → Option String := fun _ => none) (hint : String → String := fun _ => "") : TacticM Unit := do
  let what := "the parameter values could not be read off the instantiation environment"
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := ty.eq? | throwError "{tac}: internal error: `hag` is not an equation"
    unless lhs.isAppOfArity ``List.map 4 && rhs.isAppOfArity ``List.map 4 do
      throwError "{tac}: internal error: `hag` is not an equation of two maps"
    let f := lhs.getAppArgs[2]!
    let gf := rhs.getAppArgs[2]!
    let strT := mkConst ``String
    let mut acc : Lean.Expr ← mkExpectedTypeHint
      (← mkEqRefl (mkApp4 (mkConst ``List.map [Level.zero, Level.zero]) strT
        (mkApp (mkConst ``Option [Level.zero]) (mkConst ``Int)) f (mkApp (mkConst ``List.nil [Level.zero]) strT)))
      (← mkEq (mkApp4 (mkConst ``List.map [Level.zero, Level.zero]) strT
          (mkApp (mkConst ``Option [Level.zero]) (mkConst ``Int)) f (mkApp (mkConst ``List.nil [Level.zero]) strT))
        (mkApp4 (mkConst ``List.map [Level.zero, Level.zero]) strT
          (mkApp (mkConst ``Option [Level.zero]) (mkConst ``Int)) gf (mkApp (mkConst ``List.nil [Level.zero]) strT)))
    let mut suffix : List String := []
    for n in names.reverse do
      let nE := toExpr n
      let v ← mkFreshExprMVar (mkConst ``Int)
      unless ← isDefEq (mkApp f nE).headBeta (← mkAppM ``Option.some #[v]) do
        throwError "{tac}: {what}: `{n}` is not bound as a 32-bit signed `int` in the instantiation environment"
      -- the value as unification left it may hold `match`es of the parameter stage whose discriminants compute (a
      -- child's parameter point, `PDesign.atPoint`): reduce them, definitionally
      let v ← Meta.transform (← instantiateMVars v) (pre := fun e => do
        match ← Meta.reduceMatcher? e with
        | ReduceMatcherResult.reduced e' => return .visit e'
        | _ => return .continue)
      let r := val n
      unless ← isDefEq (mkApp gf nE).headBeta (← mkAppM ``Option.some #[r]) do
        throwError "{tac}: internal error: the valuation of `{n}` is not `{r}`"
      let pg ← mkFreshExprSyntheticOpaqueMVar (← mkEq (← mkAppM ``Option.some #[v]) (← mkAppM ``Option.some #[r]))
      setGoals [pg.mvarId!]
      addClog2Facts #[v, r]
      -- a definition with a shift (`CE.shl`/`shr`/`ashr`, a power of two in its term) takes the route below only: the
      -- general one ends in `rfl`, which would unfold the instantiation's `Int.fdiv`/`Int.tdiv` and the summary's `%`
      let hasShift := !(powArgs (← instantiateMVars r)).1.isEmpty
      try
        if hasShift then throwError "shift"
        evalTactic (← `(tactic| ((try simp (disch := omega) only [Int.ofNat_eq_natCast,
            LeanModels.Sv.CombView.canonInt32_of_bounds, Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg,
            LeanModels.Sv.convertConst, Nat.max_self, Bool.and_self, ↓reduceIte, Int.reducePow, Int.emod_eq_of_lt,
            LeanModels.Sv.CombView.canonInt32_add_l, LeanModels.Sv.CombView.canonInt32_add_r,
            LeanModels.Sv.CombView.canonInt32_sub_l, LeanModels.Sv.CombView.canonInt32_sub_r, LeanModels.Sv.CombView.canonInt32_mul_l,
            LeanModels.Sv.CombView.canonInt32_mul_r, LeanModels.Sv.CombView.canonInt32_neg, LeanModels.Sv.CombView.canonInt32_idem,
            LeanModels.Sv.CombView.emod_eq_hmod, Option.some.injEq]) <;> first | rfl | omega)))
      catch _ =>
        unless hasShift do
          let at? ← firstUnplaced g v
          let shown? ← match at? with
            | some x => pure (some (← unwrapShow x))
            | none => pure none
          let whereS := match shown? with
            | some x => m!", and `omega` could not place `{x}` (each step of it wrapped) in that range from the hypotheses in context"
            | none => m!", and `omega` could not show that from the hypotheses in context"
          throwError "{tac}: {what}: at a symbolic parameter the instantiation holds `{n}` at its exact 32-bit `int` value, `{← unwrapShow v}` wrapped to 32 bits at every step, which is the summary's `{r}` only where every value is in the signed 32-bit range [-2147483648, 2147483647] (the instantiation wraps every literal, constant read and intermediate result of an `int` expression to 32 bits, IEEE 1800-2023 §11.4, §11.6.1, §11.8.1){whereS} (a theorem at a symbolic `int` parameter needs a range premise such as `(hR : (N : Int) < 2147483648)` that keeps every intermediate value of a definition in range, e.g. `N + 1` needs `N < 2147483647`){hint n}"
        -- a shift: the summary reads its operands as 32-bit patterns (`% 2^32`), the instantiation as the integers;
        -- where `omega` places them in range the two are the same, and the powers `2 ^ t` are atoms that need their
        -- bounds (`addPowFacts`)
        try
          evalTactic (← `(tactic| (try simp only [Int.ofNat_eq_natCast, Int.toNat_natCast, Option.some.injEq,
            Int.reduceToNat, Int.reduceMod, Int.reducePow, Int.reduceMul, LeanModels.Sv.CombView.emod_eq_hmod])))
          unless (← getGoals).isEmpty do
            evalTactic (← `(tactic| (try simp (disch := omega) only [Int.emod_eq_of_lt, Int.add_sub_cancel,
              LeanModels.Sv.convertConst, Nat.max_self, Bool.and_self, ↓reduceIte,
              LeanModels.Sv.CombView.emod_eq_hmod, Int.reduceMod, Int.reducePow,
              Int.toNat_natCast, LeanModels.Sv.CombView.fdiv_two_pow, LeanModels.Sv.CombView.fdiv_of_nonneg,
              Int.reduceToNat, LeanModels.Sv.CombView.canonInt32_add_l, LeanModels.Sv.CombView.canonInt32_add_r,
              LeanModels.Sv.CombView.canonInt32_sub_l, LeanModels.Sv.CombView.canonInt32_sub_r, LeanModels.Sv.CombView.canonInt32_mul_l,
              LeanModels.Sv.CombView.canonInt32_mul_r, LeanModels.Sv.CombView.canonInt32_neg, LeanModels.Sv.CombView.canonInt32_idem,
              LeanModels.Sv.CombView.shr_pattern_of_bounds, LeanModels.Sv.CombView.shr_pattern_canon,
              Int.tdiv_eq_ediv_of_nonneg, LeanModels.Sv.CombView.canonInt32_of_bounds])))
          unless (← getGoals).isEmpty do
            addPowFacts #[← getMainTarget]
            evalTactic (← `(tactic| ((try simp (disch := omega) only [LeanModels.Sv.CombView.canonInt32_of_bounds,
              LeanModels.Sv.CombView.canonInt32_add_l, LeanModels.Sv.CombView.canonInt32_add_r,
              LeanModels.Sv.CombView.canonInt32_sub_l, LeanModels.Sv.CombView.canonInt32_sub_r, LeanModels.Sv.CombView.canonInt32_mul_l,
              LeanModels.Sv.CombView.canonInt32_mul_r, LeanModels.Sv.CombView.canonInt32_neg, LeanModels.Sv.CombView.canonInt32_idem,
              LeanModels.Sv.CombView.shr_pattern_of_bounds, LeanModels.Sv.CombView.shr_pattern_canon,
              Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg]) <;> first | omega | with_reducible rfl)))
        catch _ =>
          -- a closed value (a definition that names no parameter): both sides are numbers, say which
          let vI ← instantiateMVars v
          let rI ← instantiateMVars r
          if !vI.hasFVar && !vI.hasMVar && !rI.hasFVar && !rI.hasMVar then
            let mut vv? : Option Int := none
            let mut rv? : Option Int := none
            try
              vv? := some (← Lean.Meta.evalExpr Int (mkConst ``Int) vI)
              rv? := some (← Lean.Meta.evalExpr Int (mkConst ``Int) rI)
            catch _ => pure ()
            if let (some vv, some rv) := (vv?, rv?) then
              let why := (diag n).getD "the two readings differ at no operation the tactics can name"
              throwError "{tac}: {what}: the constant `{n}` is the 32-bit `int` {vv} in the instantiation, and the summary's value of its definition is {rv}: {why}"
          throwError "{tac}: {what}: at a symbolic parameter the instantiation holds `{n}` at its exact 32-bit `int` value, `{← unwrapShow v}` wrapped to 32 bits at every step, which is the summary's `{r}` only where every value is in the signed 32-bit range [-2147483648, 2147483647] (the instantiation wraps every literal, constant read and intermediate result of an `int` expression to 32 bits, IEEE 1800-2023 §11.4, §11.6.1, §11.8.1), and `omega` could not show that from the hypotheses in context (a theorem at a symbolic `int` parameter needs a range premise such as `(hR : (N : Int) < 2147483648)`; a shift `a << b` is in range where `a * 2^b` is, §11.4.10){hint n}"
      unless (← getGoals).isEmpty do throwError "{tac}: {what} (`{n}`)"
      let h ← mkExpectedTypeHint (← instantiateMVars pg) (← mkEq (mkApp f nE) (mkApp gf nE))
      acc := mkAppN (mkConst ``LeanModels.Sv.CombView.hag_cons) #[f, gf, nE, toExpr suffix, h, acc]
      suffix := n :: suffix
    unless ← isDefEq ty (← inferType acc) do
      throwError "{tac}: internal error: the parameter list is not `{names}`"
    g.assign acc
    setGoals []

/-- (Refusal text only; no theorem reads it.) At concrete arguments, where `rfl` does not close `hag`: the first constant
whose value in the instantiation environment (evaluated) is not the summary's, named with both values. -/
unsafe def hagMismatch (g : MVarId) (sv : Summary) (args : Lean.Expr) : MetaM (Option String) := do
  try
    let ty ← instantiateMVars (← g.getType)
    let some (_, lhs, _) := ty.eq? | return none
    unless lhs.isAppOfArity ``List.map 4 do return none
    let f := lhs.getAppArgs[2]!
    let envE ← match f with
      | .lam _ _ body _ =>
          if body.isAppOfArity ``IEnv.intVal? 2 then pure body.appFn!.appArg! else return none
      | _ => if f.isAppOfArity ``IEnv.intVal? 1 then pure f.appArg! else return none
    if envE.hasLooseBVars || envE.hasFVar || envE.hasMVar then return none
    let env ← Lean.Meta.evalExpr IEnv (mkConst ``IEnv) envE
    let argsV ← evalArgs args
    let lpNames := sv.lps.map Prod.fst
    let σ := sv.val argsV
    for n in sv.params do
      let want := sv.val argsV n
      match env.intVal? n with
      | some v =>
          if v != want then
            if lpNames.contains n then
              let why := match sv.lps.lookup n with
                | some c => (c.wrapDiag σ).getD "the two readings differ at no operation the tactics can name"
                | none => "the two readings differ at no operation the tactics can name"
              return some s!"the localparam `{n}` is the 32-bit `int` {v} in the instantiation, and the summary's value of its definition is {want}: {why}"
            else
              return some s!"the parameter `{n}` is {v} in the instantiation and {want} in the summary's valuation"
      | none => return some s!"`{n}` is not bound as a 32-bit signed `int` in the instantiation environment"
    return none
  catch _ => return none

/-- **Close `hag`** (`s.params.map (fun n => env.intVal? n) = s.params.map (fun n => some (s.val args n))`), the
agreement of the instantiation environment with the summary's valuation. At concrete arguments `rfl` decides it. At
a symbolic argument the environment holds each `int` parameter and localparam at its exact 32-bit value, `canonInt 32
true` of the argument or of the width-exact fold of the definition, and the valuation holds the unbounded integer:
for each name the tactic reads the environment's value (by unification, the computation `rfl` did), states it against
the valuation's value, and removes every `canonInt 32 true` whose argument `omega` shows to be in the signed 32-bit
range from the hypotheses in context (`canonInt32_of_bounds`, with `Int.tdiv`/`Int.tmod` of a non-negative numerator
as `/`/`%`). A value it cannot place in range is an error that names it: a theorem at a symbolic `int` parameter
needs its range premise, e.g. `(hR : (N : Int) < 2147483648)`. -/
unsafe def closeHag (tac : String) (g : MVarId) (sv : Summary) (args : Lean.Expr) : TacticM Unit := do
  let what := "the parameter values could not be read off the instantiation environment"
  let argsI ← instantiateMVars args
  if !argsI.hasFVar && !argsI.hasMVar then
    setGoals [g]
    try evalTactic (← `(tactic| rfl)) catch e =>
      match ← hagMismatch g sv argsI with
      | some m => throwError "{tac}: {what}: {m}"
      | none => throwError "{tac}: {what}\n{e.toMessageData}"
    unless (← getGoals).isEmpty do throwError "{tac}: {what}"
    return
  let m ← valTerms sv args
  -- a definition that names no parameter has its value at any arguments: `sv.val []` names the operation that wraps
  closeHagWith tac g sv.params (fun n => (m.lookup n).getD (toExpr (0 : Int)))
    (fun n => (sv.lps.lookup n).bind (·.wrapDiag (sv.val [])))
    (fun n => ((sv.lps.lookup n).map CE.ashrHint).getD "")

/-! ### The parameter stage at a symbolic point (`h1`)

`h1 : pd.paramEnv2 args = .ok ?env` is the instantiation environment, computed by `rfl`. At a symbolic `int`
argument the computation carries `canonInt 32 true v`, the exact 32-bit value, and it stops wherever it DECIDES on such a
value: the sign test of `$clog2` (`$clog2` of a negative value is an error), and any fold after it. `closeParamEnv`
first tries `rfl`; where `rfl` is stuck it evaluates the left-hand side with `canonInt` held back
(`whnfCanon`) down to the first `canonInt 32 true x` the evaluation needs (`exposeCanon`: the term is reduced only along
the path to it, so it is definitionally the goal's), shows `x` in the signed 32-bit range from the hypotheses in context
(`omega`, with `Int.tdiv`/`Int.tmod` of a non-negative numerator as `/`/`%` and the `clog2` facts), rewrites
`canonInt 32 true x` to `x` (`canonInt32_of_bounds`) and tries `rfl` again. Every rewrite is a kernel-checked equation;
the environment the final `rfl` computes holds the values in range, as the summary does. A value it cannot place in
range is an error that names it. -/

/-- `whnf` with `canonInt` held back. -/
def whnfCanon (e : Lean.Expr) : MetaM Lean.Expr :=
  withCanUnfoldPred (fun _ ci => pure (ci.name != ``LeanModels.Sv.canonInt)) (whnf e)

/-- The `canonInt` applications of `a` with a CLOSED argument replaced by their head normal forms (definitionally `a`):
the instantiation wraps every literal of an `int` expression (`canonInt 32 true 1` for `1`), which the evaluation must see
through. -/
def evalClosedCanon (a : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform a (post := fun x => do
    if x.isAppOfArity ``LeanModels.Sv.canonInt 3 && !x.hasFVar && !x.hasMVar && !x.hasLooseBVars then
      -- the value as an integer literal where the head normal form gives one (`Int.ofNat n`, `Int.negSucc n`)
      let v ← whnf x
      let lit? : Option Int ← do
        if v.isAppOfArity ``Int.ofNat 1 then
          pure ((← whnf v.appArg!).rawNatLit?.map fun n => (n : Int))
        else if v.isAppOfArity ``Int.negSucc 1 then
          pure ((← whnf v.appArg!).rawNatLit?.map fun n => -((n : Int) + 1))
        else pure none
      return .done (match lit? with | some i => toExpr i | none => v)
    else return .continue)

/-- `whnfCanon`, where a wrapped CLOSED value does not stop the evaluation: when the result is stuck, the closed `canonInt`
applications among its (non-function) arguments are evaluated (`evalClosedCanon`) and the reduction goes on. -/
partial def whnfCanonC (e : Lean.Expr) (fuel : Nat := 64) : MetaM Lean.Expr := do
  let e1 ← whnfCanon e
  if fuel == 0 || !e1.isApp then return e1
  let fn := e1.getAppFn
  let args := e1.getAppArgs
  let mut changed := false
  let mut args' := args
  for i in [0:args.size] do
    let a := args[i]!
    if a.isLambda || a.hasLooseBVars || a.isSort then continue
    -- only an argument that holds a `canonInt` at all is rebuilt
    unless (a.find? (·.isConstOf ``LeanModels.Sv.canonInt)).isSome do continue
    let a' ← evalClosedCanon a
    if a' != a then
      changed := true
      args' := args'.set! i a'
  if changed then whnfCanonC (mkAppN fn args') (fuel - 1) else return e1

/-- **The first `canonInt` an evaluation needs**: `e` reduced along the path to the first stuck application
`t = canonInt w s x` with `x` mentioning a free variable (the innermost one first), definitionally `e`, with `t` a
syntactic subterm; subterms that already contain `t` are kept unreduced. `none`: no such application. -/
partial def exposeCanon (e : Lean.Expr) (fuel : Nat) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  if fuel == 0 || !e.hasFVar then return none
  let e' ← whnfCanon e
  let found? : Option (Lean.Expr × Lean.Expr) ← do
    if e'.isAppOfArity ``LeanModels.Sv.canonInt 3 then
      let x := e'.appArg!
      match ← exposeCanon x (fuel - 1) with
      | some (x', t) =>
          pure (some (mkApp e'.appFn! (if (x.find? (· == t)).isSome then x else x'), t))
      | none => pure (if x.hasFVar then some (e', e') else none)
    else if e'.isApp then
      let fn := e'.getAppFn
      let args := e'.getAppArgs
      let mut res : Option (Lean.Expr × Lean.Expr) := none
      for i in [0:args.size] do
        let a := args[i]!
        if a.isLambda || a.isSort || a.hasLooseBVars then continue
        if (← isType a) || (← isProof a) then continue
        if let some (a', t) ← exposeCanon a (fuel - 1) then
          res := some (mkAppN fn (args.set! i (if (a.find? (· == t)).isSome then a else a')), t)
          break
      pure res
    else if let .proj sn i b := e' then
      -- a projection of a stuck structure (`Decidable.decide` of a stuck instance)
      match ← exposeCanon b (fuel - 1) with
      | some (b', t) => pure (some (.proj sn i (if (b.find? (· == t)).isSome then b else b'), t))
      | none => pure none
    else pure none
  match found? with
  | some (e'', t) => return some (if (e.find? (· == t)).isSome then e else e'', t)
  | none => return none

/-- The term whose occurrence keeps a subterm unreduced (`exposeStuck`): a stuck DECISION is the projection `inst.1` of
its instance, and a subterm holds the instance itself (the `[Decidable p]` argument of an `if`), so the instance is what
is looked for; a stuck `canonInt` is itself. -/
def stuckKey (t : Lean.Expr) : Lean.Expr :=
  match t with
  | .proj ``Decidable 0 b => b
  | _ => t

/-- `a` holds the stuck step `t` (`stuckKey`) as a syntactic subterm. -/
def holdsStuck (a t : Lean.Expr) : Bool := (a.find? (· == stuckKey t)).isSome

/-- The instance of `@ite α p inst x y` (or `dite`) when it is not decided yet (its head normal form is not
`Decidable.intro` of a literal). -/
def undecidedIteInst? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  unless e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 do return none
  let inst := e.getArg! 2
  unless inst.hasFVar do return none
  let iw ← whnfCanonC inst
  if iw.isAppOfArity ``Decidable.intro 2 then
    let b ← whnf (iw.getArg! 1)
    if b.isConstOf ``Bool.true || b.isConstOf ``Bool.false then return none
  return some inst

/-- **The first stuck step of an evaluation**, as `exposeCanon`, where the step is either a `canonInt w s x` with `x`
mentioning a free variable, or a DECISION: the `Decidable.decide` projection of an instance whose proposition mentions a
free variable (the sign test of a shift amount at a symbolic parameter, `if b < 0 then … else …` in `evalInt`). A
decision's own instance is reduced first, so a `canonInt` it needs is found before the decision; with `inDec = false` the
decision itself is found first (`closeParamEnv` decides it from its proposition where it can).

An `if` that is an argument (not the head, which the evaluation reduces) is a decision INSIDE a value, `if a < 0 then
a + 2^32 else a` in the instantiation's `>>` of an `int` (`evalIntExactRec`, IEEE 1800-2023 §11.4.10: the shift reads the
32-bit pattern of `a`): it is found with its own instance and kept folded (and every subterm that holds the instance with
it, `Int.tdiv` included), so the value the environment holds is the definition's own term, which `omega` reads (an `if`
of an `Int` is a case split for it). The decisions in `skip` (instances `closeParamEnv` could not decide) are not stuck
steps: their `if` is left as it is. -/
partial def exposeStuck (e : Lean.Expr) (fuel : Nat) (inDec : Bool := true) (skip : Array Lean.Expr := #[]) :
    MetaM (Option (Lean.Expr × Lean.Expr)) := do
  if fuel == 0 || !e.hasFVar then return none
  -- a decision inside a value: the `if` itself, folded
  if let some inst ← undecidedIteInst? e then
    if skip.contains inst then return none
    let t := Lean.Expr.proj ``Decidable 0 inst
    if !inDec then return some (e, t)
    match ← exposeStuck inst (fuel - 1) inDec skip with
    | some (inst', t') =>
        return some (if holdsStuck e t' then e else mkAppN e.getAppFn (e.getAppArgs.set! 2 inst'), t')
    | none => return some (e, t)
  let e' ← whnfCanonC e
  let found? : Option (Lean.Expr × Lean.Expr) ← do
    if e'.isAppOfArity ``LeanModels.Sv.canonInt 3 then
      let x := e'.appArg!
      match ← exposeStuck x (fuel - 1) inDec skip with
      | some (x', t) =>
          pure (some (mkApp e'.appFn! (if holdsStuck x t then x else x'), t))
      | none => pure (if x.hasFVar then some (e', e') else none)
    else if let .proj ``Decidable 0 b := e' then
      if skip.contains b then pure none
      -- `inDec = false`: the decision itself, before the wrapped values inside it (its proposition may mention them in
      -- another form, `convertConst`, where a rewrite of the value alone would leave the instance's type behind)
      else if !inDec && e'.hasFVar then pure (some (e', e'))
      else
      match ← exposeStuck b (fuel - 1) inDec skip with
      | some (b', t) => pure (some (.proj ``Decidable 0 (if holdsStuck b t then b else b'), t))
      | none => pure (if e'.hasFVar then some (e', e') else none)
    else if e'.isApp then
      let fn := e'.getAppFn
      let args := e'.getAppArgs
      let mut res : Option (Lean.Expr × Lean.Expr) := none
      for i in [0:args.size] do
        let a := args[i]!
        if a.isLambda || a.isSort || a.hasLooseBVars then continue
        if (← isType a) || (← isProof a) then continue
        if let some (a', t) ← exposeStuck a (fuel - 1) inDec skip then
          res := some (mkAppN fn (args.set! i (if holdsStuck a t then a else a')), t)
          break
      pure res
    else if let .proj sn i b := e' then
      match ← exposeStuck b (fuel - 1) inDec skip with
      | some (b', t) => pure (some (.proj sn i (if holdsStuck b t then b else b'), t))
      | none => pure none
    else pure none
  match found? with
  | some (e'', t) => return some (if holdsStuck e t then e else e'', t)
  | none => return none

/-- The innermost subterm of `e` of an `Except` type that holds `k` (closed under no binder): the evaluation step that a
decision whose instance is `k` stops (`liftIte`). -/
partial def innerExceptHolding (e k : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if e.hasLooseBVars || (e.find? (· == k)).isNone then return none
  let kids : Array Lean.Expr := match e with
    | .app .. => e.getAppArgs.push e.getAppFn
    | .mdata _ b | .proj _ _ b => #[b]
    | _ => #[]
  for c in kids do
    if let some r ← innerExceptHolding c k then return some r
  let ty ← try whnf (← inferType e) catch _ => return none
  return if ty.isAppOfArity ``Except 2 then some e else none

/-- The decision instances of `e` (applications of a `Decidable` instance whose proposition mentions a free variable:
`Int.decLt a b`, `Int.decEq a b`, …), innermost first, without repetition (closed under no binder). -/
partial def decisionInsts (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let rec go (e : Lean.Expr) (acc : Array Lean.Expr) : MetaM (Array Lean.Expr) := do
    if e.hasLooseBVars || !e.hasFVar then return acc
    let mut acc := acc
    match e with
    | .app .. =>
        for a in e.getAppArgs do
          acc ← go a acc
    | .mdata _ b | .proj _ _ b => acc ← go b acc
    | _ => pure ()
    if e.isApp && !acc.contains e then
      if let .const n _ := e.getAppFn then
        let s := match n with
          | .str _ x => x
          | _ => ""
        if s.startsWith "dec" || s.startsWith "instDecidable" then
          let ty ← try whnf (← inferType e) catch _ => pure (mkConst ``Unit)
          if ty.isAppOfArity ``Decidable 1 then acc := acc.push e
    return acc
  go e #[]

/-- The name of a private definition of the parameter stage (`Param.lean`): the comparison `constCompare` and the
Boolean-to-integer `b2i` the instantiation evaluates a comparison through. -/
def paramPrivate (n : Name) : Name := Name.append ((`_private ++ `LeanModels.Sv.Param).num 0) n

/-- **The condition of a lifted `?:` in a form `omega` reads** (`liftIte`): `q` is the instantiation's own test,
`(bne (convertConst 1 1 false (constCompare op a b)) 0) = true` for a comparison `a op b`; with `constCompare` and `b2i`
unfolded (definitionally) and the conversions rewritten (`convertConst`, `canonInt_one_false`, the 32-bit wraps of the
operands removed where `omega` places them in range) it is a statement about `a` and `b`. Returns `q'` and `q = q'`. -/
def liftCond (g : MVarId) (q : Lean.Expr) : TacticM (Lean.Expr × Lean.Expr) := do
  let cc := paramPrivate `LeanModels.Sv.constCompare
  let bi := paramPrivate `LeanModels.Sv.b2i
  let q1 ← Meta.transform q (pre := fun e => do
    if e.isAppOf cc || e.isAppOf bi then
      if let some e' ← unfoldDefinition? e then return .visit (← whnfCore e')
    return .continue)
  let stx ← `(tactic| simp (disch := omega) only [LeanModels.Sv.convertConst, Nat.max_self, Bool.and_self,
    Bool.and_true, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, ite_self, gt_iff_lt, ge_iff_le, beq_iff_eq, LeanModels.Sv.CombView.canonInt_one_false, decide_eq_true_eq, bne_iff_ne, ne_eq,
    Int.reducePow, Int.reduceMod, LeanModels.Sv.CombView.emod_eq_hmod, Int.emod_eq_of_lt, Int.ofNat_eq_natCast,
    LeanModels.Sv.CombView.canonInt32_idem, LeanModels.Sv.CombView.canonInt32_of_bounds])
  -- the simp context and its discharger (`omega`) read the main goal's context: `g`'s, restored after
  let gs ← getGoals
  setGoals [g]
  let (res, _) ← try
      let sc ← mkSimpContext stx (eraseLocal := false)
      sc.dischargeWrapper.with fun d? => Lean.Meta.simp q1 sc.ctx sc.simprocs d?
    finally setGoals gs
  let pf ← match res.proof? with
    | some pf => pure pf
    | none => mkEqRefl q1
  pure (res.expr, ← mkExpectedTypeHint pf (← mkEq q res.expr))

mutual

/-- **A decision the hypotheses do not settle, lifted into the value** (`eq_ok_ite_of_cases`). `t` is a stuck decision
(the instance `inst`) found in `g` (`lhs = rhs`, `exposeStuck`'s form); `r` is the innermost evaluation step of an
`Except` type that holds it. Where `r` is an `if` of the evaluation (`Decidable.rec`/`casesOn` of an instance `I : Decidable
q`, a constant motive, arms `X` and `Y` that do not use the case: the `?:` of `evalAt` whose condition compares a symbolic
parameter, IEEE 1800-2023 §11.4.11), each arm is evaluated on its own (`closeParamEnv` on `X = .ok ?x`, `Y = .ok ?y`), and
`r` is rewritten to `.ok (if q' then x else y)`, `q'` the condition in the form `omega` reads (`liftCond`, `q = q'`).
`none` (the state restored) where `r` is not such an `if` or an arm has no value: a decision that selects an error (the
sign test of `$clog2`'s argument, a divisor's test for zero) is not lifted, and is refused as before. Returns the new goal
and the instance of the `if` left in the value. -/
unsafe def liftIte (tac : String) (g : MVarId) (t : Lean.Expr) : TacticM (Option (MVarId × Lean.Expr)) := do
  let .proj _ _ inst := t | return none
  let st ← saveState
  try
    g.withContext do
      let ty ← instantiateMVars (← g.getType)
      let some (_, lhs, _) := ty.eq? | return none
      let some r ← innerExceptHolding lhs inst | return none
      -- the step is the `if` of the evaluation, unfolded: `Decidable.rec`/`casesOn` of its instance `I : Decidable q`
      -- with a constant motive and an arm for each case that does not use the case's proof
      let rf := r.getAppFn
      let rargs := r.getAppArgs
      let rty ← whnf (← inferType r)
      unless rty.isAppOfArity ``Except 2 do throwError "not an Except step"
      -- `ite q X Y` unfolds to `Bool.rec (motive := fun b => b.Reflects q → E) (fun _ => Y) (fun _ => X) d h` (the
      -- instance's `decide` and its reflection proof; `Decidable.rec`/`casesOn` of the instance in an older core): the
      -- instance is synthesized for `q` and the `if` checked definitionally equal to `r`
      let (q, mF, mT) ← match rf with
        | .const ``Bool.rec _ =>
            if rargs.size != 5 then throwError "not an if"
            let .lam _ _ (.forallE _ dom _ _) _ := rargs[0]! | throwError "not an if"
            unless dom.getAppNumArgs == 2 && dom.getAppFn.constName?.any (·.toString.endsWith "Reflects") do
              throwError "not an if"
            let q := dom.appArg!
            if q.hasLooseBVars then throwError "not an if"
            pure (q, rargs[1]!, rargs[2]!)
        | .const ``Decidable.rec _ =>
            if rargs.size != 5 then throwError "not an if"
            pure ((← whnf (← inferType rargs[4]!)).appArg!, rargs[2]!, rargs[3]!)
        | .const ``Decidable.casesOn _ =>
            if rargs.size != 5 then throwError "not an if"
            pure ((← whnf (← inferType rargs[2]!)).appArg!, rargs[3]!, rargs[4]!)
        | _ => throwError "not an if"
      let .lam _ _ Y _ := mF | throwError "not an if"
      let .lam _ _ X _ := mT | throwError "not an if"
      if X.hasLooseBVars || Y.hasLooseBVars then throwError "an arm uses the case"
      let I ← synthInstance (mkApp (mkConst ``Decidable) q)
      unless ← isDefEq r (mkApp5 (mkConst ``ite [levelOne]) rty q I X Y) do throwError "not the if of its condition"
      let ε := rty.getArg! 0
      let α := rty.getArg! 1
      let lvls := rty.getAppFn.constLevels!
      let okOf (v : Lean.Expr) : Lean.Expr := mkApp3 (mkConst ``Except.ok lvls) ε α v
      -- each arm evaluated on its own (`closeParamEnv`, which may lift a decision inside it in turn)
      let arm (A : Lean.Expr) : TacticM (Lean.Expr × Lean.Expr) := do
        let v ← mkFreshExprMVar α
        let goal ← mkFreshExprSyntheticOpaqueMVar (← mkEq A (okOf v))
        closeParamEnv tac goal.mvarId! (lift := true)
        let vI ← instantiateMVars v
        if vI.hasMVar then throwError "an arm has no value"
        pure (vI, ← instantiateMVars goal)
      let (x, hX) ← arm X
      let (y, hY) ← arm Y
      let h1 ← withLocalDeclD `hq q fun hq => do
        let e1 ← mkAppOptM ``ite_eq_left #[q, I, hq, rty, X, Y]
        mkLambdaFVars #[hq] (← mkExpectedTypeHint (← mkEqTrans e1 hX) (← mkEq r (okOf x)))
      let h2 ← withLocalDeclD `hq (mkNot q) fun hq => do
        let e2 ← mkAppOptM ``ite_eq_right #[q, I, hq, rty, X, Y]
        mkLambdaFVars #[hq] (← mkExpectedTypeHint (← mkEqTrans e2 hY) (← mkEq r (okOf y)))
      let eq0 ← mkAppOptM ``LeanModels.Sv.CombView.eq_ok_ite_of_cases #[ε, α, r, q, I, x, y, h1, h2]
      -- the condition in a normal form `omega` reads (`liftCond`): the comparison itself, not the instantiation's
      -- `bne (b2i (decide …)) 0` around it
      let (eq, Iv) ← try
          let (q', hqq') ← liftCond g q
          let I' ← synthInstance (mkApp (mkConst ``Decidable) q')
          let hT ← withLocalDeclD `hc q' fun hc => do mkLambdaFVars #[hc] (← mkEqRefl x)
          let hE ← withLocalDeclD `hc (mkNot q') fun hc => do mkLambdaFVars #[hc] (← mkEqRefl y)
          let hite ← mkAppOptM ``ite_congr #[α, q, q', x, y, x, y, I, I', hqq', hT, hE]
          pure (← mkEqTrans eq0 (← mkCongrArg (mkApp2 (mkConst ``Except.ok lvls) ε α) hite), I')
        catch _ => pure (eq0, I)
      let g' ← rewriteDesign g eq
      return some (g', Iv)
  catch _ =>
    st.restore
    return none

/-- **`liftIte` at the first decision that lifts**: `t?` first, then every decision instance of `g`'s left-hand side whose
proposition mentions a free variable, innermost first (`decisionInsts`). The condition of a `?:` over a comparison is
`cv != 0` for the comparison's value `cv`, and its instance reduces to the comparison's own (`Int.decLt b a` of `a > b`):
the innermost one names the comparison itself, which is what the `if` in the value then holds. -/
unsafe def liftAny (tac : String) (g : MVarId) (t? : Option Lean.Expr) : TacticM (Option (MVarId × Lean.Expr)) := do
  if let some t := t? then
    if let some r ← liftIte tac g t then return some r
  let insts ← g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some (_, lhs, _) := ty.eq? | return #[]
    decisionInsts lhs
  for inst in insts.toList.take 12 do
    if let some r ← liftIte tac g (.proj ``Decidable 0 inst) then return some r
  return none

/-- **Close `h1`** (`pd.paramEnv2 args = .ok ?env`): `rfl`, or, where the computation stops at an exact 32-bit
value, the rewrites described above, then `rfl`. A decision the hypotheses do not settle, on which a `?:` selects
between two values, is lifted into the value (`liftIte`), for a design whose localparams have a `?:` (`lift`,
`Summary.hasCond`): the environment then holds `if p then x else y`. -/
unsafe def closeParamEnv (tac : String) (g : MVarId) (lift : Bool := false) : TacticM Unit := do
  let what := "the parameter stage (`paramEnv2`) of this design could not be evaluated at a symbolic parameter"
  let tryRfl (g : MVarId) : TacticM Bool := do
    let st ← saveState
    setGoals [g]
    try
      evalTactic (← `(tactic| rfl))
      if (← getGoals).isEmpty then return true
      st.restore; return false
    catch _ =>
      st.restore; return false
  if ← tryRfl g then return
  let mut g := g
  -- the decisions `omega` could not settle, set aside (`exposeStuck`'s `skip`): such a decision may sit inside a value the
  -- evaluation never needs (the `if` of `>>`'s 32-bit pattern, `evalIntExactRec`), so the search goes on past it; where
  -- nothing else is left, the refusal is the first one set aside
  let mut skip : Array Lean.Expr := #[]
  let mut pending? : Option MessageData := none
  -- every wrapped literal, constant read and intermediate result the evaluation decides on is one step
  for _ in [0:256] do
    let expose (inDec : Bool) : TacticM (Option (MVarId × Lean.Expr)) := g.withContext do
        let ty ← instantiateMVars (← g.getType)
        let some (_, lhs, rhs) := ty.eq? | throwError "{tac}: internal error: `h1` is not an equation"
        let some (lhs', t) ← exposeStuck lhs 400 inDec skip | return none
        if t.isAppOfArity ``LeanModels.Sv.canonInt 3 then
          let ws := t.appFn!.appFn!.appArg!
          let sg := t.appFn!.appArg!
          unless (← isDefEq ws (toExpr (32 : Nat))) && (← isDefEq sg (toExpr true)) do
            throwError "{tac}: {what}: the instantiation evaluates `{t}` at a symbolic parameter (only the 32-bit signed reading, `canonInt 32 true`, is placed in range)"
        let g1 ← g.replaceTargetDefEq (← mkEq lhs' rhs)
        pure (some (g1, t))
    -- a decision the evaluation stops at is decided from its proposition first (`int32Decide`); only where that fails
    -- are the wrapped values inside its instance placed in range one by one, as before
    let decideAt (gN : MVarId) (t : Lean.Expr) : TacticM (Option Lean.Expr) := do
      let .proj _ _ inst := t | return none
      let p ← gN.withContext do
        let ity ← whnf (← inferType inst)
        unless ity.isAppOfArity ``Decidable 1 do return none
        pure (some ity.appArg!)
      let some p := p | return none
      let proveBy (q : Lean.Expr) : TacticM (Option Lean.Expr) := do
        let m ← gN.withContext (mkFreshExprSyntheticOpaqueMVar q)
        let st ← saveState
        setGoals [m.mvarId!]
        addClog2Facts #[q]
        addPowFacts #[q]
        let gq ← getMainGoal
        try
          int32Decide
          if (← getGoals).isEmpty then return some (← instantiateMVars m)
          throwError "undecided"
        catch _ =>
          -- the fallback: the facts normalized with the goal (`int32DecideAll`)
          try
            setGoals [gq]
            int32DecideAll
            if (← getGoals).isEmpty then return some (← instantiateMVars m)
            st.restore
            return none
          catch _ =>
            st.restore
            return none
      if let some hp ← proveBy p then
        return some (← gN.withContext do mkAppOptM ``Subsingleton.elim #[none, none, inst, ← mkAppOptM ``isTrue #[p, hp]])
      if let some hn ← proveBy (mkNot p) then
        return some (← gN.withContext do mkAppOptM ``Subsingleton.elim #[none, none, inst, ← mkAppOptM ``isFalse #[p, hn]])
      return none
    let st0 ← saveState
    let first? ← expose false
    -- the proposition of a decision `int32Decide` could not settle (for the refusal text below)
    let mut undecided? : Option (Lean.Expr × Lean.Expr) := none
    let early? : Option (MVarId × Lean.Expr) ← match first? with
      | some (gN, t) =>
          if t.isAppOfArity ``LeanModels.Sv.canonInt 3 then pure none
          else match ← decideAt gN t with
            | some eq => pure (some (gN, eq))
            | none => pure none
      | none => pure none
    if early?.isNone then
      if let some (gN, .proj _ _ inst) := first? then
        undecided? ← gN.withContext do
          try
            let ity ← whnf (← inferType inst)
            pure (if ity.isAppOfArity ``Decidable 1 then some (ity.appArg!, inst) else none)
          catch _ => pure none
    if let some (gN, eq) := early? then
      g ← gN.withContext do rewriteDesign gN eq
      if ← tryRfl g then return
      continue
    -- a wrapped value outside every decision is taken as found; after an undecided decision (or none) `expose` assigned
    -- `g`, and the second search, into the decisions, starts from it again
    let found? ← match first? with
      | some (gN, t) =>
          if t.isAppOfArity ``LeanModels.Sv.canonInt 3 then pure (some (gN, t))
          else
            st0.restore
            expose true
      | none =>
          st0.restore
          expose true
    let some (gN, t) := found?
      | -- nothing symbolic is stuck: at concrete arguments the parameter stage itself refuses; say what it says
        let msg? ← g.withContext do
          try
            let ty ← instantiateMVars (← g.getType)
            let some (_, lhs, _) := ty.eq? | pure none
            if lhs.hasFVar || lhs.hasMVar then pure none
            else
              match ← Lean.Meta.evalExpr (Res IEnv) (mkApp (mkConst ``Res) (mkConst ``IEnv)) lhs with
              | .unsupported m => pure (some m)
              | .timeout => pure (some "the parameter stage ran out of fuel")
              | .ok _ => pure none
          catch _ => pure none
        match msg? with
        | some m => throwError "{tac}: {what}: the instantiation refuses this design at these parameters: {m}"
        | none =>
          match pending? with
          | some m => throwError m
          | none => throwError "{tac}: {what}"
    let mut eq? : Option Lean.Expr := none
    if t.isAppOfArity ``LeanModels.Sv.canonInt 3 then
      -- `x` in the signed 32-bit range, from the hypotheses in context (the hypotheses of `canonInt32_of_bounds`)
      let x := t.appArg!
      let pfFn := mkApp (mkConst ``LeanModels.Sv.CombView.canonInt32_of_bounds) x
      let (bs, _, _) ← gN.withContext do forallMetaTelescopeReducing (← inferType pfFn)
      for b in bs do
        setGoals [b.mvarId!]
        addClog2Facts #[x]
        addPowFacts #[x]
        let gb ← getMainGoal
        -- the fallback: the facts normalized with the goal (`int32DecideAll`)
        let boundOrAll : TacticM Unit := do
          try int32Bound catch _ => (do setGoals [gb]; int32DecideAll)
        try
          boundOrAll
        catch _ =>
          throwError "{tac}: {what}: the instantiation decides on `{t}`, the exact 32-bit `int` value of `{x}`, which is `{x}` only in the signed 32-bit range [-2147483648, 2147483647] (the instantiation wraps every literal, constant read and intermediate result of an `int` expression to 32 bits, IEEE 1800-2023 §11.4, §11.6.1, §11.8.1), and `omega` could not show that from the hypotheses in context (a theorem at a symbolic `int` parameter needs a range premise such as `(hR : (N : Int) < 2147483648)` that keeps every intermediate value of a definition in range, e.g. `N + 1` needs `N < 2147483647`)"
        unless (← getGoals).isEmpty do throwError "{tac}: {what} (`{x}` in range)"
      eq? := some (← instantiateMVars (mkAppN pfFn bs))
    else
      -- a decision `decide p` of the evaluation (the sign test of a shift amount, of `>>`'s operand, a divisor's test for
      -- zero): `omega` proves `p` or `¬ p` from the hypotheses in context, and the decision is that value
      let .proj _ _ inst := t | throwError "{tac}: internal error: an unexpected stuck term `{t}`"
      let p ← gN.withContext do
        let ity ← whnf (← inferType inst)
        unless ity.isAppOfArity ``Decidable 1 do
          throwError "{tac}: internal error: the stuck decision `{t}` is not of a `Decidable` instance"
        pure ity.appArg!
      let proveBy (q : Lean.Expr) : TacticM (Option Lean.Expr) := do
        let m ← gN.withContext (mkFreshExprSyntheticOpaqueMVar q)
        let st ← saveState
        setGoals [m.mvarId!]
        addClog2Facts #[q]
        addPowFacts #[q]
        let gq ← getMainGoal
        try
          int32Bound
          if (← getGoals).isEmpty then
            -- keep the state (auxiliary lemmas of `omega`); the caller resets the goal list
            return some (← instantiateMVars m)
          throwError "undecided"
        catch _ =>
          try
            setGoals [gq]
            int32DecideAll
            if (← getGoals).isEmpty then return some (← instantiateMVars m)
            st.restore
            return none
          catch _ =>
            st.restore
            return none
      -- the INSTANCE is rewritten (to `isTrue h`/`isFalse h`, equal by `Subsingleton.elim`), not its projection: the
      -- evaluation also carries the instance's proof field, whose type mentions the projection
      if let some hp ← proveBy p then
        eq? := some (← gN.withContext do mkAppOptM ``Subsingleton.elim #[none, none, inst, ← mkAppOptM ``isTrue #[p, hp]])
      else if let some hn ← proveBy (mkNot p) then
        eq? := some (← gN.withContext do mkAppOptM ``Subsingleton.elim #[none, none, inst, ← mkAppOptM ``isFalse #[p, hn]])
      else
        -- a `?:` on the decision: both arms evaluated, the value is the `if` (the instance is then set aside, so that the
        -- `if` left in the value is not taken for a stuck step again)
        if let some (gL, instL) ← (if lift then liftAny tac gN (some t) else pure none) then
          skip := skip.push instL
          g := gL
          if ← tryRfl g then return
          continue
        if pending?.isNone then
          pending? := some m!"{tac}: {what}: the instantiation decides `{p}` at a symbolic parameter (the sign test of a shift amount, a divisor's test for zero, ...), and `omega` could not decide it from the hypotheses in context (a theorem at a symbolic parameter needs premises that fix the decision, e.g. `(h : 1 ≤ E)` for a shift by `E - 1`)"
        skip := skip.push inst
        g := gN
        continue
    let some eq := eq? | continue
    try
      g ← gN.withContext do rewriteDesign gN eq
    catch e =>
      -- a wrapped value inside a decision the hypotheses do not settle: the decision is what to report, where nothing
      -- else is left
      match undecided? with
      | some (p, inst) =>
          if lift then
            if let some (gL, instL) ← liftAny tac gN none then
              skip := skip.push instL
              g := gL
              if ← tryRfl g then return
              continue
          if pending?.isNone then
            pending? := some m!"{tac}: {what}: the instantiation decides `{← unwrapShow p}` at a symbolic parameter (the sign test of `$clog2`'s argument or of a shift amount, a divisor's test for zero, ...; every value in it is wrapped to 32 bits, IEEE 1800-2023 §11.4, §11.6.1, §11.8.1), and `omega` could not decide it from the hypotheses in context (a theorem at a symbolic parameter needs premises that fix the decision and keep the values in it in range, e.g. `N < 2147483647` for `$clog2(N + 1)`)"
          skip := skip.push inst
          g := gN
          continue
      | none => throw e
    if ← tryRfl g then return
  throwError (pending?.getD m!"{tac}: {what}")

end

end LeanModels.Sv.CombView

/-- **Below this many sites the grouped route is not taken** (WP-LIN). Listing the related sites costs a weak head
normalization of the site list and of each site's reads, a fixed price that the avoided pairs only repay from a few sites on:
measured, a design of ONE site (`prio_enc`, the 256-entry `sbox_table`) pays 1.6 to 4.4 million heartbeats for nothing, and a
flat chain of five sites already saves 14% of its structure cost. Smaller designs are normalized as before. -/
def groupMinSites : Nat := 4

/-- **`rdWriters s.lsites` as an expression, with the proof of `rdWriters s.lsites = RW`** (WP-LIN, `CombViewGroup.lean`).
`sv` is the value of the summary, `sE` its expression: the tactic lists, natively and without `simp`, every site with its
reads and, for each read, the writers of the signal it reads; the sites and reads are the terms the weak head normal form of
`s.lsites` gives (so the kernel's `rfl` check of the equation is a comparison of the names). The rank and the coverage
obligations are stated over this list. -/
def rdWritersExpr (sv : LeanModels.Sv.CombView.Summary) (sE : Expr) : MetaM (Expr × Expr × Nat × Nat) := do
  let lsT := mkConst ``LeanModels.Sv.CombView.LSite
  let accT := mkConst ``LeanModels.Sv.CombView.Acc
  let listOf (t : Expr) := mkApp (mkConst ``List [Level.zero]) t
  let prodT (a b : Expr) := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) a b
  let prodMk (α β a b : Expr) := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) α β a b
  let names := sv.lsites.toArray.map fun l => l.site.tgt.name
  let rdNamesAll := sv.lsites.toArray.map fun l => l.site.rds.toArray.map fun r => r.name
  let n := names.size
  let sites ← listElemExprs (mkApp (mkConst ``LeanModels.Sv.CombView.Summary.lsites) sE)
  unless sites.size == n do throwError "sv_comb: the site list differs from the summary's"
  let rdT := prodT accT (listOf lsT)
  let eT := prodT lsT (listOf rdT)
  let mut entries : Array Expr := #[]
  let mut nReads := 0
  let mut nWriters := 0
  for i in [0:n] do
    let rs ← listElemExprs (mkApp (mkConst ``LeanModels.Sv.CombView.TSite.rds)
      (mkApp (mkConst ``LeanModels.Sv.CombView.LSite.site) sites[i]!))
    let rdNames := rdNamesAll[i]!
    unless rs.size == rdNames.size do throwError "sv_comb: the read list differs from the summary's"
    let mut qs : Array Expr := #[]
    for k in [0:rs.size] do
      let mut ws : Array Expr := #[]
      for j in [0:n] do
        if names[j]! == rdNames[k]! then ws := ws.push sites[j]!
      nReads := nReads + 1
      nWriters := nWriters + ws.size
      qs := qs.push (prodMk accT (listOf lsT) rs[k]! (← mkListLit lsT ws.toList))
    entries := entries.push (prodMk lsT (listOf rdT) sites[i]! (← mkListLit rdT qs.toList))
  let RW ← mkListLit eT entries.toList
  let hRW := mkApp2 (mkConst ``Eq.refl [Level.one]) (listOf eT) RW
  return (RW, hRW, nReads, nWriters)

/-- **The grouped route for the two quadratic structure obligations** (WP-LIN, `CombViewGroup.lean`). `g` is the goal
`s.DisjObl σ` or `s.RankObl ρ σ` / `s.LexObl κ σ` of the summary `s` (a closed term, evaluated as the value `sv`). Only
the pairs of sites that write the SAME signal, and the triples (site, read, writer of the signal read), can fail to hold
trivially; the tactic lists them natively (from the target names, no `simp`), assigns the lemma of `CombViewGroup` whose
`rfl` hypothesis the kernel checks once, and returns the new goal: the original obligation restricted to that list,
which the usual normalization then handles in time linear in the number of listed pairs. -/
def groupStructureGoal (sv : LeanModels.Sv.CombView.Summary) (g : MVarId) : MetaM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  let lsT := mkConst ``LeanModels.Sv.CombView.LSite
  let prodT (a b : Expr) := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) a b
  let prodMk (a b : Expr) (α β : Expr) := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) α β a b
  let names := sv.lsites.toArray.map fun l => l.site.tgt.name
  let n := names.size
  if ty.isAppOfArity ``LeanModels.Sv.CombView.Summary.DisjObl 2 then
    let sE := ty.appFn!.appArg!
    let σE := ty.appArg!
    let sites ← listElemExprs (mkApp (mkConst ``LeanModels.Sv.CombView.Summary.lsites) sE)
    unless sites.size == n do throwError "sv_structure: the site list differs from the summary's"
    let mut pairs : Array Expr := #[]
    for i in [0:n] do
      for j in [i+1:n] do
        if names[i]! == names[j]! then pairs := pairs.push (prodMk sites[i]! sites[j]! lsT lsT)
    let pT := prodT lsT lsT
    svGroupReport s!"sv_comb group: DisjObl, {pairs.size} same-signal pairs of {n} sites"
    let P ← mkListLit pT pairs.toList
    let listT := mkApp (mkConst ``List [Level.zero]) pT
    let hP := mkApp2 (mkConst ``Eq.refl [Level.one]) listT P
    let app := mkApp4 (mkConst ``LeanModels.Sv.CombView.Summary.disjObl_of_groups) sE σE P hP
    let hTy := (← whnf (← inferType app)).bindingDomain!
    let hNew ← mkFreshExprSyntheticOpaqueMVar hTy (← g.getTag)
    g.assign (mkApp app hNew)
    return hNew.mvarId!
  else
    -- `RankObl ρ σ` and `LexObl κ σ` unfold to `RankObl' R σ`
    let ty' ← match ← unfoldDefinition? ty with
      | some t => pure t.headBeta
      | none => pure ty
    unless ty'.isAppOfArity ``LeanModels.Sv.CombView.Summary.RankObl' 3 do
      throwError "sv_structure: not a rank obligation"
    let sE := ty'.appFn!.appFn!.appArg!
    let RE := ty'.appFn!.appArg!
    let σE := ty'.appArg!
    let (RW, hRW, nReads, nWriters) ← rdWritersExpr sv sE
    svGroupReport s!"sv_comb group: RankObl', {nReads} reads with {nWriters} writers of {n} sites"
    let app := mkApp5 (mkConst ``LeanModels.Sv.CombView.Summary.rankObl'_of_groups) sE RE σE RW hRW
    let hTy := (← whnf (← inferType app)).bindingDomain!
    let hNew ← mkFreshExprSyntheticOpaqueMVar hTy (← g.getTag)
    g.assign (mkApp app hNew)
    return hNew.mvarId!

/-- The simp lemmas that unfold the REPLICATION vocabulary (WP-B2 gate 4c: the counts of a site, `repAff`, the affine
reader behind it). They are passed to `simp` ONLY for a design that contains a replication (`Summary.hasRepl`), never named
in the tactics' own lists: a name in those lists costs about 21 units of heartbeats per `simp` call, on every proof. -/
def replSimpLemmas {m : Type → Type} [Monad m] [MonadQuotation m] :
    m (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  return #[← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.PExpr.rcounts),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.PExpr.consts),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.CombView.repCount),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.CombView.repAff),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.CombView.affOf?),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.CombView.affBin),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.CombView.affMul),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.CombView.affDiv),
    ← `(Lean.Parser.Tactic.simpLemma| List.isEmpty_nil),
    ← `(Lean.Parser.Tactic.simpLemma| List.isEmpty_cons)]

/-- `t` (a normalization step `at h`), preceded by the replication vocabulary when the design has a replication. -/
def withRepl {m : Type → Type} [Monad m] [MonadQuotation m] (hasRepl : Bool)
    (replL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) (h : Ident) (t : TSyntax `tactic) :
    m (TSyntax `tactic) :=
  if hasRepl then
    `(tactic| first | (simp only [$replL,*] at $h:ident; try $t:tactic) | $t:tactic)
  else pure t

/-- **A design with signed reads** (`PDesign.unsign`, `CombSigned.lean`). The tactics summarize the unsigned twin
`PDesign.unsign X.pdesign` and prove the theorem about the twin's instantiation; the goal about the design as written is
reached along `instantiateGD2_unsign_view`, whose hypotheses are the view's (shared named goals) plus the fragment,
width and bit-read obligations of `sv_equations` (`hfrag`, `hwid`, `hbit`). `extra` closes or normalizes those three:
it is supplied by `CombEqTactic.lean`, where the normalization of the width obligation lives. -/
structure TwinInfo where
  /-- The twin the theorems are about (a `PDesign` literal). -/
  design : Lean.Expr
  args : Lean.Expr
  /-- `D = D'` for the goal's design `D` (definitional): the family the wrapper's bridge is about. -/
  restate : Lean.Expr → MetaM Lean.Expr
  /-- The application of a comb theorem about the twin's family, wrapped into a proof about the goal's design. -/
  wrap : TSyntax `term → TacticM (TSyntax `term)
  /-- What the twin is the twin of, for the refusals. -/
  what : String
  /-- Where the first process the site recognizer refuses comes from in the design as written (`""`: no such process),
  for the refusal of a twin outside the fragment, whose site names are the twin's. -/
  origin : String := ""
  /-- The refusal text of a site of the twin's summary whose width contract fails at a sampled valuation (`""`: none),
  checked with the other sampled obligations (diagnostics only: `CombHier.twinWidthMsg`). -/
  widthBad : Summary → (String → Int) → String := fun _ _ => ""

structure SignedHook where
  extra : (Name → TacticM MVarId) → Summary → TacticM (List MVarId)
  /-- A twin other than the unsigned one (`CombHier.lean`: the flat twin of a design with module instances). -/
  twin? : Option TwinInfo := none

/-- The vocabulary of the unsigned twin, for the normalization of a summary computed from `PDesign.unsign X.pdesign`
(the summary `rfl` produces may keep the twin's fields unevaluated). -/
def unsignSimpLemmas {m : Type → Type} [Monad m] [MonadQuotation m] :
    m (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  return #[← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.PDesign.unsign),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.PProcess.unsign),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.PExpr.unsign),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.PExpr.unsignL),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.GenItem.unsign),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.GenItem.unsignL),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.CombView.unsignOp)]

/-- Whether a design has signed reads the tactics read through its unsigned twin (`PDesign.unsign d ≠ d`). -/
unsafe def hasSignedReads (pd : Lean.Expr) : MetaM Bool := do
  let e ← mkAppM ``BEq.beq #[mkApp (mkConst ``LeanModels.Sv.PDesign.unsign) pd, pd]
  return !(← evalExpr Bool (mkConst ``Bool) e)

/-- The application `tm` of a comb theorem about the twin's family, wrapped into a proof of the goal about the design
as written: `Eq.mpr (congrArg motive (instantiateGD2_unsign_view …)) tm`, the bridge's hypotheses the SAME named
goals as the view's (`?s`, `?env`, `?hs`, …). -/
def signedWrap (pd args : Lean.Expr) (tm : TSyntax `term) : TacticM (TSyntax `term) := do
  let g ← getMainGoal
  let gty ← instantiateMVars (← g.getType)
  let D := mkApp2 (mkConst ``LeanModels.Sv.PDesign.instantiateGD2) pd args
  let abs ← kabstract gty D
  unless abs.hasLooseBVars do
    throwError "sv_comb: internal error: the design `{D}` does not occur in the goal"
  let motive := Lean.mkLambda `D .default (mkConst ``LeanModels.Sv.Design2) abs
  let motiveT ← Term.exprToSyntax motive
  let pdT ← Term.exprToSyntax pd
  let argsT ← Term.exprToSyntax args
  `(Eq.mpr (congrArg $motiveT (LeanModels.Sv.CombEq.instantiateGD2_unsign_view (d := $pdT) (args := $argsT)
      (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1) (hag := ?hag) (hok := ?hok)
      (hauto := ?hauto) (hin := ?hin) (hfrag := ?hfrag) (hwid := ?hwid) (hbit := ?hbit))) $tm)

/-- Run the structural stage. (`unsafe`: it evaluates the recognizer on the design with
`evalExpr`, at tactic time only.) With `hook?` the design has signed reads and is read through its unsigned twin
(`SignedHook`). -/
unsafe def runSvStructure (rankStx? lexStx? usingStx? : Option Syntax) (hintOnly : Bool)
    (hook? : Option SignedHook := none) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    -- the bundle `CombDesign D ∧ Acyclic D` (WP-P): one application of `Summary.sound`, one round of
    -- obligations for both
    -- the triple `CombDesign D ∧ Acyclic D ∧ SharedObl X.pdesign args` (perf, CombShared.lean): the bundle, and the
    -- `auto`/`inRange` obligations packaged for `sv_equations`
    let isShared := ty.isAppOfArity ``And 2 &&
      ty.appFn!.appArg!.getAppFn.isConstOf ``LeanModels.Sv.CombDesign &&
      ty.appArg!.isAppOfArity ``And 2 &&
      ty.appArg!.appFn!.appArg!.getAppFn.isConstOf ``LeanModels.Sv.Acyclic &&
      ty.appArg!.appArg!.getAppFn.isConstOf ``LeanModels.Sv.CombView.SharedObl
    let isBoth := isShared || (ty.isAppOfArity ``And 2 &&
      ty.appFn!.appArg!.getAppFn.isConstOf ``LeanModels.Sv.CombDesign &&
      ty.appArg!.getAppFn.isConstOf ``LeanModels.Sv.Acyclic)
    let isComb := ty.getAppFn.isConstOf ``LeanModels.Sv.CombDesign
    let isAcyc := ty.getAppFn.isConstOf ``LeanModels.Sv.Acyclic || isBoth
    unless isComb || isAcyc do
      throwError "sv_structure: the goal must be `CombDesign (X.sem N)`, `Acyclic (X.sem N)`, their conjunction `CombDesign (X.sem N) ∧ Acyclic (X.sem N)`, or that conjunction with the shared obligations `∧ SharedObl X.pdesign [N]` (for `sv_equations`)"
    let dGoal := if isBoth then ty.appFn!.appArg!.appArg! else ty.appArg!
    let twin? := hook?.bind (·.twin?)
    let (pd, args, aliased) ← match twin? with
      | some tw => pure (tw.design, tw.args, false)
      | none => do
          let some r ← findGD2A dGoal 8
            | if (← isHD2Family dGoal 8) then throwError (hierarchyRefusal "sv_structure")
              else throwError "sv_structure: cannot read a `load_design_sv2` family (`X.sem N`) off the design in the goal"
          pure r
    let pdName? := headConst? pd
    if twin?.isNone && pdName?.isNone then
      throwError "sv_structure: the design is not a named constant"
    -- a design with signed reads is summarized through its unsigned twin (`SignedHook`), a design with module
    -- instances through its flat twin (`TwinInfo`)
    let pdS := if hook?.isSome && twin?.isNone then mkApp (mkConst ``LeanModels.Sv.PDesign.unsign) pd else pd
    let twinWhat := match twin? with
      | some tw => tw.what
      | none => "a design with signed reads (its summary is the unsigned twin's)"
    if hook?.isSome && usingStx?.isSome then
      throwError "sv_structure: `using hc` is not available for {twinWhat}; prove `CombDesign (X.sem N) ∧ Acyclic (X.sem N)` in one call"
    if hook?.isSome && isShared then
      throwError "sv_structure: the shared obligations `SharedObl X.pdesign [N]` are not available for {twinWhat}; prove `CombDesign (X.sem N) ∧ Acyclic (X.sem N)` and let `sv_equations` normalize its obligations"
    match ← evalSummary pdS with
    | .error msg =>
        let loc := match twin? with
          | some tw => if tw.origin.isEmpty then "" else s!" (in the flat twin of this design: {tw.origin})"
          | none => ""
        let rom ← evalExpr String (mkConst ``String) (mkApp (mkConst ``LeanModels.Sv.PDesign.wallNote) pdS)
        throwError "sv_structure: outside the supported fragment — {msg}{loc}{rom}"
    | .ok s =>
      if hintOnly then
        logInfo m!"{s.describe}"
        return
      -- structural facts, with the specific reason when one fails
      let probs := s.structProblems
      unless probs.isEmpty do
        throwError "sv_structure: structural check failed:\n  {"\n  ".intercalate probs}"
      -- the Nat variables of the arguments, and small sample values for them
      let fvs ← (fvarsOf args).filterM fun f => do
        return (← f.getType).isConstOf ``Nat
      let lb ← lowerBounds fvs
      let rankE? : Option Expr ← match rankStx? with
        | none => pure none
        | some stx => do
            let rty := Lean.mkForall `x BinderInfo.default (mkConst ``LeanModels.Sv.CombView.SiteId)
              (mkConst ``Nat)
            some <$> Tactic.elabTermEnsuringType stx rty
      let lexE? : Option Expr ← match lexStx? with
        | none => pure none
        | some stx => do
            let rty := Lean.mkForall `x BinderInfo.default (mkConst ``LeanModels.Sv.CombView.SiteId)
              (mkConst ``LeanModels.Sv.CombView.Key)
            some <$> Tactic.elabTermEnsuringType stx rty
      if usingStx?.isSome && !isAcyc then
        throwError "sv_structure: `using hc` is for an `Acyclic` goal (it supplies the one-driver obligation from `CombDesign`)"
      if usingStx?.isSome && isBoth then
        throwError "sv_structure: `using hc` is for an `Acyclic` goal alone; the conjunction `CombDesign ∧ Acyclic` derives the one-driver obligation itself"
      if isAcyc && rankE?.isNone && lexE?.isNone then
        throwError "sv_structure: an `Acyclic` goal needs a rank over site identities, e.g. `sv_structure (rank := rippleRank … …)` or a lexicographic key `sv_structure (lexRank := fun | .plain 0 => (0, 0, 0) | …)`; run `sv_structure?` to see the sites and the rank relation they must satisfy"
      -- sampling: genuine violations are reported with the offending sites
      for k in [lb, lb + 1, lb + 2, lb + 3, lb + 4] do
        let lits := fvs.map fun _ => (mkNatLit k)
        let argsK := args.replaceFVars (fvs.map mkFVar) lits
        let argVals ← evalArgs argsK
        let σ := s.val argVals
        let ctxMsg := s!"(sampled at {s.pnames} = {argVals}; a genuine violation, not a missing proof, unless your hypotheses exclude this point)"
        if let some m := s.accCounterexample σ then
          throwError "sv_structure: in-range obligation fails — {m} {ctxMsg}"
        if let some m := s.rangeCounterexample σ then
          throwError "sv_structure: in-range obligation fails — {m} {ctxMsg}"
        if let some m := s.disjCounterexample σ then
          throwError "sv_structure: {m} {ctxMsg}"
        if let some tw := twin? then
          let m := tw.widthBad s σ
          unless m.isEmpty do
            throwError "sv_structure: {m} {ctxMsg}"
        if let some re := rankE? then
          let reK := re.replaceFVars (fvs.map mkFVar) lits
          let ρ ← evalRank reK
          if let some m := s.rankCounterexample σ (fun w r => decide (ρ w < ρ r))
              (fun i => toString (ρ i)) then
            throwError "sv_structure: {m} {ctxMsg}{(s.rankReadNote σ (fun w r => decide (ρ w < ρ r))).getD ""}"
        if let some le := lexE? then
          let leK := le.replaceFVars (fvs.map mkFVar) lits
          let κ ← evalLex leK
          if let some m := s.rankCounterexample σ (fun w r => decide (KLt (κ w) (κ r)))
              (fun i => showKey (κ i)) then
            throwError "sv_structure: {m} {ctxMsg}{(s.rankReadNote σ (fun w r => decide (KLt (κ w) (κ r)))).getD ""}"
      -- the proof
      -- the alias-guarded family (`X.sem N`, ls-sv 7c9b7ac59): the goal is restated at the unguarded family the
      -- theorems are about, along `X.sem N = X.pdesign.instantiateGD2 [N]` (`aliasInertEq`), and so is `using hc`
      let mut usingStx? := usingStx?
      if aliased then
        let hA ← aliasInertEq "sv_structure" dGoal pd args
        replaceMainGoal [← rewriteDesign (← getMainGoal) hA]
        if let some u := usingStx? then
          let hcE ← Tactic.elabTerm u none
          usingStx? := some (← Term.exprToSyntax (← transportDesign hcE dGoal hA)).raw
      -- a design with module instances: the goal restated at the hierarchical family the bridge is about
      if let some tw := twin? then
        replaceMainGoal [← rewriteDesign (← getMainGoal) (← tw.restate dGoal)]
      let wrapT (tm : TSyntax `term) : TacticM (TSyntax `term) :=
        match twin? with
        | some tw => tw.wrap tm
        | none => if hook?.isSome then signedWrap pd args tm else pure tm
      let replL ← if s.hasRepl then replSimpLemmas else pure #[]
      let pdL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← match pdName? with
        | some pdName => do let pdId := mkIdent pdName; pure #[← `(Lean.Parser.Tactic.simpLemma| $pdId:ident)]
        | none => pure #[]
      let unsL ← if hook?.isSome && twin?.isNone then unsignSimpLemmas else pure #[]
      let preL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := pdL ++ replL ++ unsL
      -- the player's own rank/key function, if it is a named definition: unfold it
      let keyIds : Array Ident :=
        match (rankE?.orElse fun _ => lexE?) with
        | some e =>
            match e.getAppFn with
            | .const n _ => #[mkIdent n]
            | _ => #[]
        | none => #[]
      let keyLemmas ← keyIds.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
      let normR : TSyntax `tactic ←
        if s.hasRepl then `(tactic| (sv_norm [$keyLemmas,*]; (try simp only [$replL,*]); try sv_norm [$keyLemmas,*]))
        else `(tactic| sv_norm [$keyLemmas,*])
      if isComb then
        evalTactic (← `(tactic| refine $(← wrapT (← `(LeanModels.Sv.CombView.comb_view (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
            (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj))))))
      else if isBoth then
        if lexE?.isSome then
          let r ← match lexStx? with
            | some r => pure r
            | none => throwError "unreachable"
          let rT : TSyntax `term := ⟨r⟩
          let thm := mkIdent (if isShared then ``LeanModels.Sv.CombView.comb_lex_shared_view
            else ``LeanModels.Sv.CombView.comb_lex_view)
          evalTactic (← `(tactic| refine $(← wrapT (← `($thm:ident (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
              (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj)
              (κ := $rT) (hrank := ?hrank))))))
        else
          let r ← match rankStx? with
            | some r => pure r
            | none => throwError "unreachable"
          let rT : TSyntax `term := ⟨r⟩
          let thm := mkIdent (if isShared then ``LeanModels.Sv.CombView.comb_acyclic_shared_view
            else ``LeanModels.Sv.CombView.comb_acyclic_view)
          evalTactic (← `(tactic| refine $(← wrapT (← `($thm:ident (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
              (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj)
              (ρ := $rT) (hrank := ?hrank))))))
      else if lexE?.isSome then
        let r ← match lexStx? with
          | some r => pure r
          | none => throwError "unreachable"
        let rT : TSyntax `term := ⟨r⟩
        match usingStx? with
        | none =>
          evalTactic (← `(tactic| refine $(← wrapT (← `(LeanModels.Sv.CombView.lex_view (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
              (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj)
              (κ := $rT) (hrank := ?hrank))))))
        | some u =>
          let uT : TSyntax `term := ⟨u⟩
          evalTactic (← `(tactic| refine $(← wrapT (← `(LeanModels.Sv.CombView.lex_view_using (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
              (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hc := $uT)
              (κ := $rT) (hrank := ?hrank))))))
      else
        let r ← match rankStx? with
          | some r => pure r
          | none => throwError "unreachable"
        let rT : TSyntax `term := ⟨r⟩
        match usingStx? with
        | none =>
          evalTactic (← `(tactic| refine $(← wrapT (← `(LeanModels.Sv.CombView.acyclic_view (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
              (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj)
              (ρ := $rT) (hrank := ?hrank))))))
        | some u =>
          let uT : TSyntax `term := ⟨u⟩
          evalTactic (← `(tactic| refine $(← wrapT (← `(LeanModels.Sv.CombView.acyclic_view_using (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
              (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hc := $uT)
              (ρ := $rT) (hrank := ?hrank))))))
      -- name the new goals, close the structural hypotheses, keep the obligations
      let goals ← getGoals
      let find (n : Name) : TacticM MVarId := do
        for g in goals do
          if (← g.getTag).eraseMacroScopes == n then return g
        throwError "sv_structure: internal error: goal `{n}` not found"
      let closeWith (n : Name) (what : String) (tac : TSyntax `tactic) : TacticM Unit := do
        setGoals [← find n]
        try
          evalTactic tac
        catch e =>
          throwError "sv_structure: {what}\n{e.toMessageData}"
        unless (← getGoals).isEmpty do
          throwError "sv_structure: {what}"
      let closeDecide (n : Name) (what : String) : TacticM Unit := do
        setGoals [← find n]
        try
          closeByDecide (← getMainGoal) what
          setGoals []
        catch _ =>
          -- false (or not evaluable): the kernel decision, for its own report, as before WP-P
          closeWith n what (← `(tactic| decide +kernel))
      closeWith `hs "the recognizer's summary could not be computed by `rfl`" (← `(tactic| rfl))
      closeWith `harity "the number of arguments differs from the number of parameters" (← `(tactic| rfl))
      closeParamEnv "sv_structure" (← find `h1) (lift := s.hasCond)
      closeHag "sv_structure" (← find `hag) s args
      closeDecide `hok "the structural check failed"
      let mut out : Array MVarId := #[]
      let runOb (n : Name) (nm : String) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq)
          (grouped : Bool := false) : TacticM (List MVarId) := do
        let g0 ← find n
        -- WP-LIN: the obligations that are quadratic in the number of sites are first restricted to the sites
        -- that write the same signal (`groupStructureGoal`); a failure of that step keeps the original goal
        let g ← if grouped && groupMinSites ≤ s.lsites.length then
            (do
              let st ← saveState
              try
                groupStructureGoal s g0
              catch _ =>
                st.restore
                pure g0)
          else pure g0
        setGoals [g]
        svObProfile nm (evalTactic tac)
        let rest ← getGoals
        let k := rest.length
        let mut i := 0
        for g in rest do
          i := i + 1
          g.setTag (if k == 1 then Name.mkSimple nm else Name.mkSimple s!"{nm}_{i}")
        return rest
      -- A FLAT netlist (WP-P3b): when no site has a generate header and the goal mentions no free
      -- variable (no parameter), the four obligations (reads and windows in range, one driver per bit,
      -- rank) are closed statements about the site list. They are decided (`closeByDecide`) through
      -- `CombViewPlain` instead of being normalized by `simp` (two of them into one goal per pair of
      -- sites: quadratic in the number of sites). Anything else (a loop, a parameter, a statement that
      -- is false) takes the normalization below, unchanged.
      let closePlain (n : Name) (lem : Name) (what : String) : TacticM Bool := do
        tryClosePlain s (← find n) lem what
      unless (← closePlain `hauto ``LeanModels.Sv.CombView.Summary.autoObl_of_plain
          "an in-range fact of a flat netlist does not hold") do
        out := out ++ (← runOb `hauto "auto" (← `(tacticSeq|
          (try simp only [$preL,*])
          $normR:tactic
          repeat' refine And.intro ?_ ?_
          all_goals first | (intros; omega) | skip))).toArray
      unless (← closePlain `hin ``LeanModels.Sv.CombView.Summary.inRangeObl_of_plain
          "the in-range obligation of a flat netlist does not hold") do
        out := out ++ (← runOb `hin "inRange" (← `(tacticSeq|
          (try simp only [$preL,*])
          $normR:tactic
          repeat' refine And.intro ?_ ?_))).toArray
      if usingStx?.isNone then
        unless (← closePlain `hdisj ``LeanModels.Sv.CombView.Summary.disjObl_of_plain
            "the one-driver obligation of a flat netlist does not hold") do
          out := out ++ (← runOb `hdisj "driverDisjoint" (← `(tacticSeq|
            (try simp only [$preL,*])
            $normR:tactic
            repeat' refine And.intro ?_ ?_)) (grouped := true)).toArray
      if isAcyc then
        unless (← closePlain `hrank ``LeanModels.Sv.CombView.Summary.rankObl'_of_plain
            "the rank obligation of a flat netlist does not hold") do
          out := out ++ (← runOb `hrank "rankDecreases" (← `(tacticSeq|
            (try simp only [$preL,*])
            $normR:tactic
            repeat' refine And.intro ?_ ?_)) (grouped := true)).toArray
      if let some hook := hook? then
        out := out ++ (← hook.extra find s).toArray
      setGoals out.toList

declare_syntax_cat svRankCat
syntax "(" &"rank" " := " term ")" : svRankCat
syntax "(" &"lexRank" " := " term ")" : svRankCat

/-- `sv_structure` — see the module docstring. -/
syntax (name := svStructure) "sv_structure" (svRankCat)? (" using " term)? : tactic

/-- `sv_structure?` prints the families, site identities and the required rank relation. -/
syntax (name := svStructureQ) "sv_structure?" : tactic

@[tactic svStructure] unsafe def evalSvStructure : Tactic := fun stx => do
  let usingStx? : Option Syntax := if stx[2].isNone then none else some stx[2][1]
  if stx[1].isNone then
    withDeepRec (runSvStructure none none usingStx? false)
  else
    let cl := stx[1][0]
    if cl[1].getAtomVal == "lexRank" then withDeepRec (runSvStructure none (some cl[3]) usingStx? false)
    else withDeepRec (runSvStructure (some cl[3]) none usingStx? false)

@[tactic svStructureQ] unsafe def evalSvStructureQ : Tactic := fun _ => withDeepRec (runSvStructure none none none true)

/-! ## `sv_interface` (WP-P, P1): the ports of a design of the fragment

```
theorem add_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  sv_interface
```

proves the interface conjunct of a task statement (`t.Interface N (X.sem N)`: the design's input and
output ports are exactly `t.inputs N` and `t.outputs N`, names, order and widths) for a design the
recognizer reads, from the profile `hc : CombDesign (X.sem N)` in the context (the product of
`sv_structure`). Nothing of the soundness machinery is visible: the declarations of `X.sem N` are the
recognizer's (`decls_view`, whose hypotheses `rfl` and `decide` close: the parameter stage and the
structural check), and what remains is the arithmetic of the widths, which the tactic closes with
`simp` and `omega`. It generalizes the 23-line recipe that every proof carried until WP-P (the
`Summary.sound`/`σL`/`Aff.eval` incantation of svgolf/PROVING.md §2.2) and, unlike it, does not
re-derive the in-range obligations the profile already stands for. Designs with localparams need no
change: the valuation is `Summary.val`. -/

/-- Run the interface stage. -/
unsafe def runSvInterface : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    unless ty.isApp && ty.getAppNumArgs ≥ 3 && ty.getAppFn.isConst do
      throwError "sv_interface: the goal must be a task's interface statement `t.Interface N (X.sem N)`"
    let D := ty.appArg!
    let some (pd, args, aliased) ← findGD2A D 8
      | if (← isHD2Family D 8) then throwError (hierarchyRefusal "sv_interface")
        else throwError "sv_interface: cannot read a `load_design_sv2` family (`X.sem N`) off the design in the goal"
    let some pdName := headConst? pd
      | throwError "sv_interface: the design is not a named constant"
    -- the profile `CombDesign (X.sem N)` in the context
    let mut hc? : Option Expr := none
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if t.getAppFn.isConstOf ``LeanModels.Sv.CombDesign && hc?.isNone then
        if ← isDefEq t.appArg! D then hc? := some d.toExpr
    let some hcE := hc?
      | throwError "sv_interface: no hypothesis `CombDesign (X.sem N)` in the context (prove it with `sv_structure`, or take it from the `CombDesign ∧ Acyclic` bundle)"
    match ← evalSummary pd with
    | .error msg => throwError "sv_interface: outside the supported fragment — {msg}"
    | .ok s =>
      let probs := s.structProblems
      unless probs.isEmpty do
        throwError "sv_interface: structural check failed:\n  {"\n  ".intercalate probs}"
      let pdId := mkIdent pdName
      let keyI := mkIdent `key
      -- the goal over the unfolded family, so that `key` rewrites it syntactically; the alias-guarded family
      -- (`X.sem N`, ls-sv 7c9b7ac59) is restated at the unguarded one (`aliasInertEq`), and so is the profile
      let D' := mkApp2 (mkConst ``LeanModels.Sv.PDesign.instantiateGD2) pd args
      let hcI ← if aliased then
          let hA ← aliasInertEq "sv_interface" D pd args
          replaceMainGoal [← rewriteDesign goal hA]
          Term.exprToSyntax (← transportDesign hcE D hA)
        else
          let ty' := ty.replace fun e => if e == D then some D' else none
          replaceMainGoal [← goal.replaceTargetDefEq ty']
          Term.exprToSyntax hcE
      evalTactic (← `(tactic|
        have $keyI:ident := LeanModels.Sv.CombView.decls_view (s := ?s) (env := ?env) (hs := ?hs)
            (h1 := ?h1) (hag := ?hag) (hok := ?hok) (hc := $hcI)))
      let goals ← getGoals
      let named : List Name := [`s, `env, `hs, `h1, `hag, `hok]
      let mut bodyGoal? : Option MVarId := none
      for g in goals do
        unless named.contains (← g.getTag).eraseMacroScopes do
          if bodyGoal?.isNone then bodyGoal? := some g
      let some bodyGoal := bodyGoal?
        | throwError "sv_interface: internal error: no main goal after introducing the declarations"
      let find (n : Name) : TacticM MVarId := do
        for g in goals do
          if (← g.getTag).eraseMacroScopes == n then return g
        throwError "sv_interface: internal error: goal `{n}` not found"
      let closeWith (n : Name) (what : String) (tac : TSyntax `tactic) : TacticM Unit := do
        setGoals [← find n]
        try
          evalTactic tac
        catch e =>
          throwError "sv_interface: {what}\n{e.toMessageData}"
        unless (← getGoals).isEmpty do
          throwError "sv_interface: {what}"
      let closeDecide (n : Name) (what : String) : TacticM Unit := do
        setGoals [← find n]
        try
          closeByDecide (← getMainGoal) what
          setGoals []
        catch _ =>
          -- false (or not evaluable): the kernel decision, for its own report, as before WP-P
          closeWith n what (← `(tactic| decide +kernel))
      closeWith `hs "the recognizer's summary could not be computed by `rfl`" (← `(tactic| rfl))
      closeParamEnv "sv_interface" (← find `h1) (lift := s.hasCond)
      closeHag "sv_interface" (← find `hag) s args
      closeDecide `hok "the structural check failed"
      setGoals [bodyGoal]
      -- unfold the statement and the task, and evaluate the declarations' widths
      let headId := mkIdent ty.getAppFn.constName!
      let taskIds : Array Ident :=
        match ty.getArg! 0 with
        | .const n _ => #[mkIdent n]
        | _ => #[]
      let taskLemmas ← taskIds.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
      try
        -- (`SvGolf` is not imported here: the names are built without macro scopes, resolved in the user's file)
        let inPorts := mkIdent `SvGolf.inputPorts
        let outPorts := mkIdent `SvGolf.outputPorts
        evalTactic (← `(tactic| simp only [$headId:ident, $inPorts:ident, $outPorts:ident]))
        evalTactic (← `(tactic| rw [$keyI:ident]))
        evalTactic (← `(tactic|
          sv_simp [LeanModels.Sv.CombView.DeclT.toDecl, LeanModels.Sv.CombView.DeclT.width,
            LeanModels.Sv.CombView.dimsW, LeanModels.Sv.CombView.Aff.eval,
            LeanModels.Sv.CombView.Aff.evalTerms, LeanModels.Sv.CombView.Aff.evalQs, LeanModels.Sv.CombView.Aff.sub,
            LeanModels.Sv.CombView.Aff.neg, LeanModels.Sv.CombView.Aff.negTerms, LeanModels.Sv.CombView.Aff.negQs,
            LeanModels.Sv.CombView.Aff.add, LeanModels.Sv.CombView.Aff.var,
            LeanModels.Sv.CombView.Aff.const, LeanModels.Sv.CombView.Aff.scale,
            LeanModels.Sv.CombView.Aff.scaleTerms, LeanModels.Sv.CombView.Aff.scaleQs, LeanModels.Sv.CombView.σL,
            LeanModels.Sv.CombView.Summary.val, LeanModels.Sv.CombView.lpEnv,
            LeanModels.Sv.CombView.CE.eval, List.lookup_cons, List.lookup_nil, $pdId:ident,
            List.zip_cons_cons, List.zip_nil_right, List.lookup_cons_self, Option.getD_some,
            $taskLemmas,*] <;> omega))
      catch e =>
        throwError "sv_interface: the declared ports do not match the task's interface (or the width arithmetic is outside `omega`'s reach):\n{e.toMessageData}"

/-- `sv_interface` — see the comment above. -/
syntax (name := svInterface) "sv_interface" : tactic

@[tactic svInterface] unsafe def evalSvInterface : Tactic := fun _ => withDeepRec runSvInterface
