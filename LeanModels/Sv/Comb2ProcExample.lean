import LeanModels.Sv.Comb2Proc
import LeanModels.Sv.CombGuard2
import LeanModels.Sv.CombGuard2Sound

/-!
# `always_comb` in the combinational settle theorem, end to end (`LeanModels.Sv` — Design2)

The acceptance example of `Comb2Proc.lean`: designs whose logic is an
`always_comb` block of blocking assignments, proved correct under `⊨₂`
together with `Terminates2`. Each design is hand-built in exactly the shape
the sv-0.2 instantiation produces (`agree.lean` in
`Examples/system-verilog/sem2/{fa_comb_proc, mux4_case, latch_comb,
onehot_dec, addsub_comb, rbw_comb, rbw_held}` checks that each SV source
instantiates to its design, and the `harness/sv/cases2.json` rows of the
first five names run them against Icarus).

1. **`faDesign`** — a full adder as ONE `always_comb` with a temporary and
   an `if`/`else`:

       always_comb begin
         t = a ^ b;
         s = t ^ cin;
         if (t) cout = cin;
         else   cout = a;
       end

   Proved: every run completes (`fa_terminates`), and on every snapshot
   with known 1-bit inputs `s = a ^ b ^ cin` and `cout` is the majority —
   the statement `Comb2Example` proves of the gate-level full adder
   (`fa_correct`, `fa_correct_stim`).
2. **`muxDesign`** — a 4-way multiplexer with a `default`-then-`case`
   body:

       always_comb begin
         y = 1'b0;
         case (sel)
           2'd0: y = d[0];  2'd1: y = d[1];  2'd2: y = d[2];
           default: y = d[3];
         endcase
       end

   Proved: termination and `y = d[sel]` for every known `sel`, `d`
   (`mux_correct`, through `bv2_cases`).
3. **`latchDesign`** — `always_comb if (en) q = d;`, a latch. The body
   executes symbolically (`latch_symExec`), but its equation reads `q`
   itself, so the lowering refuses it (`latch_refused`, the self-read check
   `SymState.selfReadFree`); that equation taken as an assign is not
   acyclic either (`latch_not_acyclic`).
4. **`decDesign`** — a one-hot decoder in the "default, then override one
   bit" style (`y = 4'b0000; if (en) case (sel) k: y[k] = 1'b1; …`): every
   bit write lands INSIDE the already written `y` and is spliced into its
   default (`Expr2.splice`). Proved: termination and
   `y = en ? 1 << sel : 0` for every known `sel`, `en` (`dec_correct`).
5. **`asDesign N`** — an `N`-bit adder/subtractor with a zero flag
   (`if (sub) y = a - b; else y = a + b; z = ~|y;`), at EVERY width `N`:
   the symbolic execution (`as_symExec`) and the profile are evaluated by
   `simp` with `N` a variable; termination (`as_terminates`) and
   `y = sub ? a - b : a + b`, `z = (y == 0)` (`as_correct`) for all `N`.
6. **`rbwDesign`, `heldDesign`** — self-reads, refused by the lowering
   (`rbw_refused`, `held_refused`): `y = t; t = a;` and
   `if (c) t = a; y = t; t = b;`. On both, the settle semantics of `run2`
   (pinned by `#guard`) and Icarus 12 disagree, because a simulator never
   re-runs an `always_comb` block on its own writes. Since 2026-10-28 (WP4)
   the always_comb self-read guard (`CombGuard2.lean`) refuses both at
   instantiation, so no `name.sem` runs them: `rbw_guard`, `held_guard`
   (section 7), and the fixtures' `agree.lean` pin `load_design_sv2`'s
   refusal of the SV sources.
7. **The self-read guard on these designs** (WP4): every body the
   lowering accepts here is admitted by the guard (`fa_admits`,
   `mux_admits`, `dec_admits`, `as_admits` at every `N`), and so is the
   latch (`latch_admits`: one run of a latch is its own fixpoint); the two
   self-reads are refused with the guard's message. The guard and the
   lowering's `SymState.selfReadFree` are different tests: the guard is
   path-sensitive and admits latches, the lowering refuses them; the
   lowering looks through values that never reach an equation, the guard
   does not — `deadDesign` (`y = t; y = a; t = b;`, the read of `t` dead)
   and `sameDesign` (`if (t) y = a; else y = a; t = b;`, the condition
   irrelevant) lower, but the guard refuses them (`dead_lowers`,
   `dead_refused`, `same_lowers`, `same_refused`): on such a body the proof
   API meets the refusal through `name.sem` (its `lowerComb` is `none`
   there), never a design the guard let through.

## The proof pattern

* The symbolic execution of the body (`Stmt2.symExec`) is computed by `rfl`
  and written down as `faSym` — one expression per written window, over the
  pre-state: `t = a ^ b`, `s = (a ^ b) ^ cin`, and
  `cout = ((|(a ^ b)) === 1) ? cin : a` (the `if` became a known-bit guard).
  The lowered design (`Design2.lowerComb`) is `faLow`, also by `rfl`.
* The profile of the lowered design is a set of closed-data checks
  (`CombDesign.of_single`, each obligation by `decide`): the body's windows
  are in range and pairwise disjoint and it writes no input. The
  acyclicity certificate of a one-process design comes for free from the
  lowering's self-read check (`Acyclic.of_lowerComb_single`).
* `Models2.of_combProc_pointwise` reduces `⊨₂` to one state solving the
  lowered equations; `CombEqs.symWindow_ident` reads one window's equation
  back; `sv2_known` evaluates it on known inputs; what remains is `BitVec 1`
  algebra (`fa_cout_maj`, a case split on the three input bits).

No `bv_decide`, no `native_decide`; `decide` only on closed data (design
facts, and the eight closed instances of a 1-bit identity).
-/

namespace LeanModels.Sv

namespace Comb2ProcExample

/-! ## 1. The full adder as one `always_comb` -/

/-- The body `t = a ^ b; s = t ^ cin; if (t) cout = cin; else cout = a;`. -/
def faBody : Stmt2 := .block #[
  .blockingAssign (.ident "t") (.binary .xor (.ident "a") (.ident "b")),
  .blockingAssign (.ident "s") (.binary .xor (.ident "t") (.ident "cin")),
  .ifStmt (.ident "t") (.blockingAssign (.ident "cout") (.ident "cin"))
    (some (.blockingAssign (.ident "cout") (.ident "a")))]

/-- The full adder: ports, the temporary `t`, one `always_comb` (the
declaration order of the sv-0.2 instantiation: ports, then module
variables). -/
def faDesign : Design2 where
  name := "fa_comb_proc"
  decls := #[
    { name := "a", width := 1, isInput := true },
    { name := "b", width := 1, isInput := true },
    { name := "cin", width := 1, isInput := true },
    { name := "s", width := 1, isOutput := true },
    { name := "cout", width := 1, isOutput := true },
    { name := "t", width := 1 }]
  processes := #[.alwaysComb faBody]

/-- The equation of `t`: `a ^ b` (at the target width). -/
def eT : Expr2 := .resize 1 (.binary .xor (.ident "a") (.ident "b"))

/-- The equation of `s`: the read of `t` is replaced by its equation. -/
def eS : Expr2 := .resize 1 (.binary .xor eT (.ident "cin"))

/-- The equation of `cout`: the `if` on `t` is a known-bit guard on `t`'s
equation. -/
def eCout : Expr2 := .ternary eT.ifGuard (.resize 1 (.ident "cin")) (.resize 1 (.ident "a"))

/-- **The symbolic execution of the body**: one equation per written
window. -/
def faSym : SymState := [(("t", 0, 1), eT), (("s", 0, 1), eS), (("cout", 0, 1), eCout)]

theorem fa_symExec : faBody.symExec faDesign [] = some faSym := rfl

/-- The lowered design: the `always_comb` replaced by
`assign {t, s, cout} = {eT, eS, eCout}`. -/
def faLow : Design2 := { faDesign with processes := #[faSym.toAssign] }

theorem fa_lower : faDesign.lowerComb = some faLow := rfl

/-- The lowered design is in the comb profile (closed-data checks). -/
theorem faLow_comb : CombDesign faLow :=
  CombDesign.of_single rfl (by decide) (SymState.target_windows _ _) (by decide) (by decide)
    (by decide) rfl (by decide) (by decide) (by decide)

/-- The lowered equations read only the inputs: the certificate comes for
free from the lowering's self-read check (one process). -/
theorem faLow_acyclic : Acyclic faLow := Acyclic.of_lowerComb_single fa_lower rfl

/-- The carry `if` is the majority function (the eight closed instances of
three bits). -/
theorem fa_cout_maj (x y z : BitVec 1) :
    (if BitVec.ofBool (!decide (x = y)) = 1#1 then z else x) = x &&& y ||| x &&& z ||| y &&& z := by
  have hb : ∀ v : BitVec 1, BitVec.ofBool (v.getLsbD 0) = v := by
    intro v
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain rfl : i = 0 := by omega
    simp
  rw [← hb x, ← hb y, ← hb z]
  cases x.getLsbD 0 <;> cases y.getLsbD 0 <;> cases z.getLsbD 0 <;> decide

/-- **The full adder, one settled state**: in a state solving the lowered
equations, with the comb shape and known 1-bit inputs, `s` is the sum and
`cout` the majority. -/
theorem fa_settled {st : SvState} (heqs : CombEqs faLow st) (hs : StateShape faLow st)
    {x y z : BitVec 1}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "cin" = some (LVec.ofBitVec z)) :
    SvState.lookup st "s" = some (LVec.ofBitVec (x ^^^ y ^^^ z)) ∧
      SvState.lookup st "cout" = some (LVec.ofBitVec (x &&& y ||| x &&& z ||| y &&& z)) := by
  have hS : evalPure2 st eS = .ok (LVec.ofBitVec (x ^^^ y ^^^ z)) := by
    sv2_known [eS, eT, ha, hb, hc]
  have hC : evalPure2 st eCout = .ok (LVec.ofBitVec (x &&& y ||| x &&& z ||| y &&& z)) := by
    rw [← fa_cout_maj]
    sv2_known [eCout, eT, Expr2.ifGuard, ha, hb, hc]
  exact ⟨CombEqs.symWindow_ident fa_lower faLow_comb heqs hs (i := 0) rfl fa_symExec
      (by simp [faSym]) rfl hS,
    CombEqs.symWindow_ident fa_lower faLow_comb heqs hs (i := 0) rfl fa_symExec
      (by simp [faSym]) rfl hC⟩

/-- **Non-vacuity**: every run of the `always_comb` full adder completes,
under every schedule and every stimulus. -/
theorem fa_terminates : Terminates2 faDesign :=
  Terminates2.of_lowerComb_acyclic fa_lower faLow_comb faLow_acyclic

/-- **`always_comb` full-adder correctness** (snapshot form): on every
snapshot of every completed run whose inputs hold known 1-bit values, `s`
holds the sum and `cout` the majority — `Comb2Example.fa_correct`'s
statement for the gate-level adder. -/
theorem fa_correct : faDesign ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState),
    tr[c]? = some st → ∀ x y z : BitVec 1,
      SvState.lookup st "a" = some (LVec.ofBitVec x) →
      SvState.lookup st "b" = some (LVec.ofBitVec y) →
      SvState.lookup st "cin" = some (LVec.ofBitVec z) →
      SvState.lookup st "s" = some (LVec.ofBitVec (x ^^^ y ^^^ z)) ∧
      SvState.lookup st "cout" = some (LVec.ofBitVec (x &&& y ||| x &&& z ||| y &&& z)) :=
  Models2.of_combProc_pointwise fa_lower faLow_comb fun _ heqs hs _ _ _ ha hb hc =>
    fa_settled heqs hs ha hb hc

/-- **`always_comb` full-adder correctness** (stimulus form): whenever cycle
`c`'s stimulus entry drives `a`, `b`, `cin` with known 1-bit values,
snapshot `c` carries their sum on `s` and their majority on `cout`. -/
theorem fa_correct_stim : faDesign ⊨₂ spec2 fun stim tr => ∀ (c : Nat) (inputs st : SvState),
    stim[c]? = some inputs → tr[c]? = some st → ∀ x y z : BitVec 1,
      SvState.lookup inputs "a" = some (LVec.ofBitVec x) →
      SvState.lookup inputs "b" = some (LVec.ofBitVec y) →
      SvState.lookup inputs "cin" = some (LVec.ofBitVec z) →
      SvState.lookup st "s" = some (LVec.ofBitVec (x ^^^ y ^^^ z)) ∧
      SvState.lookup st "cout" = some (LVec.ofBitVec (x &&& y ||| x &&& z ||| y &&& z)) := by
  apply Models2.of_combProc_inputs fa_lower faLow_comb
  intro stim tr h c inputs st hi hc x y z ha hb hci
  obtain ⟨heqs, hs, hin⟩ := h c st hc
  have hmem : ∀ n, n = "a" ∨ n = "b" ∨ n = "cin" → n ∈ faLow.inputNames.toList := by
    rintro n (rfl | rfl | rfl) <;> decide
  exact fa_settled heqs hs
    (hin inputs hi "a" (hmem _ (by simp)) _ ha)
    (hin inputs hi "b" (hmem _ (by simp)) _ hb)
    (hin inputs hi "cin" (hmem _ (by simp)) _ hci)

/-- Non-vacuity, packaged: under every schedule and stimulus a completed run
EXISTS, and it satisfies the correctness statement. -/
example (σ : ScheduleOracle) (stim : List SvState) :
    ∃ tr, Runs2 faDesign σ stim tr ∧ ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ x y z : BitVec 1,
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec z) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x ^^^ y ^^^ z)) ∧
        SvState.lookup st "cout" = some (LVec.ofBitVec (x &&& y ||| x &&& z ||| y &&& z)) :=
  Models2.exists_of_terminates fa_terminates fa_correct σ stim

/-! ### Concrete runs: the interpreter runs the body itself

`run2` executes the `always_comb` body (not the lowering) under two
schedules; the last two rows drive `x`/`z` inputs: `t = x`, so `if (t)`
takes the `else` branch (`cout = a`), and `s` is `x`. The lowered design
produces the same traces (`Runs2.lowerComb_iff`). -/

private def faStim : List SvState :=
  [[("a", .lit "0"), ("b", .lit "0"), ("cin", .lit "0")],
   [("a", .lit "1"), ("b", .lit "0"), ("cin", .lit "1")],
   [("a", .lit "1"), ("b", .lit "1"), ("cin", .lit "0")],
   [("a", .lit "1"), ("b", .lit "1"), ("cin", .lit "1")],
   [("a", .lit "0"), ("b", .lit "1"), ("cin", .lit "0")],
   [("a", .lit "x"), ("b", .lit "1"), ("cin", .lit "1")],
   [("a", .lit "1"), ("b", .lit "z"), ("cin", .lit "0")]]

private def faView (st : SvState) : String × String :=
  (SvState.showSignal st "s", SvState.showSignal st "cout")

#guard (run2 faDesign σ_src 64 faStim).toOption.map (·.map faView) ==
  some [("0", "0"), ("0", "1"), ("0", "1"), ("1", "1"), ("1", "0"), ("x", "x"), ("x", "1")]
#guard (run2 faDesign σ_rev 64 faStim).toOption.map (·.map faView) ==
  some [("0", "0"), ("0", "1"), ("0", "1"), ("1", "1"), ("1", "0"), ("x", "x"), ("x", "1")]
#guard (run2 faLow σ_src 64 faStim).toOption.map (·.map faView) ==
  (run2 faDesign σ_src 64 faStim).toOption.map (·.map faView)

/-! ## 2. A `case` multiplexer with a default assignment -/

/-- The body `y = 1'b0; case (sel) 0: y = d[0]; 1: y = d[1]; 2: y = d[2];
default: y = d[3]; endcase`. -/
def muxBody : Stmt2 := .block #[
  .blockingAssign (.ident "y") (.lit (.lit "0")),
  .caseStmt (.ident "sel")
    #[.mk #[.lit (.lit "00")] (.blockingAssign (.ident "y") (.slice (.ident "d") 0 1)),
      .mk #[.lit (.lit "01")] (.blockingAssign (.ident "y") (.slice (.ident "d") 1 1)),
      .mk #[.lit (.lit "10")] (.blockingAssign (.ident "y") (.slice (.ident "d") 2 1))]
    (some (.blockingAssign (.ident "y") (.slice (.ident "d") 3 1))) false .none]

/-- The multiplexer. -/
def muxDesign : Design2 where
  name := "mux4_case"
  decls := #[
    { name := "sel", width := 2, isInput := true },
    { name := "d", width := 4, isInput := true },
    { name := "y", width := 1, isOutput := true }]
  processes := #[.alwaysComb muxBody]

/-- The arm guard `(sel === pat) | 1'b0` of a one-pattern arm. -/
def muxHit (pat : String) : Expr2 :=
  Expr2.anyGuard false (.ident "sel") [.lit (.lit pat)]

/-- Bit `k` of `d`, at the target width. -/
def muxBit (k : Nat) : Expr2 := .resize 1 (.slice (.ident "d") k 1)

/-- The equation of `y`: the arms nest in source order, the default last. -/
def muxE : Expr2 :=
  .ternary (muxHit "00") (muxBit 0)
    (.ternary (muxHit "01") (muxBit 1) (.ternary (muxHit "10") (muxBit 2) (muxBit 3)))

/-- **The symbolic execution of the body**: the default `y = 1'b0` is
overwritten on every path, so it disappears. -/
def muxSym : SymState := [(("y", 0, 1), muxE)]

theorem mux_symExec : muxBody.symExec muxDesign [] = some muxSym := rfl

/-- The lowered multiplexer. -/
def muxLow : Design2 := { muxDesign with processes := #[muxSym.toAssign] }

theorem mux_lower : muxDesign.lowerComb = some muxLow := rfl

theorem muxLow_comb : CombDesign muxLow :=
  CombDesign.of_single rfl (by decide) (SymState.target_windows _ _) (by decide) (by decide)
    (by decide) rfl (by decide) (by decide) (by decide)

theorem muxLow_acyclic : Acyclic muxLow := Acyclic.of_lowerComb_single mux_lower rfl

/-- **Non-vacuity**: every run of the multiplexer completes. -/
theorem mux_terminates : Terminates2 muxDesign :=
  Terminates2.of_lowerComb_acyclic mux_lower muxLow_comb muxLow_acyclic

/-- A 2-bit vector is one of four values. -/
theorem bv2_cases (s : BitVec 2) : s = 0#2 ∨ s = 1#2 ∨ s = 2#2 ∨ s = 3#2 := by
  have h : s.toNat < 4 := s.isLt
  simp only [BitVec.toNat_eq, BitVec.toNat_ofNat]
  omega

/-- **The multiplexer selects** (snapshot form): on every snapshot with known
`sel` and `d`, `y` holds bit `sel` of `d`. -/
theorem mux_correct : muxDesign ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState),
    tr[c]? = some st → ∀ (s : BitVec 2) (dv : BitVec 4),
      SvState.lookup st "sel" = some (LVec.ofBitVec s) →
      SvState.lookup st "d" = some (LVec.ofBitVec dv) →
      SvState.lookup st "y" = some (LVec.ofBitVec (BitVec.ofBool (dv.getLsbD s.toNat))) := by
  refine Models2.of_combProc_pointwise mux_lower muxLow_comb fun st heqs hs s dv hsel hd => ?_
  have h0 : LVec.lit "00" = LVec.ofBitVec 0#2 := by decide
  have h1 : LVec.lit "01" = LVec.ofBitVec 1#2 := by decide
  have h2 : LVec.lit "10" = LVec.ofBitVec 2#2 := by decide
  have hv : evalPure2 st muxE = .ok (LVec.ofBitVec (BitVec.ofBool (dv.getLsbD s.toNat))) := by
    sv2_known [muxE, muxHit, muxBit, Expr2.anyGuard, Expr2.hitGuard, hsel, hd, h0, h1, h2]
    rcases bv2_cases s with rfl | rfl | rfl | rfl <;> simp
  exact CombEqs.symWindow_ident mux_lower muxLow_comb heqs hs (i := 0) rfl mux_symExec
    (by simp [muxSym]) rfl hv

#guard (run2 muxDesign σ_src 64
    [[("sel", .lit "00"), ("d", .lit "0101")], [("sel", .lit "01"), ("d", .lit "0101")],
     [("sel", .lit "10"), ("d", .lit "0100")], [("sel", .lit "11"), ("d", .lit "1000")],
     [("sel", .lit "x1"), ("d", .lit "1111")]]).toOption.map
      (·.map fun st => SvState.showSignal st "y") ==
  some ["1", "0", "1", "1", "1"]

/-! ## 3. A latch is refused by the lowering -/

/-- `always_comb begin if (en) q = d; end` — `q` holds when `en` is
false. -/
def latchDesign : Design2 where
  name := "latch_comb"
  decls := #[
    { name := "en", width := 1, isInput := true },
    { name := "d", width := 1, isInput := true },
    { name := "q", width := 1, isOutput := true }]
  processes := #[.alwaysComb
    (.block #[.ifStmt (.ident "en") (.blockingAssign (.ident "q") (.ident "d")) none])]

/-- The latch's equation: `q = ((|en) === 1) ? d : q` — the held branch
reads `q`'s own pre-state value (`Win.held`). -/
def latchSym : SymState :=
  [(("q", 0, 1), .ternary (Expr2.ifGuard (.ident "en")) (.resize 1 (.ident "d"))
    (Win.held ("q", 0, 1)))]

/-- The body executes symbolically: the latch is not refused for its
shape. -/
theorem latch_symExec :
    (Stmt2.block #[.ifStmt (.ident "en") (.blockingAssign (.ident "q") (.ident "d")) none]).symExec
      latchDesign [] = some latchSym := rfl

/-- **The lowering refuses the latch**: its equation reads the window it
writes, so `SymState.selfReadFree` fails. -/
theorem latch_refused : latchDesign.lowerComb = none := rfl

/-- The latch's equation taken as a continuous assign. -/
def latchLow : Design2 := { latchDesign with processes := #[latchSym.toAssign] }

/-- **Nor is that assign acyclic**: its one process reads the window it
writes. -/
theorem latch_not_acyclic : ¬ Acyclic latchLow := by
  rintro ⟨rank, h⟩
  have := h 0 0 latchSym.target latchSym.rhs latchSym.target latchSym.rhs ("q", 0, 1) rfl rfl
    (by rw [SymState.target_wins]; simp [latchSym])
    ⟨.win "q" 0 1, by decide, by decide⟩
  exact Nat.lt_irrefl _ this

-- The interpreter agrees that `q` holds while `en` is low.
#guard (run2 latchDesign σ_src 64
    [[("en", .lit "1"), ("d", .lit "1")], [("en", .lit "0"), ("d", .lit "0")],
     [("en", .lit "1"), ("d", .lit "0")]]).toOption.map
      (·.map fun st => SvState.showSignal st "q") ==
  some ["1", "1", "0"]

/-! ## 4. Default, then override one bit: a one-hot decoder -/

/-- The body `y = 4'b0000; if (en) case (sel) 0: y[0] = 1'b1; 1: y[1] = 1'b1;
2: y[2] = 1'b1; 3: y[3] = 1'b1; endcase` (no `default`: an unknown `sel`
matches no arm and `y` keeps its default). -/
def decBody : Stmt2 := .block #[
  .blockingAssign (.ident "y") (.lit (.lit "0000")),
  .ifStmt (.ident "en")
    (.block #[.caseStmt (.ident "sel")
      #[.mk #[.lit (.lit "00")] (.blockingAssign (.slice "y" 0 1) (.lit (.lit "1"))),
        .mk #[.lit (.lit "01")] (.blockingAssign (.slice "y" 1 1) (.lit (.lit "1"))),
        .mk #[.lit (.lit "10")] (.blockingAssign (.slice "y" 2 1) (.lit (.lit "1"))),
        .mk #[.lit (.lit "11")] (.blockingAssign (.slice "y" 3 1) (.lit (.lit "1")))]
      none false .none])
    none]

/-- The one-hot decoder. -/
def decDesign : Design2 where
  name := "onehot_dec"
  decls := #[
    { name := "sel", width := 2, isInput := true },
    { name := "en", width := 1, isInput := true },
    { name := "y", width := 4, isOutput := true }]
  processes := #[.alwaysComb decBody]

/-- `y`'s default, at the target width. -/
def decZero : Expr2 := .resize 4 (.lit (.lit "0000"))

/-- The default with bit `k` overridden by `1'b1`: the symbolic write of a
bit INSIDE the already written `y` (`Expr2.splice`). -/
def decSet (k : Nat) : Expr2 := Expr2.splice decZero 4 k 1 (.resize 1 (.lit (.lit "1")))

/-- The arm guard of a one-pattern arm on `sel`. -/
def decHit (pat : String) : Expr2 := Expr2.anyGuard false (.ident "sel") [.lit (.lit pat)]

/-- The equation of `y`. -/
def decE : Expr2 :=
  .ternary (Expr2.ifGuard (.ident "en"))
    (.ternary (decHit "00") (decSet 0) (.ternary (decHit "01") (decSet 1)
      (.ternary (decHit "10") (decSet 2) (.ternary (decHit "11") (decSet 3) decZero))))
    decZero

/-- **The symbolic execution of the body**: one window, the whole `y`. -/
def decSym : SymState := [(("y", 0, 4), decE)]

theorem dec_symExec : decBody.symExec decDesign [] = some decSym := rfl

/-- The lowered decoder. -/
def decLow : Design2 := { decDesign with processes := #[decSym.toAssign] }

theorem dec_lower : decDesign.lowerComb = some decLow := rfl

theorem decLow_comb : CombDesign decLow :=
  CombDesign.of_single rfl (by decide) (SymState.target_windows _ _) (by decide) (by decide)
    (by decide) rfl (by decide) (by decide) (by decide)

theorem decLow_acyclic : Acyclic decLow := Acyclic.of_lowerComb_single dec_lower rfl

/-- **Non-vacuity**: every run of the decoder completes. -/
theorem dec_terminates : Terminates2 decDesign :=
  Terminates2.of_lowerComb_acyclic dec_lower decLow_comb decLow_acyclic

/-- **The decoder is one-hot** (snapshot form): on every snapshot with known
`sel` and `en`, `y` is `1 << sel` when `en` is set and `0` otherwise. -/
theorem dec_correct : decDesign ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState),
    tr[c]? = some st → ∀ (s : BitVec 2) (b : Bool),
      SvState.lookup st "sel" = some (LVec.ofBitVec s) →
      SvState.lookup st "en" = some (LVec.ofBitVec (BitVec.ofBool b)) →
      SvState.lookup st "y" = some (LVec.ofBitVec (if b then 1#4 <<< s.toNat else 0#4)) := by
  refine Models2.of_combProc_pointwise dec_lower decLow_comb fun st heqs hs s b hsel hen => ?_
  have h0 : LVec.lit "00" = LVec.ofBitVec 0#2 := by decide
  have h1 : LVec.lit "01" = LVec.ofBitVec 1#2 := by decide
  have h2 : LVec.lit "10" = LVec.ofBitVec 2#2 := by decide
  have h3 : LVec.lit "11" = LVec.ofBitVec 3#2 := by decide
  have hz : LVec.lit "0000" = LVec.ofBitVec 0#4 := by decide
  have ho : LVec.lit "1" = LVec.ofBitVec 1#1 := by decide
  have hv : evalPure2 st decE = .ok (LVec.ofBitVec (if b then 1#4 <<< s.toNat else 0#4)) := by
    sv2_known [decE, decHit, decSet, decZero, Expr2.splice, Expr2.anyGuard, Expr2.hitGuard,
      Expr2.ifGuard, hsel, hen, h0, h1, h2, h3, hz, ho]
    rcases bv2_cases s with rfl | rfl | rfl | rfl <;> cases b <;> decide
  exact CombEqs.symWindow_ident dec_lower decLow_comb heqs hs (i := 0) rfl dec_symExec
    (by simp [decSym]) rfl hv

#guard (run2 decDesign σ_src 64
    [[("sel", .lit "00"), ("en", .lit "1")], [("sel", .lit "10"), ("en", .lit "1")],
     [("sel", .lit "11"), ("en", .lit "0")], [("sel", .lit "x1"), ("en", .lit "1")],
     [("sel", .lit "01"), ("en", .lit "x")]]).toOption.map
      (·.map fun st => SvState.showSignal st "y") ==
  some ["0001", "0100", "0000", "0000", "0000"]

/-! ## 5. Every width: an `N`-bit adder/subtractor with a zero flag

    always_comb begin
      if (sub) y = a - b;
      else     y = a + b;
      z = ~|y;              // reads the y just written
    end

`N` stays a variable throughout: the symbolic execution is evaluated by
`simp` (its window checks compare symbolic widths, which `rfl` cannot
decide), and so are the profile obligations. -/

/-- The body. -/
def asBody : Stmt2 := .block #[
  .ifStmt (.ident "sub")
    (.blockingAssign (.ident "y") (.binary .sub (.ident "a") (.ident "b")))
    (some (.blockingAssign (.ident "y") (.binary .add (.ident "a") (.ident "b")))),
  .blockingAssign (.ident "z") (.reduce .nor (.ident "y"))]

/-- The adder/subtractor at width `N`. -/
def asDesign (N : Nat) : Design2 where
  name := "addsub_comb"
  decls := #[
    { name := "a", width := N, isInput := true },
    { name := "b", width := N, isInput := true },
    { name := "sub", width := 1, isInput := true },
    { name := "y", width := N, isOutput := true },
    { name := "z", width := 1, isOutput := true }]
  processes := #[.alwaysComb asBody]

/-- The equation of `y`: the `if` as a known-bit guard on `sub`. -/
def eY (N : Nat) : Expr2 :=
  .ternary (Expr2.ifGuard (.ident "sub"))
    (.resize N (.binary .sub (.ident "a") (.ident "b")))
    (.resize N (.binary .add (.ident "a") (.ident "b")))

/-- The equation of `z`: the read of `y` is `y`'s equation. -/
def eZ (N : Nat) : Expr2 := .resize 1 (.reduce .nor (eY N))

/-- The symbolic execution of the body, at width `N`. -/
def asSym (N : Nat) : SymState := [(("y", 0, N), eY N), (("z", 0, 1), eZ N)]

theorem as_declWidth_y (N : Nat) : (asDesign N).declWidth "y" = some N := by
  simp [Design2.declWidth, asDesign]

theorem as_declWidth_z (N : Nat) : (asDesign N).declWidth "z" = some 1 := by
  simp [Design2.declWidth, asDesign]

theorem as_symNames (N : Nat) : (asDesign N).symNames = ["a", "b", "sub", "y", "z"] := rfl

/-- **The symbolic execution at every width.** -/
theorem as_symExec (N : Nat) : asBody.symExec (asDesign N) [] = some (asSym N) := by
  simp [asBody, Stmt2.symExec, Stmt2.symExecList, Stmt2.symExecOpt, Expr2.wfB,
    Expr2.symSubst, SymState.readWhole, SymState.writesName, SymState.findWin, Lhs2.symWin,
    Lhs2.window?, as_declWidth_y, as_declWidth_z, SymState.write, SymState.findCover,
    SymState.overlapsAny, SymState.join, SymState.joinWins, Win.allDisjoint,
    SymState.lookupOr, Expr2.joinIte, Expr2.same, as_symNames, Expr2.idents,
    Expr2.unsupportedFree, asSym, eY, eZ, Win.overlaps, Win.contains]

/-- The lowered adder/subtractor. -/
def asLow (N : Nat) : Design2 := { asDesign N with processes := #[(asSym N).toAssign] }

/-- The equations read none of the windows the body writes (`y`, `z`). -/
theorem as_selfReadFree (N : Nat) : (asSym N).selfReadFree = true := by
  simp [SymState.selfReadFree, asSym, eY, eZ, Expr2.ifGuard, Expr2.reads, Expr2.listReads,
    ReadWin.overlaps]

theorem as_lower (N : Nat) : (asDesign N).lowerComb = some (asLow N) := by
  unfold Design2.lowerComb
  rw [show (asDesign N).processes.toList = [.alwaysComb asBody] from rfl]
  simp only [Design2.lowerProcs, Process2.lowerComb, as_symExec, as_selfReadFree, if_true,
    Option.map_some, Option.bind_some]
  rfl

theorem asLow_declWidth (N : Nat) (n : String) :
    (asLow N).declWidth n = (asDesign N).declWidth n := rfl

theorem asLow_comb (N : Nat) : CombDesign (asLow N) :=
  CombDesign.of_single rfl (by simp [asLow, asDesign]) (SymState.target_windows _ _)
    (by simp [asSym, asLow_declWidth, as_declWidth_y, as_declWidth_z])
    (by simp [asSym, asLow, asDesign, Design2.inputNames])
    (by simp [asSym, Win.allDisjoint, Win.overlaps]) rfl
    (by simp [SymState.rhs, asSym, eY, eZ, Expr2.ifGuard, Expr2.idents, Expr2.listIdents,
      asLow, asDesign])
    (by simp [asLow, asDesign])
    (by simp [asLow, asDesign])

theorem asLow_acyclic (N : Nat) : Acyclic (asLow N) :=
  Acyclic.of_lowerComb_single (as_lower N) rfl

/-- **Non-vacuity at every width**: every run completes. -/
theorem as_terminates (N : Nat) : Terminates2 (asDesign N) :=
  Terminates2.of_lowerComb_acyclic (as_lower N) (asLow_comb N) (asLow_acyclic N)

/-- **The adder/subtractor, one settled state, at every width.** -/
theorem as_settled {N : Nat} {st : SvState} (heqs : CombEqs (asLow N) st)
    (hs : StateShape (asLow N) st) {x y : BitVec N} {c : Bool}
    (ha : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hb : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hc : SvState.lookup st "sub" = some (LVec.ofBitVec (BitVec.ofBool c))) :
    SvState.lookup st "y" = some (LVec.ofBitVec (if c then x - y else x + y)) ∧
      SvState.lookup st "z" =
        some (LVec.ofBitVec (BitVec.ofBool (decide ((if c then x - y else x + y) = 0#N)))) := by
  have hcond : (BitVec.ofBool (!decide (BitVec.ofBool c = 0#1)) = 1#1) = (c = true) := by
    cases c <;> decide
  have hY : evalPure2 st (eY N) = .ok (LVec.ofBitVec (if c then x - y else x + y)) := by
    sv2_known [eY, Expr2.ifGuard, ha, hb, hc, hcond]
  have hZ : evalPure2 st (eZ N) =
      .ok (LVec.ofBitVec (BitVec.ofBool (decide ((if c then x - y else x + y) = 0#N)))) := by
    sv2_known [eZ, eY, Expr2.ifGuard, ha, hb, hc, hcond]
  exact ⟨CombEqs.symWindow_ident (as_lower N) (asLow_comb N) heqs hs (i := 0) rfl (as_symExec N)
      (by simp [asSym]) (as_declWidth_y N) hY,
    CombEqs.symWindow_ident (as_lower N) (asLow_comb N) heqs hs (i := 0) rfl (as_symExec N)
      (by simp [asSym]) (as_declWidth_z N) hZ⟩

/-- **`always_comb` adder/subtractor correctness, every `N`**: on every
snapshot with known `a`, `b`, `sub`, `y` is `a - b` or `a + b` (mod `2^N`) as
`sub` says, and the flag `z` is set exactly when `y` is zero. -/
theorem as_correct (N : Nat) : asDesign N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState),
    tr[c]? = some st → ∀ (x y : BitVec N) (s : Bool),
      SvState.lookup st "a" = some (LVec.ofBitVec x) →
      SvState.lookup st "b" = some (LVec.ofBitVec y) →
      SvState.lookup st "sub" = some (LVec.ofBitVec (BitVec.ofBool s)) →
      SvState.lookup st "y" = some (LVec.ofBitVec (if s then x - y else x + y)) ∧
      SvState.lookup st "z" =
        some (LVec.ofBitVec (BitVec.ofBool (decide ((if s then x - y else x + y) = 0#N)))) :=
  Models2.of_combProc_pointwise (as_lower N) (asLow_comb N) fun _ heqs hs _ _ _ ha hb hc =>
    as_settled heqs hs ha hb hc

#guard (run2 (asDesign 4) σ_src 64
    [[("a", .lit "0101"), ("b", .lit "0011"), ("sub", .lit "0")],
     [("a", .lit "0101"), ("b", .lit "0011"), ("sub", .lit "1")],
     [("a", .lit "0011"), ("b", .lit "0011"), ("sub", .lit "1")],
     [("a", .lit "1111"), ("b", .lit "0001"), ("sub", .lit "0")],
     [("a", .lit "0101"), ("b", .lit "0011"), ("sub", .lit "x")]]).toOption.map
      (·.map fun st => (SvState.showSignal st "y", SvState.showSignal st "z")) ==
  some [("1000", "0"), ("0010", "0"), ("0000", "1"), ("0000", "1"), ("1000", "0")]

/-! ## 6. Self-reads are refused

A body that reads one of its own windows before writing it, or reads a value
a join kept for a window the body later overwrites, is outside the profile.
The settle semantics re-runs such a block until nothing changes (the
`#guard`s below pin what `run2` computes, which is also what Yosys 0.53
`proc` synthesizes). An event-driven simulator runs the block once per
wake-up, and the block's own writes never wake it (IEEE 1800-2023
§9.2.2.2.1), so Icarus 12 shows `y` one input change behind on both
designs. The lowering refuses both (`SymState.selfReadFree`), so nothing is
proved about them through this API. `run2` itself still runs them with the
settle answer: that divergence from the standard's event semantics is
recorded in `docs/sv-charter.md` (2026-10-27). -/

/-- `y = t; t = a;` — `t` is read before it is written. -/
def rbwBody : Stmt2 := .block #[
  .blockingAssign (.ident "y") (.ident "t"),
  .blockingAssign (.ident "t") (.ident "a")]

/-- The design of `Examples/system-verilog/sem2/rbw_comb`. -/
def rbwDesign : Design2 where
  name := "rbw_comb"
  decls := #[
    { name := "a", width := 2, isInput := true },
    { name := "y", width := 2, isOutput := true },
    { name := "t", width := 2 }]
  processes := #[.alwaysComb rbwBody]

/-- The body executes symbolically; the shape is not what is refused. -/
theorem rbw_symExec_isSome : (rbwBody.symExec rbwDesign []).isSome = true := rfl

/-- **Refused**: `y`'s equation reads the pre-state `t`, a window the body
writes. -/
theorem rbw_refused : rbwDesign.lowerComb = none := rfl

-- The settle semantics gives `y = a`; Icarus 12 gives the previous `a`.
#guard (run2 rbwDesign σ_src 64
    [[("a", .lit "00")], [("a", .lit "01")], [("a", .lit "10")], [("a", .lit "11")]]).toOption.map
      (·.map fun st => SvState.showSignal st "y") ==
  some ["00", "01", "10", "11"]

/-- `if (c) t = a; y = t; t = b;` — on the `c = 0` path `y` reads the value
`t` held before the block ran, and the block then overwrites `t`. -/
def heldBody : Stmt2 := .block #[
  .ifStmt (.ident "c") (.blockingAssign (.ident "t") (.ident "a")) none,
  .blockingAssign (.ident "y") (.ident "t"),
  .blockingAssign (.ident "t") (.ident "b")]

/-- The design of `Examples/system-verilog/sem2/rbw_held`. -/
def heldDesign : Design2 where
  name := "rbw_held"
  decls := #[
    { name := "c", width := 1, isInput := true },
    { name := "a", width := 2, isInput := true },
    { name := "b", width := 2, isInput := true },
    { name := "y", width := 2, isOutput := true },
    { name := "t", width := 2 }]
  processes := #[.alwaysComb heldBody]

/-- The body executes symbolically; the shape is not what is refused. -/
theorem held_symExec_isSome : (heldBody.symExec heldDesign []).isSome = true := rfl

/-- **Refused**: `y`'s equation holds `t`'s pre-state value (`Win.held`) on
the `c = 0` path, and the body writes `t`. A check that exempted held values
would accept this body, on which Icarus disagrees with the settle answer. -/
theorem held_refused : heldDesign.lowerComb = none := rfl

-- The settle semantics gives `y = c ? a : b`; Icarus 12 gives the previous
-- `b` while `c` is low.
#guard (run2 heldDesign σ_src 64
    [[("c", .lit "0"), ("a", .lit "00"), ("b", .lit "01")],
     [("c", .lit "0"), ("a", .lit "00"), ("b", .lit "10")],
     [("c", .lit "1"), ("a", .lit "11"), ("b", .lit "10")]]).toOption.map
      (·.map fun st => SvState.showSignal st "y") ==
  some ["01", "10", "11"]

/-! ## 7. The self-read guard (WP4, `CombGuard2.lean`)

`instProcess2` passes every instantiated `always_comb` body through
`combGuardProc` at the module's declared widths (`Design2.combWd`). The
bodies of sections 1–5 are admitted — the proof API's designs are never
refused — and so is the latch of section 3 (one run of a latch is already
its own fixpoint, `runCombProcess2_alwaysComb_idem_of_admits`). The two
self-reads of section 6 are refused with the guard's message. -/

theorem fa_admits : faBody.combAdmits faDesign.combWd = true := by decide

theorem mux_admits : muxBody.combAdmits muxDesign.combWd = true := by decide

theorem dec_admits : decBody.combAdmits decDesign.combWd = true := by decide

/-- The latch the lowering refuses is admitted by the guard. -/
theorem latch_admits :
    (Stmt2.block #[.ifStmt (.ident "en") (.blockingAssign (.ident "q") (.ident "d")) none]).combAdmits
      latchDesign.combWd = true := by decide

/-- **The justification theorem at the latch** (`CombGuard2Sound.lean`):
on a shaped state, running the latch body again on the state its own run
produced changes nothing — the one run a simulator makes per wake-up is the
fixpoint the settle semantics computes. (This import also keeps
`CombGuard2Sound` under the default `Examples` build, through the
`agree.lean` files that import this module.) -/
theorem latch_idem {st r : SvState} {f : Nat}
    (hs : CombGuard.Shaped latchDesign.combWd st)
    (h : runCombProcess2 f st
      (.alwaysComb (Stmt2.block #[.ifStmt (.ident "en") (.blockingAssign (.ident "q") (.ident "d")) none]))
      = .ok r) :
    runCombProcess2 f r
      (.alwaysComb (Stmt2.block #[.ifStmt (.ident "en") (.blockingAssign (.ident "q") (.ident "d")) none]))
      = .ok r :=
  runCombProcess2_alwaysComb_idem_of_admits latch_admits hs h

/-- The adder/subtractor at EVERY width: each read the walk compares is on a
different signal than the bits written after it, so `simp` decides it with
`N` a variable. -/
theorem as_admits (N : Nat) : asBody.combAdmits (asDesign N).combWd = true := by
  simp [Stmt2.combAdmits, asBody, Design2.combWd, asDesign, Stmt2.combViol, Stmt2.listCombViol,
    Stmt2.optCombViol, Stmt2.mayW, Stmt2.optMayW, Stmt2.listMayW, Stmt2.mustW, Stmt2.optMustW,
    Lhs2.mayW, Lhs2.mustW, Lhs2.rdW, Expr2.rdW, CombGuard.readsViol, CombGuard.whole,
    CombGuard.BWin.inter, CombGuard.BWin.sub, CombGuard.BWin.subAll, CombGuard.interL,
    List.lookup]

/-- **`y = t; t = a;` is refused** with the guard's message on all of `t`. -/
theorem rbw_guard :
    combGuardProc rbwDesign.combWd rbwBody =
      .unsupported "AlwaysComb:self-read" (selfReadMsg ("t", 0, 2)) :=
  combGuardProc_of_viol (by decide)

/-- **`if (c) t = a; y = t; t = b;` is refused** (the `c = 0` path). -/
theorem held_guard :
    combGuardProc heldDesign.combWd heldBody =
      .unsupported "AlwaysComb:self-read" (selfReadMsg ("t", 0, 2)) :=
  combGuardProc_of_viol (by decide)

/-- `y = t; y = a; t = b;` — the read of `t` is dead (`y` is overwritten). -/
def deadBody : Stmt2 := .block #[
  .blockingAssign (.ident "y") (.ident "t"),
  .blockingAssign (.ident "y") (.ident "a"),
  .blockingAssign (.ident "t") (.ident "b")]

def deadDesign : Design2 where
  name := "dead_read"
  decls := #[
    { name := "a", width := 2, isInput := true },
    { name := "b", width := 2, isInput := true },
    { name := "y", width := 2, isOutput := true },
    { name := "t", width := 2 }]
  processes := #[.alwaysComb deadBody]

/-- The lowering accepts the dead read (no equation reads `t`) … -/
theorem dead_lowers : deadDesign.lowerComb.isSome = true := rfl

/-- … the guard refuses it: the read happens before `t = b` on the path. -/
theorem dead_refused : deadBody.combAdmits deadDesign.combWd = false := by decide

/-- `if (t) y = a; else y = a; t = b;` — the condition cannot matter. -/
def sameBody : Stmt2 := .block #[
  .ifStmt (.ident "t") (.blockingAssign (.ident "y") (.ident "a"))
    (some (.blockingAssign (.ident "y") (.ident "a"))),
  .blockingAssign (.ident "t") (.ident "b")]

def sameDesign : Design2 where
  name := "same_branches"
  decls := #[
    { name := "a", width := 2, isInput := true },
    { name := "b", width := 2, isInput := true },
    { name := "y", width := 2, isOutput := true },
    { name := "t", width := 2 }]
  processes := #[.alwaysComb sameBody]

/-- The lowering accepts it (the join of two equal branches drops the guard
on `t`) … -/
theorem same_lowers : sameDesign.lowerComb.isSome = true := rfl

/-- … the guard refuses it: the condition reads `t` before `t = b`. -/
theorem same_refused : sameBody.combAdmits sameDesign.combWd = false := by decide

/-! ## Axiom pins

Standard axioms only. The `#guard_msgs` wrappers make the build fail if any
of these drifts. -/

/--
info: 'LeanModels.Sv.Comb2ProcExample.fa_terminates' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fa_terminates

/--
info: 'LeanModels.Sv.Comb2ProcExample.fa_correct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fa_correct

/--
info: 'LeanModels.Sv.Comb2ProcExample.fa_correct_stim' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fa_correct_stim

/--
info: 'LeanModels.Sv.Comb2ProcExample.mux_terminates' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mux_terminates

/--
info: 'LeanModels.Sv.Comb2ProcExample.mux_correct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mux_correct

/--
info: 'LeanModels.Sv.Comb2ProcExample.latch_not_acyclic' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms latch_not_acyclic

/--
info: 'LeanModels.Sv.Comb2ProcExample.dec_terminates' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dec_terminates

/--
info: 'LeanModels.Sv.Comb2ProcExample.dec_correct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms dec_correct

/--
info: 'LeanModels.Sv.Comb2ProcExample.as_terminates' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms as_terminates

/--
info: 'LeanModels.Sv.Comb2ProcExample.as_correct' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms as_correct

/--
info: 'LeanModels.Sv.Comb2ProcExample.latch_refused' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms latch_refused

/--
info: 'LeanModels.Sv.Comb2ProcExample.rbw_refused' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rbw_refused

/--
info: 'LeanModels.Sv.Comb2ProcExample.held_refused' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms held_refused

/--
info: 'LeanModels.Sv.runCombProcess2_alwaysComb_idem' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms runCombProcess2_alwaysComb_idem

/--
info: 'LeanModels.Sv.Acyclic.of_lowerComb_single' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Acyclic.of_lowerComb_single

/--
info: 'LeanModels.Sv.Comb2ProcExample.as_admits' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms as_admits

/--
info: 'LeanModels.Sv.Comb2ProcExample.latch_idem' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms latch_idem

end Comb2ProcExample

end LeanModels.Sv
