import LeanModels.Go

/-!
# The rung-3 exemplar: `bigmod.bitLen`, and the model agrees with `gc`

**A real function, chosen by census — not a fixture written to be easy.**
`docs/backlog/go.md` §G6 searched the standard library for functions the
walker could execute, filtered to those that RETURN a value and do real
arithmetic, and this is what came out. Its source, verbatim from
`src/crypto/internal/fips140/bigmod/nat.go` (Go 1.25.6), comments and all:

    // bitLen is a version of bits.Len that only leaks the bit length of n, but not
    // its value. bits.Len and bits.LeadingZeros use a lookup table for the
    // low-order bits on some architectures.
    func bitLen(n uint) int {
        len := 0
        // We assume, here and elsewhere, that comparison to zero is constant time
        // with respect to different non-zero values.
        for n != 0 {
            len++
            n >>= 1
        }
        return len
    }

FIPS-140 crypto code — a better provenance than anything this lane could
have written.

**THE ORACLE'S PROVENANCE, so the printed column survives its
generator.** The expected values in §3 were produced by compiling exactly
the function above into a `main` that prints `"%d %d\n"` for each input,
and running it:

    $ go version    # go1.25.6 darwin/arm64
    $ go build -o bl main.go && ./bl

An audit noted that a vendored source marked *"NOT compiled as part of
this repository"* shipped the column without the command that made it.
The command is now here, the Go version is pinned, and the inputs are the
list in §3 — so the column is reproducible from this file alone. Reproduced under the cite-and-paraphrase law;
BSD-3-Clause, "Copyright 2009 The Go Authors", per
`docs/go-charter.md` §1.4's ruling that the in-tree copies are taken under
the repository's single instrument rather than the website's CC-BY-4.0.

**It is quoted HERE rather than vendored as a sibling `.go` file, and that
is a build-cost decision measured rather than guessed.** `tools/triad.sh`'s
`path_targets` maps `Examples/*.lean` to its own precise module but sends
every OTHER `Examples/` path to the whole `Examples` library — so a
reference file that nothing builds and no module reads widened the last
tenure's target from four Go modules to the entire library, and the build
went from 91 seconds to 37 minutes. `--build-target` cannot narrow it
(it UNIONs, never replaces). Quoting the source costs nothing and keeps
the tenure scoped.

## What is claimed here, and what is not

The rows below are a **differential claim**: the model, executed in Lean's
kernel, produces the same integer as the compiled function did on the same
input. The expected column was not derived — it was **produced by running
the real `gc`-compiled function** and pasted in, which is the only way the
comparison means anything.

It is NOT a proof that `bitLen` is correct. That statement — `bitLen n` is
the number of significant bits of `n` — is an induction over the loop and
is this lane's next theorem, not this inch's. What these rows establish is
the thing that has to come first: **the model and the toolchain agree on
this function's behaviour.**

## What the exemplar needed, and why the census picked the operators

Nothing here was added because it seemed useful. `>>=` forced compound
assignment and the shift operators; the `for n != 0` form forced a
condition-only loop; and the function boundary forced calls, which
§G6 measured as blocking **73.3%** of the files rung 1 already reaches.
-/

namespace Examples.go.bitlen

open LeanModels LeanModels.Go

/-- Go's `uint` is 64-bit on the censused platform. The width is a profile
input, not a constant of the language — `docs/go-charter.md` §7.3. -/
def uintK : IntKind := IntKind.uint64
def intK : IntKind := IntKind.int64

private def u (n : Int) : Expr := .lit (GoVal.mkInt uintK n)
private def i (n : Int) : Expr := .lit (GoVal.mkInt intK n)

/-- `bitLen`'s body, transcribed statement for statement. The comment in
the middle of the real loop is a comment; everything else is here. -/
def bitLenBody : List Stmt :=
  [ .declare "len" (i 0),
    .forS none (some (.binary .ne (.ident "n") (u 0))) none
      [ .incDec "len" true,
        .assignOp .shr "n" (u 1) ],
    .ret (some (.ident "len")) ]

/-- The program: one function, one parameter. -/
def prog : FuncTable := [("bitLen", ["n"], bitLenBody)]

/-- Run `bitLen` on a concrete input and read the integer back out. -/
def bitLen (n : Int) : Option Int :=
  match (callFunction prog 4096 "bitLen" [GoVal.mkInt uintK n]) ({} : GoWorld) with
  | .ok (.ok (.intV _ r), _) => some r
  | _ => none

/-! ## §1 THE SPEC HALF — the mathematics of `bitLen`, no interpreter

STMT-65 / `docs/statement-cookbook.md` §6: a theorem that can be stated
about the mathematics SHOULD be. Nothing in this section mentions
`execStmt`, `GoM`, a world or fuel, so all of it recompiles unchanged if
the walker is redefined.

`bitLenSpec` is what the Go loop computes, written as mathematics: shift
right until zero, counting. The two theorems are the CHARACTERISATION —
`bitLenSpec n` really is the number of significant bits, bracketed from
both sides. Together they say `2^(k-1) ≤ n < 2^k` for `k = bitLenSpec n`,
which is the definition of bit length and not a restatement of the code. -/

def bitLenSpec : Nat → Nat
  | 0 => 0
  | n + 1 => bitLenSpec ((n + 1) / 2) + 1
decreasing_by omega

@[go_spec] theorem bitLenSpec_zero : bitLenSpec 0 = 0 := by simp [bitLenSpec]

@[go_spec] theorem bitLenSpec_pos {n : Nat} (h : 0 < n) :
    bitLenSpec n = bitLenSpec (n / 2) + 1 := by
  match n, h with
  | k + 1, _ => rw [bitLenSpec]

@[go_spec] theorem bitLenSpec_lt (n : Nat) : n < 2 ^ bitLenSpec n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [bitLenSpec]
    | k + 1 =>
      have hh : (k + 1) / 2 < k + 1 := by omega
      have hrec := ih ((k + 1) / 2) hh
      rw [bitLenSpec_pos (by omega : 0 < k + 1), Nat.pow_succ]
      omega

@[go_spec] theorem bitLenSpec_le {n : Nat} (h : 0 < n) : 2 ^ (bitLenSpec n - 1) ≤ n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, h with
    | k + 1, _ =>
      rw [bitLenSpec_pos (by omega : 0 < k + 1)]
      simp only [Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos ((k + 1) / 2) with hz | hp
      · rw [hz, bitLenSpec_zero]; simp
      · have hh : (k + 1) / 2 < k + 1 := by omega
        have hrec := ih ((k + 1) / 2) hh hp
        have hb : 1 ≤ bitLenSpec ((k + 1) / 2) := by
          rw [bitLenSpec_pos hp]; omega
        have hsplit : bitLenSpec ((k+1)/2) - 1 + 1 = bitLenSpec ((k+1)/2) := by omega
        calc 2 ^ bitLenSpec ((k + 1) / 2)
            = 2 ^ (bitLenSpec ((k+1)/2) - 1) * 2 := by
              rw [← Nat.pow_succ]; congr 1; omega
          _ ≤ ((k + 1) / 2) * 2 := by exact Nat.mul_le_mul_right 2 hrec
          _ ≤ k + 1 := by omega


/-! ## §1b THE LOOP'S STEP LEMMAS — the walker, proved through a mutation

`docs/backlog/go.md` §G8 recorded the loop induction as blocked and §G10
cleared the reduction blocker with the seam. These are what the seam
bought: the **first proofs in this lane that step the walker through a
write**, and they are where §1.3b's frame predicates and `Obs.lean`'s
`go_run` meet on one goal.

They are stated about the loop's own pieces, so they mention the
interpreter and sit in the interpreter half. -/

/-- The loop's invariant: `n` and `len` live at DISTINCT addresses and
hold the values the mathematics says they should. The distinctness is not
bookkeeping — it is exactly what `wRead_wStore_other` needs, and without
it `len++` could not be shown to leave `n` alone. -/
structure Inv (w : GoWorld) (an al : Addr) (v l : Nat) : Prop where
  ne : an ≠ al
  ln : wLookup w "n" = some an
  ll : wLookup w "len" = some al
  rn : wRead w an = some (.intV uintK (v : Int))
  rl : wRead w al = some (.intV intK (l : Int))

/-- `mkInt` is the identity on a value already in range. -/
theorem mkInt_u (v : Nat) (h : v < 2 ^ 64) :
    GoVal.mkInt uintK (v : Int) = .intV uintK (v : Int) := by
  simp [GoVal.mkInt, IntKind.wrap, uintK, IntKind.uint64, IntKind.modulus]; omega

theorem mkInt_i (l : Nat) (h : l < 2 ^ 63) :
    GoVal.mkInt intK (l : Int) = .intV intK (l : Int) := by
  simp [GoVal.mkInt, IntKind.wrap, intK, IntKind.int64, IntKind.modulus]; omega

/-- The loop's body, named so the step lemma can be about it. -/
def loopBody : List Stmt := [.incDec "len" true, .assignOp .shr "n" (u 1)]

/-- The loop's condition. -/
def loopCond : Expr := .binary .ne (.ident "n") (u 0)

/-- **ONE TURN OF THE BODY**, proved: `len++` then `n >>= 1` takes the
world from `(v, l)` to `(v / 2, l + 1)`.

This is the crux, and it is the theorem that needed BOTH halves of the
last two inches: `go_run` to step `lookupLocal`/`loadAddr`/`storeLocal`,
and `wRead_wStore_other` to show that writing `len` leaves `n` alone. -/
theorem body_step (P : FuncTable) {w : GoWorld} {an al : Addr} {v l f : Nat}
    (hi : Inv w an al v l) (hv : v < 2 ^ 64) (hl : l + 1 < 2 ^ 63) (hf : 4 ≤ f) :
    ∃ w', execSeq P f loopBody w = .ok (.ok Flow.normal, w')
        ∧ Inv w' an al (v / 2) (l + 1) := by
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 4 := ⟨f - 4, by omega⟩
  refine ⟨wStore (wStore w al (.intV intK ((l + 1 : Nat) : Int))) an
            (.intV uintK ((v / 2 : Nat) : Int)), ?_, ?_⟩
  · have hcast : ((l : Int) + 1) = (((l + 1 : Nat)) : Int) := by push_cast; rfl
    have hfd : Int.fdiv (v : Int) 2 = ((v / 2 : Nat) : Int) := by
      cases v with | zero => rfl | succ k => rfl
    simp only [loopBody, execSeq, execStmt, go_run,
      lookupLocal_ok hi.ll, loadAddr_ok hi.rl, if_true, hcast,
      mkInt_i (l + 1) hl, storeLocal_ok hi.ll]
    have hln : wLookup (wStore w al (.intV intK ((l + 1 : Nat) : Int))) "n" = some an := by
      rw [wLookup_wStore]; exact hi.ln
    have hrn : wRead (wStore w al (.intV intK ((l + 1 : Nat) : Int))) an
        = some (.intV uintK (v : Int)) := by
      rw [wRead_wStore_other _ _ _ _ hi.ne]; exact hi.rn
    have h1 : GoVal.mkInt uintK 1 = .intV uintK 1 := by rfl
    simp only [go_run, lookupLocal_ok hln, loadAddr_ok hrn, u, evalExpr, binNum, h1]
    have hif : ¬ ((1 : Int) < 0) := by decide
    have hp : ((2 : Int) ^ (Int.toNat 1)) = 2 := by decide
    have hmk : GoVal.mkInt uintK ((v / 2 : Nat) : Int) = .intV uintK ((v / 2 : Nat) : Int) :=
      mkInt_u (v / 2) (by omega)
    simp only [if_neg hif, hp, hfd, hmk, go_run, storeLocal_ok hln]
  · refine ⟨hi.ne, ?_, ?_, ?_, ?_⟩
    · rw [wLookup_wStore, wLookup_wStore]; exact hi.ln
    · rw [wLookup_wStore, wLookup_wStore]; exact hi.ll
    · rw [wRead_wStore_same]
    · rw [wRead_wStore_other _ _ _ _ (Ne.symm hi.ne), wRead_wStore_same]

/-- **THE CONDITION**: `n != 0` reads `n` and compares it to zero, leaving
the world untouched. -/
theorem cond_eval (P : FuncTable) {w : GoWorld} {an al : Addr} {v l f : Nat}
    (hi : Inv w an al v l) (hf : 2 ≤ f) :
    evalExpr P f loopCond w = .ok (.ok (.boolV (decide (¬ (v = 0)))), w) := by
  obtain ⟨f, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  have h0 : GoVal.mkInt uintK 0 = .intV uintK 0 := by rfl
  simp only [loopCond, u, evalExpr, go_run, lookupLocal_ok hi.ln, loadAddr_ok hi.rn, h0, binNum]
  simp only [decide_not]
  congr 1
  cases v with
  | zero => simp
  | succ k => simp; omega

/-! ## §1c THE LOOP INDUCTION — CLOSED

§G11 named the last blocker: **`simp` will not rewrite inside a dependent
match discriminant.** `LeanModels/Go/Obs.lean` §1b answers it, and the
answer is not a congruence over the scrutinee — it is three lemmas that
step a bind from a KNOWN HEAD, so the match never appears at all.

With those, the induction closes. It is a strong induction on `v`, and
each turn is `cond_eval` to test, `body_step` to advance, and the
induction hypothesis at `v / 2`. -/

theorem asBool_ok (b : Bool) (w : GoWorld) :
    asBool (.boolV b) w = .ok (.ok b, w) := rfl

theorem loop_computes (P : FuncTable) : ∀ (v : Nat) (l f : Nat) (w : GoWorld) (an al : Addr),
    Inv w an al v l → v < 2 ^ 64 → l + bitLenSpec v < 2 ^ 63 →
    bitLenSpec v + 6 ≤ f →
    ∃ w', execLoop P f (some loopCond) none loopBody [] w = .ok (.ok Flow.normal, w')
        ∧ Inv w' an al 0 (l + bitLenSpec v) := by
  intro v
  induction v using Nat.strongRecOn with
  | _ v ih =>
    intro l f w an al hi hv hl hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rcases Nat.eq_zero_or_pos v with rfl | hpos
    · have hz : bitLenSpec 0 = 0 := by simp [bitLenSpec]
      rw [hz] at hf hl
      refine ⟨w, ?_, by simpa [hz] using hi⟩
      simp only [execLoop]
      rw [run_bind_ok (cond_eval P (f := f) hi (by omega)), run_bind_ok (asBool_ok _ w)]
      simp only [decide_not, decide_true, Bool.not_true, Bool.false_eq_true, if_false,
        decide_false, Bool.not_false, if_true]
      exact run_pure _ _
    · have hbs : bitLenSpec v = bitLenSpec (v / 2) + 1 := bitLenSpec_pos hpos
      have hlt : v / 2 < v := by omega
      have hfb : (4 : Nat) ≤ f := by omega
      have hl1 : l + 1 < 2 ^ 63 := by omega
      have hl2 : l + 1 + bitLenSpec (v / 2) < 2 ^ 63 := by omega
      have hf2 : bitLenSpec (v / 2) + 6 ≤ f := by omega
      have hv2 : v / 2 < 2 ^ 64 := by omega
      obtain ⟨w1, hw1, hi1⟩ := body_step P hi hv hl1 hfb
      obtain ⟨w2, hw2, hi2⟩ := ih (v / 2) hlt (l + 1) f w1 an al hi1 hv2 hl2 hf2
      refine ⟨w2, ?_, ?_⟩
      · simp only [execLoop]
        rw [run_bind_ok (cond_eval P (f := f) hi (by omega)), run_bind_ok (asBool_ok _ w)]
        have hne : ¬ (v = 0) := by omega
        simp only [hne, not_false_eq_true, decide_true, Bool.not_true,
          Bool.false_eq_true, if_false]
        rw [run_bind_ok hw1]
        dsimp only
        rw [run_bind_ok (run_get w1)]
        cases hb : w1.lang.perIterationLoopVars
        · simp only [hb, Bool.false_eq_true, if_false]; exact hw2
        · simp only [hb, if_true]
          rw [run_bind_ok (show freshenLoopVars [] w1 = .ok (.ok ⟨⟩, w1) from rfl)]
          exact hw2
      · have he : l + 1 + bitLenSpec (v / 2) = l + bitLenSpec v := by omega
        simpa [he] using hi2

/-- A bit length never exceeds the width — needed so a concrete fuel
suffices for every input the type can hold. -/
theorem bitLenSpec_le_64 {n : Nat} (h : n < 2 ^ 64) : bitLenSpec n ≤ 64 := by
  rcases Nat.eq_zero_or_pos n with rfl | hp
  · simp [bitLenSpec]
  · have h1 : 2 ^ (bitLenSpec n - 1) ≤ n := bitLenSpec_le hp
    have hlt : bitLenSpec n - 1 < 64 := by
      rcases Nat.lt_or_ge (bitLenSpec n - 1) 64 with hx | hx
      · exact hx
      · have h2 : (2 : Nat) ^ 64 ≤ 2 ^ (bitLenSpec n - 1) :=
          Nat.pow_le_pow_right (by omega) hx
        omega
    have hb : 1 ≤ bitLenSpec n := by rw [bitLenSpec_pos hp]; omega
    omega

/-! **THE DEBT IS CLEARED.** §G8 could not step the walker; §G10's seam
made it steppable; §G11 proved one turn and named the last obstacle; and
`run_bind_ok` above closes it. The loop's correctness is now a theorem,
not a checked composition. -/

/-! ## §1d THE COMPOSITION — from the loop to the FUNCTION

The loop theorem says what the loop does. This carries it through the
function's frame: bind the parameter, declare `len`, run the loop, return
`len`. Each of the three statements is `body_step`-shaped, which is what
made this one inch rather than a campaign. -/

/-- The world after the callee's frame is set up: `n` at 0, `len` at 1. -/
def setupW (v : Nat) : GoWorld :=
  { store := [(1, .intV intK 0), (0, .intV uintK (v : Int))],
    nextAddr := 2,
    locals := [("len", 1), ("n", 0)] }

theorem setup_inv (v : Nat) : Inv (setupW v) 0 1 v 0 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> simp [setupW, wLookup, wRead]

/-- The world after the parameter is bound. -/
def paramW (v : Nat) : GoWorld :=
  { store := [(0, .intV uintK (v : Int))], nextAddr := 1, locals := [("n", 0)] }

theorem bindParams_ok (v : Nat) (hv : v < 2 ^ 64) :
    bindParams ["n"] [GoVal.mkInt uintK (v : Int)] ({} : GoWorld)
      = .ok (.ok ⟨⟩, paramW v) := by
  simp only [bindParams, bindLocal, go_run, mkInt_u v hv]
  rfl

theorem declare_ok (P : FuncTable) (v : Nat) (f : Nat) :
    execStmt P (f + 2) (.declare "len" (.lit (GoVal.mkInt intK 0))) (paramW v)
      = .ok (.ok Flow.normal, setupW v) := by
  have h0 : GoVal.mkInt intK 0 = .intV intK 0 := by rfl
  simp only [execStmt, go_run, evalExpr, h0]
  rfl



/-- The `for` statement: no init, so the loop-variable set is empty and
the version branch is a no-op here. -/
theorem for_step (P : FuncTable) (v : Nat) (hv : v < 2 ^ 64) (f : Nat)
    (hf : bitLenSpec v + 6 ≤ f) (hb : bitLenSpec v < 2 ^ 63) :
    ∃ w', execStmt P (f + 1) (.forS none (some loopCond) none loopBody) (setupW v)
        = .ok (.ok Flow.normal, w')
      ∧ Inv w' 0 1 0 (bitLenSpec v) := by
  obtain ⟨w1, hw1, hi1⟩ :=
    loop_computes P v 0 f (setupW v) 0 1 (setup_inv v) hv (by simpa using hb) hf
  refine ⟨{ w1 with locals := (setupW v).locals }, ?_, ?_⟩
  · simp only [execStmt]
    rw [run_bind_ok (run_get (setupW v)), run_bind_ok (run_get (setupW v))]
    simp only [Nat.sub_self, List.take_zero, List.map_nil]
    rw [run_bind_ok hw1, run_bind_ok (run_modify _ w1)]
    rfl
  · refine ⟨hi1.ne, ?_, ?_, hi1.rn, ?_⟩
    · simp [wLookup, setupW]
    · simp [wLookup, setupW]
    · have h := hi1.rl; rw [Nat.zero_add] at h; exact h



/-- `bitLenBody` IS the three statements, with the loop's own pieces. -/
theorem body_eq : bitLenBody
    = [ .declare "len" (.lit (GoVal.mkInt intK 0)),
        .forS none (some loopCond) none loopBody,
        .ret (some (.ident "len")) ] := rfl

/-- `return len` reads `len` and returns it. -/
theorem ret_ok (P : FuncTable) {w : GoWorld} {an al : Addr} {v l f : Nat}
    (hi : Inv w an al v l) :
    execStmt P (f + 2) (.ret (some (.ident "len"))) w
      = .ok (.ok (Flow.returned (some (.intV intK (l : Int)))), w) := by
  simp only [execStmt, go_run, evalExpr, lookupLocal_ok hi.ll, loadAddr_ok hi.rl]

/-- The function's THREE STATEMENTS, run end to end. -/
theorem body_runs (v : Nat) (hv : v < 2 ^ 64) (g : Nat)
    (hg : bitLenSpec v + 8 ≤ g) :
    ∃ w', execSeq prog (g + 3) bitLenBody (paramW v)
        = .ok (.ok (Flow.returned (some (.intV intK ((bitLenSpec v : Nat) : Int)))), w') := by
  have hb64 : bitLenSpec v ≤ 64 := bitLenSpec_le_64 hv
  obtain ⟨h, rfl⟩ : ∃ h, g = h + 2 := ⟨g - 2, by omega⟩
  obtain ⟨w2, hw2, hi2⟩ := for_step prog v hv (h + 2) (by omega) (by omega)
  refine ⟨w2, ?_⟩
  simp only [body_eq, execSeq]
  rw [run_bind_ok (declare_ok prog v (h + 2))]
  dsimp only
  rw [run_bind_ok hw2]
  dsimp only
  rw [run_bind_ok (ret_ok prog (f := h) hi2)]
  rfl

/-- **THE FUNCTION.** `bitLen v` returns `bitLenSpec v`. -/
theorem bitLen_correct (v : Nat) (hv : v < 2 ^ 64) (f : Nat)
    (hf : bitLenSpec v + 11 ≤ f) :
    ∃ w', callFunction prog f "bitLen" [GoVal.mkInt uintK (v : Int)] ({} : GoWorld)
        = .ok (.ok (.intV intK ((bitLenSpec v : Nat) : Int)), w') := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 3 := ⟨f - 3, by omega⟩
  obtain ⟨w3, hw3⟩ := body_runs v hv g (by omega)
  have hfind : prog.find? (fun d => d.1 == "bitLen")
      = some ("bitLen", ["n"], bitLenBody) := rfl
  have hlen : ((["n"] : List String).length
      != ([GoVal.mkInt uintK (v : Int)] : List GoVal).length) = false := rfl
  refine ⟨{ w3 with locals := [] }, ?_⟩
  simp only [callFunction, hfind, hlen, Bool.false_eq_true, if_false]
  rw [run_bind_ok (run_get ({} : GoWorld))]
  rw [run_bind_ok (bindParams_ok v hv)]
  rw [run_bind_ok hw3]
  rw [run_bind_ok (run_modify _ w3)]
  rfl

/-- **THE CLAIM, in the form the guards use.** `bitLen` — the helper the
35 differential rows call — returns `bitLenSpec` on every value the type
can hold. The fixed fuel of 4096 suffices because a bit length never
exceeds 64 (`bitLenSpec_le_64`).

**This demotes the 35 spec rows below from checks to corroboration**:
they were the evidence while the composition was owed, and they are now
instances of a theorem. The 35 ORACLE rows keep their full weight —
they are the only thing tying the model to what `gc` actually printed,
and no theorem about the model can replace them. -/
theorem bitLen_eq_spec (v : Nat) (hv : v < 2 ^ 64) :
    bitLen (v : Int) = some ((bitLenSpec v : Nat) : Int) := by
  have hb : bitLenSpec v ≤ 64 := bitLenSpec_le_64 hv
  obtain ⟨w', hw⟩ := bitLen_correct v hv 4096 (by omega)
  simp only [bitLen, hw]

/-! ## §2 THE INTERPRETER BRIDGE — one step, and it is the load-bearing one

The interpreter half's content is that the walker's OPERATION is the
spec's operation. `n >>= 1` on a `uint64` is the interpreter's
`binNum .shr`; the spec's step is `n / 2`. This lemma is the join, and it
is where a width bug or a signedness bug would surface. -/

/-- Halving a non-negative integer is floor division — the arithmetic
fact the bridge rests on. -/
@[go_spec] theorem fdiv_two (v : Nat) :
    Int.fdiv (v : Int) 2 = ((v / 2 : Nat) : Int) := by
  cases v with
  | zero => rfl
  | succ k => rfl

/-- **THE BRIDGE.** The interpreter's `n >>= 1` on a `uint64` IS the
spec's `n / 2`. This is where a width bug or a signedness bug would
surface, and it is the one place the two halves touch. -/
@[go_spec] theorem shr_one_is_halving (v : Nat) :
    binNum .shr IntKind.uint64 (v : Int) 1
      = pure (GoVal.mkInt IntKind.uint64 ((v / 2 : Nat) : Int)) := by
  simp [binNum, fdiv_two]

/-! **What is still owed, named rather than implied.** The full
interpreter half — *the walker, run on `bitLenBody` with enough fuel,
leaves `len` equal to `bitLenSpec n`* — is an induction over the loop
carrying the store through each iteration. It is this lane's next
theorem. What is proved here is its arithmetic step; what is CHECKED
below, on 35 inputs, is the composition. The distinction is the whole
reason §1 and §2 are separated. -/

/-! ## THE DIFFERENTIAL ROWS — 35 of them, and the expected column was
GENERATED, not typed

Every row below was produced by `printf`-ing the compiled function's
answer and mechanically rewriting it into `#guard` syntax. Typing the
column by hand was the first attempt and it is exactly the wrong way:
this file's whole claim is that two independent implementations agree, and
a hand-copied expectation makes the Lean side's answer the source of both
columns the moment anyone "fixes" a row. The inputs sweep the powers of
two and their neighbours up to the full 64-bit width, where a width bug
would hide. -/

#guard bitLen 0 == some 0
#guard bitLen 1 == some 1
#guard bitLen 2 == some 2
#guard bitLen 3 == some 2
#guard bitLen 4 == some 3
#guard bitLen 5 == some 3
#guard bitLen 7 == some 3
#guard bitLen 8 == some 4
#guard bitLen 9 == some 4
#guard bitLen 15 == some 4
#guard bitLen 16 == some 5
#guard bitLen 17 == some 5
#guard bitLen 31 == some 5
#guard bitLen 32 == some 6
#guard bitLen 33 == some 6
#guard bitLen 63 == some 6
#guard bitLen 64 == some 7
#guard bitLen 65 == some 7
#guard bitLen 100 == some 7
#guard bitLen 127 == some 7
#guard bitLen 128 == some 8
#guard bitLen 255 == some 8
#guard bitLen 256 == some 9
#guard bitLen 511 == some 9
#guard bitLen 512 == some 10
#guard bitLen 1000 == some 10
#guard bitLen 1023 == some 10
#guard bitLen 1024 == some 11
#guard bitLen 65535 == some 16
#guard bitLen 65536 == some 17
#guard bitLen 2147483648 == some 32
#guard bitLen 4294967296 == some 33
#guard bitLen 4611686018427387904 == some 63
#guard bitLen 9223372036854775808 == some 64
#guard bitLen 18446744073709551615 == some 64

/-! `uint` is 64 bits on this profile, so the last row above — `2^64 - 1`
— is the widest value the type holds, and its bit length is 64. A value
BEYOND the width wraps on the way in, which is the language's own
reduction rule and not a clamp: -/

#guard bitLen (2 ^ 64) == some 0

/-! ## THREE-WAY AGREEMENT — model, oracle, and the MATHEMATICS

The rows above pin the model against what `gc` printed. These pin it
against `bitLenSpec`, which §1 proved is genuinely the bit length
(`bitLenSpec_le` and `bitLenSpec_lt` bracket it from both sides).

So the same 35 inputs are checked twice, against two independent
standards: an executable oracle and a proved specification. A model that
agreed with the compiler but not the mathematics — or the reverse — would
show up in exactly one of the two blocks. -/

def bitLenN (n : Nat) : Option Int := bitLen (n : Int)

#guard bitLenN 0 == some (bitLenSpec 0)
#guard bitLenN 1 == some (bitLenSpec 1)
#guard bitLenN 2 == some (bitLenSpec 2)
#guard bitLenN 3 == some (bitLenSpec 3)
#guard bitLenN 4 == some (bitLenSpec 4)
#guard bitLenN 5 == some (bitLenSpec 5)
#guard bitLenN 7 == some (bitLenSpec 7)
#guard bitLenN 8 == some (bitLenSpec 8)
#guard bitLenN 9 == some (bitLenSpec 9)
#guard bitLenN 15 == some (bitLenSpec 15)
#guard bitLenN 16 == some (bitLenSpec 16)
#guard bitLenN 17 == some (bitLenSpec 17)
#guard bitLenN 31 == some (bitLenSpec 31)
#guard bitLenN 32 == some (bitLenSpec 32)
#guard bitLenN 33 == some (bitLenSpec 33)
#guard bitLenN 63 == some (bitLenSpec 63)
#guard bitLenN 64 == some (bitLenSpec 64)
#guard bitLenN 65 == some (bitLenSpec 65)
#guard bitLenN 100 == some (bitLenSpec 100)
#guard bitLenN 127 == some (bitLenSpec 127)
#guard bitLenN 128 == some (bitLenSpec 128)
#guard bitLenN 255 == some (bitLenSpec 255)
#guard bitLenN 256 == some (bitLenSpec 256)
#guard bitLenN 511 == some (bitLenSpec 511)
#guard bitLenN 512 == some (bitLenSpec 512)
#guard bitLenN 1000 == some (bitLenSpec 1000)
#guard bitLenN 1023 == some (bitLenSpec 1023)
#guard bitLenN 1024 == some (bitLenSpec 1024)
#guard bitLenN 65535 == some (bitLenSpec 65535)
#guard bitLenN 65536 == some (bitLenSpec 65536)
#guard bitLenN 2147483648 == some (bitLenSpec 2147483648)
#guard bitLenN 4294967296 == some (bitLenSpec 4294967296)
#guard bitLenN 4611686018427387904 == some (bitLenSpec 4611686018427387904)
#guard bitLenN 9223372036854775808 == some (bitLenSpec 9223372036854775808)
#guard bitLenN 18446744073709551615 == some (bitLenSpec 18446744073709551615)

/-! ## Non-vacuity — the harness DISCRIMINATES

A differential row that cannot fail is decoration. An audit
(`docs/quality-audit-2026-08-23.md`) caught this section failing its own
standard: its rows were byte-identical to ordinary oracle rows above, so
it checked nothing the file did not already check. These rows are
different in kind — each asserts a NEGATIVE, which no oracle row does:

* the model does not answer a neighbouring value,
* and does not answer `none` (a refusal or a fuel exhaustion).

Together they say the harness would notice if either failure mode
appeared, which is what "can fail" means. The stronger check — that a
wrong EXPECTATION breaks the build — is a flip test, run and recorded in
`docs/backlog/go.md` §G6 and §G9, and deliberately not left in the file,
because a guard that must fail is not a guard. -/

#guard (bitLen 1024 == some 10) == false
#guard (bitLen 1024 == some 12) == false
#guard (bitLen 1024 == none) == false

/-! ## Fuel is not decoration either

The loop runs once per significant bit, so `bitLen (2^63)` needs 64
iterations. At fuel too small for the walk, the answer is a TIMEOUT and
not a wrong number — the model declines rather than truncating. -/

def bitLenAt (fuel : Nat) (n : Int) : Bool :=
  match (callFunction prog fuel "bitLen" [GoVal.mkInt uintK n]) ({} : GoWorld) with
  | .error .timeout => true
  | _ => false

#guard bitLenAt 4 (2 ^ 63) == true
#guard bitLenAt 4096 (2 ^ 63) == false

/-! ## A call to an undeclared function is ENVIRONMENT, not a language gap

It retires by widening the modelled slice, never by climbing a rung —
and, per the tier's standing gate, never as `undefined`. -/

#guard (match (callFunction prog 64 "bits.Len" [GoVal.mkInt uintK 1]) ({} : GoWorld) with
        | .error (.unsupported c _ _) => c.className == "environment"
        | _ => false) == true

#guard (match (callFunction prog 64 "bits.Len" [GoVal.mkInt uintK 1]) ({} : GoWorld) with
        | .error (.unsupported c _ _) => c.isUndefined
        | _ => true) == false

end Examples.go.bitlen

/-! ## Axioms -/
#print axioms Examples.go.bitlen.bitLenSpec_lt
#print axioms Examples.go.bitlen.bitLenSpec_le
#print axioms Examples.go.bitlen.shr_one_is_halving
