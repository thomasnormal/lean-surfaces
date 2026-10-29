import LeanModels.Sv.Comb2
import LeanModels.Sv.Mono2
import LeanModels.Sv.Known2

/-!
# `always_comb` in the combinational settle theorem (`LeanModels.Sv` — Design2)

The combinational settle theorem (`Comb2Base`/`Comb2Sound`/`Comb2Term`/
`Comb2`) is stated for designs whose processes are all continuous assigns.
This file extends it to designs that also contain `always_comb` processes
(`Process2.alwaysComb body`) whose bodies are blocking assignments under
`begin … end`, `if`/`else` and `case` (`case … inside` included).

## The idea: lower the body to one continuous assign

A body in the profile is run SYMBOLICALLY (`Stmt2.symExec`) over a
symbolic state (`SymState`): the list of windows the body has written so
far, each with an expression over the PRE-state saying what the window now
holds. Reads of a written window are replaced by its expression
(`Expr2.symSubst`), an `if`/`case` joins its branches window by window with
a known 1-bit guard (`SymState.join`; `Expr2.ifGuard` is `(|c) === 1'b1`,
which is exactly the interpreter's `if` truthiness, `Expr2.anyGuard` the
`case` arm hit), and a window a branch does not write keeps its pre-state
value (`Win.held`). The result is ONE equation per written window. The
process is then replaced by the continuous assign
`assign {w₀, …, wₖ} = {E₀, …, Eₖ}` (`SymState.toAssign`; every leaf a
constant slice `n[lo +: w]`), and `Design2.lowerComb d` is `d` with every
`always_comb` lowered this way (assigns kept, anything else refused). A body
whose equations read a window the body itself writes is refused too
(`SymState.selfReadFree`, below).

**The lowering is exact on shaped states** (`runCombProcess2_alwaysComb_ok`,
`runCombProcess2_alwaysComb_fwd`): a successful run of the body, at any
fuel, is exactly the lowered assign's `combWrite`, and at every fuel from
the body's static bound `Stmt2.fuelB` on the body run succeeds. So
`Runs2 d σ stim tr ↔ Runs2 d' σ stim tr` (`Runs2.lowerComb_iff`) whenever
`d.lowerComb = some d'` and `d'` is in the comb profile — the two designs
have the same completed runs, under every schedule, with the same traces —
and EVERYTHING proved about comb designs transfers: `⊨₂`
(`Models2.of_lowerComb`, `Models2.of_combProc`, …), termination
(`Terminates2.of_lowerComb`), the fixpoint characterization.

## The profile, in terms of the lowered design

* **(a) Static write set, disjoint from every other process.** The windows
  of the symbolic state are the write set; `CombDesign d'` asks them to be
  in range, pairwise disjoint within the process (`selfDisjoint`) and
  disjoint from every other process's windows (`disjoint`), exactly as for a
  concatenated assign.
* **(b) Latch freedom, and no self-reads.** A window that some path does not
  write holds its pre-state value, so its equation READS ITSELF (`Win.held`);
  a read of a window the body writes only later reads its pre-state value
  too. The lowering refuses every body with such a read
  (`SymState.selfReadFree`: no equation reads any window of the body's write
  set — latches, `y = t; t = a;`, and `if (c) t = a; y = t; t = b;` alike).
  A `Win.held` value is always such a read, so an accepted body writes each
  of its windows on every path. The reason is simulator agreement, not only the fixpoint argument: an
  event-driven simulator runs an `always_comb` block once per wake-up and is
  never woken by the block's own writes (IEEE 1800-2023 §9.2.2.2.1), while
  the settle semantics re-runs every comb process until nothing changes.
  Icarus 12 lags one input change behind the settle answer on the last two
  bodies (Yosys 0.53 `proc` synthesizes the settle answer); since WP4
  (2026-10-28) `name.sem` refuses those two at instantiation
  (`CombGuard2.lean`) and admits the latch. The check makes
  one run of a lowered body its own fixpoint
  (`runCombProcess2_alwaysComb_idem`): the single run a simulator makes per
  wake-up already gives the block's settled value, and across blocks a
  simulator (Xcelium 24.03, Verilator 5.042) re-runs a block when another
  block's write changes what it reads, as the settle loop does — Icarus
  12.0 does not on a pure copy of a variable the block writes (it
  propagates the copy inside the block's run, an LRM-permitted
  interleaving) nor on a bit split (it drops the whole variable from the
  sensitivity list); both declared, `CombGuard2Sound.lean` module
  docstring.
  The check is the self-edge half of
  `Acyclic d'`; for a one-process design it is all of it
  (`Acyclic.of_lowerComb_single`).
* **(c) Termination of the body.** `Stmt2` has no loops; `Stmt2.fuelB` is a
  static fuel bound (`runCombProcess2_alwaysComb_fwd`).
* **(d) Dependency edges.** The read set of the lowered right-hand side —
  every read reached before the window it reads is written, every guard —
  is what `Acyclic d'` ranks: the Comb2Term rank
  argument, applied to `d'`, is the read/write-set rank argument for
  `always_comb`.

## The equations

`CombEqs d' S` is the generalized `CombEqs`: one equation per written window
(`CombEqs.symWindow`, `CombEqs.symWindow_ident`: the window holds the value
of its symbolic expression in `S`). `ProcFixpoint d S` — every process of `d`
maps `S` to itself (running the body on `S` yields `S`) — is equivalent to it
on shaped states (`procFixpoint_iff_combEqs`), and every snapshot of a run
satisfies both (`Runs2.combProc_snapshot`).

## API index

* Symbolic execution: `SymState`, `SymState.write`, `SymState.join`
  (`Expr2.joinIte`, with the sound syntactic equality `Expr2.same` /
  `Expr2.eq_of_same`), `SymState.readWhole`, `SymState.readWin`,
  `Expr2.symSubst`, `Lhs2.symWin`, `Stmt2.symExec` (with
  `Stmt2.symExecList`, `CaseItem2.symExecList`), `Expr2.ifGuard`,
  `Expr2.hitGuard`, `Expr2.anyGuard`, `Expr2.splice`, `Win.held`, the static
  fuel bound `Stmt2.fuelB`; names only grow (`Stmt2.symExec_names`).
* Lowering: `SymState.target`, `SymState.rhs`, `SymState.toAssign`,
  `SymState.selfReadFree` (`SymState.selfReadFree_iff`,
  `SymState.rhs_reads`), `Process2.lowerComb`, `Design2.lowerComb`,
  `Design2.lowerComb_spec`, `Design2.lowerComb_proc` / `_proc'`,
  `Process2.lowerComb_alwaysComb`, `SymState.target_wins`.
* Semantics of symbolic execution: `SymRel` (a concrete state agrees with
  the symbolic state over a pre-state), `SymOk` (pre-state width facts),
  `Expr2.symSubst_sound`, `SymState.write_sound`,
  `SymState.join_sound_left` / `_right`, `evalPure2_ifGuard`,
  `evalPure2_anyGuard`, `symExec_sound` (fuel induction over
  `execStmt2`/`execCase2`/`execStmts2`), `symExec_total`, `SymRel.unique`,
  `SymRel.of_combWrite`.
* Process level: `runCombProcess2_alwaysComb_ok` (inversion, any fuel),
  `runCombProcess2_alwaysComb_fwd` (forward, from `Stmt2.fuelB`),
  `runCombProcess2_alwaysComb_idem` (one run is the body's own fixpoint).
* Run level: `CombSim` (`CombSim.runs2`), `CombSim.of_lowerComb` /
  `_of_lowerComb'`, **`Runs2.lowerComb_iff`**, `Models2.of_lowerComb`,
  `Terminates2.of_lowerComb`, **`Terminates2.of_lowerComb_acyclic`**,
  **`Models2.of_combProc`**, `Models2.of_combProc_inputs`,
  `Models2.of_combProc_pointwise`, `ProcFixpoint`,
  **`procFixpoint_iff_combEqs`**, `Runs2.combProc_snapshot`,
  **`CombEqs.symWindow`**, `CombEqs.symWindow_ident`.
* Single-process designs: `CombDesign.of_single`, `Acyclic.of_single` —
  the profile and the certificate as checks on closed data (`decide`) —
  and `Acyclic.of_lowerComb_single` / `Terminates2.of_lowerComb_single`:
  for a design whose only process is one `always_comb`, the certificate
  needs no proof at all.
* Worked examples: `Comb2ProcExample.lean` (a full adder with a temporary
  and an `if`/`else`, a `case` multiplexer, a "default then override one
  bit" decoder, an `N`-bit adder/subtractor with a zero flag proved for
  EVERY `N` — all proved correct and terminating — and three bodies the
  lowering refuses: a latch and two self-reads).

## Covered `always_comb` shapes

Covered: `begin … end` blocks; blocking assignments to a whole signal, a
constant slice or a constant-literal element select; `if` with or without
`else`; `case` and `case … inside` (any check qualifier: `unique`/`priority`
do not change SIMULATION — `run2`, Icarus and IEEE 1800-2023 §12.5.3 (a
violation is only reported) run the arms as for a plain `case` — but they DO
change synthesis: Yosys 0.53 `proc` treats a `unique`/`priority` case with
no matching arm as don't-care, and reads x bits in a plain `case`'s item
constants as wildcards, so the netlist can differ from the settle answer;
the declared entries are in `docs/sv-oracle-disagreements.md`) with or
without `default`, several patterns per
arm (a window that an `if` without `else`, or a `case` without `default`,
writes on some arms only must already have been written before it, or the
body is a latch and the self-read check refuses it); reads of whole signals, constant slices and arbitrary expressions,
dynamic selects included; a write to a sub-window of an already written
window (the "default then override" idiom `y = '0; if (c) y[2] = 1'b1;` —
`Expr2.splice`). Reads of a window written earlier on the path are replaced
by its expression, so a body may use temporaries freely (the temporary is
itself a written window with its own equation).

## Gaps (refused or rejected, never silently wrong)

Refused by `symExec` (so `lowerComb` returns `none`): nonblocking
assignments; dynamic-index targets (`y[i] = …` with `i` not a literal);
procedural concatenation targets (`{c, s} = a + b;` — write it as a
continuous assign, which the comb profile admits); a whole-signal read of a
signal of which only part was written; a window read that straddles a
written window; a write that partially overlaps a written window without
lying inside it (`y[0] = a; y = b;`); branches that write overlapping but
different windows of one signal; any `.unsupported` node or undeclared
identifier. There are no loops in `Stmt2`; the extractor refuses a
procedural `for` in symbolic mode (`ForLoopStatement`). Refused before any
of this: a block-local declaration inside the `always_comb`
(`begin logic t; … end`) reaches the envelope as a `LocalDecl` statement,
which the sv-0.2 ingestion does not parse, so `load_design_sv2` and the
differential runner refuse the whole envelope (declare the temporary at
module level instead); a `unique if`/`unique0 if`/`priority if` is refused
by the extractor (`ConditionalStatement:Unique`, `:Unique0`, `:Priority` —
a loud node, so `symExec` refuses it too). Refused by the
self-read check (`SymState.selfReadFree`): latches (a window some path does
not write keeps its pre-state value), a body that reads one of its own
windows before writing it (`y = t; t = a;`), and a body that reads a value a
join kept for a window it later overwrites (`if (c) t = a; y = t; t = b;`).
An event-driven simulator does NOT re-run such a block on its own writes:
Icarus 12 leaves `y` one input change behind on the last two, where the
settle semantics (and Yosys 0.53 `proc`) give `y = a` and `y = c ? a : b`.
This refusal covers this API only. Since 2026-10-28 (WP4) the always_comb
self-read guard (`CombGuard2.lean`) refuses the self-reading bodies at
instantiation too, so no `name.sem` and no differential-runner design runs
them (`rbw_guard`, `held_guard` in `Comb2ProcExample`; the fixtures'
`agree.lean` pin `load_design_sv2`'s refusal). `run2` on a HAND-BUILT
`Design2` still settles them (`rbwDesign`/`heldDesign`'s `#guard` pins) —
the retired declared divergence `sv-div-3`. The guard and
`SymState.selfReadFree` are different tests, neither stronger: the guard is
path-sensitive and admits latches (one run of a latch is its own fixpoint,
`runCombProcess2_alwaysComb_idem_of_admits`, which generalizes
`runCombProcess2_alwaysComb_idem` to every admitted body), while
`selfReadFree` sees through values that never reach an equation and lowers
`y = t; y = a; t = b;` and `if (t) y = a; else y = a; t = b;`, which the
guard refuses (`dead_lowers`/`dead_refused`, `same_lowers`/`same_refused`).
On such a body the API meets the guard's loud process through `name.sem`
(`lowerComb` is `none` there), never a body the guard let through; every
body of `Comb2ProcExample` the lowering accepts is admitted by the guard
(`fa_admits`, `mux_admits`, `dec_admits`, `as_admits` at every `N`). Only comb-only designs lower (`alwaysFF`
and friends refuse; the settle theorem is comb-only). The termination
certificate `Acyclic d'` ranks PROCESSES, not windows, and a whole body
lowers to ONE assign: a body that writes `t` and reads `w`, next to
`assign w = t + 1`, is a process-level cycle although no window depends on
itself (Icarus and the settle semantics both settle it). Split such a body
into separate `always_comb` blocks or assigns; a window-level rank is future
work. Expression size: substitution copies a written
window's expression into every later read, and a join wraps every window a
branch CHANGED in a `?:` (windows both branches leave alone are kept,
`Expr2.joinIte`), so `k` sequential `if`s that write the same window nest
`k` deep. Parametric (`∀ N`) bodies: `symExec` is computed by `rfl` on
closed designs; at a symbolic width its window comparisons do not reduce by
`rfl`, and `simp` over the definitions evaluates it instead
(`Comb2ProcExample.as_symExec`, an `N`-bit adder/subtractor) — no generic
tactic packages that recipe yet.

## Design laws

* **Reuse, not re-proof.** The settle soundness and termination theorems of
  `Comb2Sound`/`Comb2Term` are NOT re-proved for `always_comb`: the lowering
  simulates the design step for step (`CombSim`: every pass, settle, cycle
  and run of `d` is one of `d'` at some fuel, and back, on states with the
  comb shape of `d'`), so the existing theorems apply to `d'` verbatim and
  `Runs2.lowerComb_iff` carries them back. `Comb2*.lean` are unchanged.
* **Fuel never reaches a statement.** The symbolic-execution lemmas are fuel
  inductions over the interpreter's mutual block (`symExec_sound`,
  `symExec_total`); every consumer-facing theorem quantifies over `Runs2` /
  `⊨₂` / `Terminates2` only.
* **4-state exact.** Nothing assumes known values: `x`/`z` conditions take
  the `else` branch exactly as the interpreter's `if` does (the guard
  `(|c) === 1'b1` is never `x`), a `case` subject with `x`/`z` bits
  matches a plain pattern only when the two agree bit for bit under `===`
  (so never a fully known pattern), and the equivalence holds on every
  shaped state.
* **The symbolic execution is computed, not trusted.** It is an ordinary
  structural function, evaluated by `rfl` on a concrete body; its soundness
  (`symExec_sound`) is proved once, against the interpreter.

## Deviations from the original statement

* The profile, `CombEqs` and the rank certificate are not generalized IN
  PLACE (`CombDesign`, `CombEqs`, `Acyclic` keep their assign-only
  statements): they are stated of the lowered design `d'`. The generalized
  fixpoint condition is `ProcFixpoint d S` (every process of `d`, the
  `always_comb` bodies included, maps `S` to itself), proved equivalent to
  `CombEqs d' S` on shaped states; the read/write-set rank argument for
  `always_comb` is `Acyclic d'`, whose read set for a lowered body is the
  read set of its symbolic equations.
* Latch freedom is not a separate condition: the self-read check
  (`SymState.selfReadFree`) refuses latches together with every other body
  whose equations read the body's own write set, which is also the
  condition under which the settle semantics and an event-driven simulator
  agree on the body (`runCombProcess2_alwaysComb_idem`).
* The termination bound for a body is `Stmt2.fuelB`; the run-level
  termination theorem is stated, like `Terminates2.of_acyclic`, without a
  bound.
-/

namespace LeanModels.Sv

/-! ## Symbolic states -/

/-- A symbolic state: the windows an `always_comb` body has written so far,
each with the expression — over the PRE-state of the body — whose value it
now holds. -/
abbrev SymState := List (Win × Expr2)

/-- The declared signal names of a design (in declaration order). -/
def Design2.symNames (d : Design2) : List String := d.decls.toList.map Decl.name

/-- Well-formedness of an expression a body evaluates: no `.unsupported`
node and every identifier declared (`evalPure2_ok_of_wf` then makes it
evaluate on every state that binds the declared names). -/
def Expr2.wfB (d : Design2) (e : Expr2) : Bool :=
  e.unsupportedFree && e.idents.all fun x => decide (x ∈ d.symNames)

/-- `Expr2.wfB` of every element of a list. -/
def Expr2.listWfB (d : Design2) (es : List Expr2) : Bool :=
  Expr2.listUnsupportedFree es && (Expr2.listIdents es).all fun x => decide (x ∈ d.symNames)

/-- The pre-state value of a window, `n[lo +: w]` (what a window the current
path did not write still holds). -/
def Win.held (W : Win) : Expr2 := .slice (.ident W.1) W.2.1 W.2.2

/-- `W` contains `V`: same signal and `V`'s bit range inside `W`'s. -/
def Win.contains (W V : Win) : Bool :=
  W.1 == V.1 && decide (W.2.1 ≤ V.2.1) && decide (V.2.1 + V.2.2 ≤ W.2.1 + W.2.2)

/-- Pairwise disjointness of a window list, as a checker. -/
def Win.allDisjoint : List Win → Bool
  | [] => true
  | W :: ws => ws.all (fun V => !Win.overlaps W V) && Win.allDisjoint ws

/-- The `if (c)` guard as a KNOWN bit: `(|c) === 1'b1` is `1` exactly when
`c` has a `1` bit (`LVec.condTrue`, the interpreter's `if` truthiness) and
`0` otherwise — never `x`, so a `?:` on it picks one arm. -/
def Expr2.ifGuard (c : Expr2) : Expr2 :=
  .binary .caseEq (.reduce .or c) (.lit (LVec.ofLogic .l1))

/-- One `case` pattern's hit as a known bit: `subj === pat` (plain `case`),
`(subj ==? pat) === 1'b1` (`case … inside`) — `caseHit`. -/
def Expr2.hitGuard (inside : Bool) (subj pat : Expr2) : Expr2 :=
  if inside then .binary .caseEq (.binary .wildEq subj pat) (.lit (LVec.ofLogic .l1))
  else .binary .caseEq subj pat

/-- A `case` arm's hit as a known bit: the `|` of its patterns' hits (`0`
for no pattern). -/
def Expr2.anyGuard (inside : Bool) (subj : Expr2) : List Expr2 → Expr2
  | [] => .lit (LVec.ofLogic .l0)
  | p :: ps => .binary .or (Expr2.hitGuard inside subj p) (Expr2.anyGuard inside subj ps)

/-- Replace bits `[r, r + w)` of a `w0`-bit value `E0` by `E` (a `w`-bit
value): `{E0[w0-1 : r+w], E, E0[r-1 : 0]}`. -/
def Expr2.splice (E0 : Expr2) (w0 r w : Nat) (E : Expr2) : Expr2 :=
  .concat #[.slice E0 (r + w) (w0 - (r + w)), E, .slice E0 0 r]

mutual
/-- Sound syntactic equality of expressions (`Expr2` derives no
`DecidableEq`): `true` only on identical trees. -/
def Expr2.same : Expr2 → Expr2 → Bool
  | .lit v, e' => match e' with | .lit v' => decide (v = v') | _ => false
  | .ident n, e' => match e' with | .ident n' => decide (n = n') | _ => false
  | .unsupported k x, e' => match e' with
      | .unsupported k' x' => decide (k = k') && decide (x = x') | _ => false
  | .unary o a, e' => match e' with | .unary o' a' => decide (o = o') && a.same a' | _ => false
  | .resizeSigned w a, e' => match e' with
      | .resizeSigned w' a' => decide (w = w') && a.same a' | _ => false
  | .squash2 a, e' => match e' with | .squash2 a' => a.same a' | _ => false
  | .repl k a, e' => match e' with | .repl k' a' => decide (k = k') && a.same a' | _ => false
  | .reduce o a, e' => match e' with | .reduce o' a' => decide (o = o') && a.same a' | _ => false
  | .resize w a, e' => match e' with | .resize w' a' => decide (w = w') && a.same a' | _ => false
  | .binary o l r, e' => match e' with
      | .binary o' l' r' => decide (o = o') && l.same l' && r.same r' | _ => false
  | .scmp o l r, e' => match e' with
      | .scmp o' l' r' => decide (o = o') && l.same l' && r.same r' | _ => false
  | .logical b l r, e' => match e' with
      | .logical b' l' r' => decide (b = b') && l.same l' && r.same r' | _ => false
  | .index a i w, e' => match e' with
      | .index a' i' w' => decide (w = w') && a.same a' && i.same i' | _ => false
  | .ternary c t f, e' => match e' with
      | .ternary c' t' f' => c.same c' && t.same t' && f.same f' | _ => false
  | .slice a lo w, e' => match e' with
      | .slice a' lo' w' => decide (lo = lo') && decide (w = w') && a.same a' | _ => false
  | .concat ps, e' => match e' with
      | .concat ps' => Expr2.listSame ps.toList ps'.toList | _ => false
termination_by structural e => e

def Expr2.listSame : List Expr2 → List Expr2 → Bool
  | [], l' => match l' with | [] => true | _ => false
  | e :: es, l' => match l' with | e' :: es' => e.same e' && Expr2.listSame es es' | _ => false
termination_by structural es => es
end

/-- The joined value of a window: the first branch's if the two branches
agree syntactically, else `G ? a : b`. -/
def Expr2.joinIte (G A B : Expr2) : Expr2 := if A.same B then A else .ternary G A B

namespace SymState

/-- The signals a symbolic state writes. -/
def names (S : SymState) : List String := S.map fun e => e.1.1

/-- The expression of the entry with window exactly `W`. -/
def findWin (S : SymState) (W : Win) : Option Expr2 := (S.find? fun e => e.1 == W).map Prod.snd

/-- The first entry whose window contains `V`. -/
def findCover (S : SymState) (V : Win) : Option (Win × Expr2) :=
  S.find? fun e => Win.contains e.1 V

/-- Some entry's window overlaps `V`. -/
def overlapsAny (S : SymState) (V : Win) : Bool := S.any fun e => Win.overlaps e.1 V

/-- Some entry writes signal `n`. -/
def writesName (S : SymState) (n : String) : Bool := S.any fun e => e.1.1 == n

/-- The value window `W` holds: its entry, or its pre-state value. -/
def lookupOr (S : SymState) (W : Win) : Expr2 := (S.findWin W).getD W.held

/-- A whole-signal read `n`: the pre-state `n` if the body has not written
`n`, the entry of the FULL window `(n, 0, declared width)` if it has; any
other partial write refuses. -/
def readWhole (d : Design2) (S : SymState) (n : String) : Option Expr2 :=
  if S.writesName n then (d.declWidth n).bind fun dw => S.findWin (n, 0, dw)
  else some (.ident n)

/-- A window read `n[lo +: w]`: a slice of the entry whose window contains
it, the pre-state read if no entry overlaps it; a straddling read
refuses. -/
def readWin (S : SymState) (n : String) (lo w : Nat) : Option Expr2 :=
  match S.findCover (n, lo, w) with
  | some (W, E) => some (.slice E (lo - W.2.1) w)
  | none => if S.overlapsAny (n, lo, w) then none else some (.slice (.ident n) lo w)

/-- Blocking write of window `W` with value `E`: replace the entry with
window exactly `W`; else splice `E` into the entry whose window contains
`W` (`Expr2.splice`); else append `W` if it overlaps no entry; else
refuse. -/
def write (S : SymState) (W : Win) (E : Expr2) : Option SymState :=
  if S.any (fun e => e.1 == W) then some (S.map fun e => if e.1 == W then (W, E) else e)
  else
    match S.findCover W with
    | some (W0, E0) =>
        some (S.map fun e =>
          if e.1 == W0 then (W0, Expr2.splice E0 W0.2.2 (W.2.1 - W0.2.1) W.2.2 E) else e)
    | none => if S.overlapsAny W then none else some (S ++ [(W, E)])

/-- The windows of a join: the first branch's, then the second branch's new
ones. -/
def joinWins (Sa Sb : SymState) : List Win :=
  Sa.map Prod.fst ++ (Sb.map Prod.fst).filter fun W => !(Sa.any fun e => e.1 == W)

/-- Join two branches under a known 1-bit guard `G`: every window either
branch wrote gets `G ? (branch a's value) : (branch b's value)`, a branch
that did not write it contributing the pre-state value (`lookupOr`); a
window both branches leave syntactically equal keeps that value
(`Expr2.joinIte`). The windows must be pairwise disjoint (a signal written
in different windows by the two branches refuses). -/
def join (G : Expr2) (Sa Sb : SymState) : Option SymState :=
  if Win.allDisjoint (joinWins Sa Sb) then
    some ((joinWins Sa Sb).map fun W => (W, Expr2.joinIte G (Sa.lookupOr W) (Sb.lookupOr W)))
  else none

end SymState

/-- Substitution under a slice: a slice of an identifier is a window read
(`SymState.readWin`); any other slice substitutes its base. -/
def Expr2.sliceSubst (d : Design2) (S : SymState) : Expr2 → Nat → Nat → Option Expr2 →
    Option Expr2
  | .ident n, lo, w, _ => if n ∈ d.symNames then S.readWin n lo w else none
  | _, lo, w, r => r.map fun a => .slice a lo w

mutual

/-- **Symbolic substitution**: rewrite an expression read at the CURRENT
point of a body into an expression over the body's pre-state — written
windows are replaced by their entries (`SymState.readWhole`,
`SymState.readWin`); `none` on an `.unsupported` node, an undeclared
identifier, or a read the symbolic state cannot express. -/
def Expr2.symSubst (d : Design2) (S : SymState) : Expr2 → Option Expr2
  | .lit v => some (.lit v)
  | .ident n => if n ∈ d.symNames then S.readWhole d n else none
  | .unsupported _ _ => none
  | .unary op a => (a.symSubst d S).map (.unary op)
  | .resizeSigned w a => (a.symSubst d S).map (.resizeSigned w)
  | .squash2 a => (a.symSubst d S).map .squash2
  | .repl k a => (a.symSubst d S).map (.repl k)
  | .reduce op a => (a.symSubst d S).map (.reduce op)
  | .resize w a => (a.symSubst d S).map (.resize w)
  | .binary op l r => (l.symSubst d S).bind fun l' => (r.symSubst d S).map (.binary op l')
  | .scmp op l r => (l.symSubst d S).bind fun l' => (r.symSubst d S).map (.scmp op l')
  | .logical b l r => (l.symSubst d S).bind fun l' => (r.symSubst d S).map (.logical b l')
  | .index a i w => (a.symSubst d S).bind fun a' => (i.symSubst d S).map fun i' => .index a' i' w
  | .ternary c t f =>
      (c.symSubst d S).bind fun c' => (t.symSubst d S).bind fun t' =>
        (f.symSubst d S).map (.ternary c' t')
  | .slice a lo w => Expr2.sliceSubst d S a lo w (a.symSubst d S)
  | .concat parts => (Expr2.listSymSubst d S parts.toList).map fun ps => .concat ps.toArray
termination_by structural e => e

/-- `Expr2.symSubst` of a list, elementwise. -/
def Expr2.listSymSubst (d : Design2) (S : SymState) : List Expr2 → Option (List Expr2)
  | [] => some []
  | e :: es => (e.symSubst d S).bind fun e' => (Expr2.listSymSubst d S es).map (e' :: ·)
termination_by structural es => es

end

/-- The static write window of a blocking-assignment target: a leaf
(whole signal, constant slice, constant-literal element select) with a
declared signal, inside its declared width. Concatenations and dynamic
selects refuse. -/
def Lhs2.symWin (d : Design2) (t : Lhs2) : Option Win :=
  match t with
  | .concat _ => none
  | _ =>
      (t.window? d).bind fun W =>
        (d.declWidth W.1).bind fun dw => if W.2.1 + W.2.2 ≤ dw then some W else none

mutual

/-- **Symbolic execution of an `always_comb` body** from a symbolic state
(`none`: outside the profile — see the module docstring). -/
def Stmt2.symExec (d : Design2) (S : SymState) : Stmt2 → Option SymState
  | .blockingAssign t e =>
      if e.wfB d then
        (e.symSubst d S).bind fun e' => (t.symWin d).bind fun W => S.write W (.resize W.2.2 e')
      else none
  | .ifStmt c t e =>
      if c.wfB d then
        (c.symSubst d S).bind fun c' => (t.symExec d S).bind fun St =>
          (Stmt2.symExecOpt d S e).bind fun Sf => SymState.join c'.ifGuard St Sf
      else none
  | .block body => Stmt2.symExecList d S body.toList
  | .caseStmt subj items dflt inside _ =>
      if subj.wfB d then
        (subj.symSubst d S).bind fun subj' => (Stmt2.symExecOpt d S dflt).bind fun Sd =>
          CaseItem2.symExecList d S subj' inside Sd items.toList
      else none
  | .nbaAssign _ _ => none
  | .unsupported _ _ => none
termination_by structural s => s

/-- `Stmt2.symExec` of an optional statement (`none`: no-op). -/
def Stmt2.symExecOpt (d : Design2) (S : SymState) : Option Stmt2 → Option SymState
  | none => some S
  | some s => s.symExec d S
termination_by structural o => o

/-- `Stmt2.symExec` of a statement list, in sequence. -/
def Stmt2.symExecList (d : Design2) (S : SymState) : List Stmt2 → Option SymState
  | [] => some S
  | s :: ss => (s.symExec d S).bind fun S' => Stmt2.symExecList d S' ss
termination_by structural ss => ss

/-- One `case` arm: its patterns (substituted) and its body's symbolic
state. -/
def CaseItem2.symArm (d : Design2) (S : SymState) : CaseItem2 → Option (List Expr2 × SymState)
  | .mk pats body =>
      if Expr2.listWfB d pats.toList then
        (Expr2.listSymSubst d S pats.toList).bind fun pats' =>
          (body.symExec d S).map fun Sb => (pats', Sb)
      else none
termination_by structural it => it

/-- The arms of a `case`, first match first, ending in the default's
symbolic state `Sd`: arm `k` joins its body with the rest under its hit
guard. -/
def CaseItem2.symExecList (d : Design2) (S : SymState) (subj : Expr2) (inside : Bool)
    (Sd : SymState) : List CaseItem2 → Option SymState
  | [] => some Sd
  | it :: rest =>
      (it.symArm d S).bind fun arm =>
        (CaseItem2.symExecList d S subj inside Sd rest).bind fun Sr =>
          SymState.join (Expr2.anyGuard inside subj arm.1) arm.2 Sr
termination_by structural its => its

end

/-! ## Static fuel bound of a body -/

mutual

/-- Fuel at which `execStmt2` runs a statement of the profile to completion
on every state (`symExec_total`). -/
def Stmt2.fuelB : Stmt2 → Nat
  | .blockingAssign _ e => e.size + 2
  | .ifStmt c t e => max (c.size + 1) (max t.fuelB (Stmt2.optFuelB e)) + 1
  | .block body => Stmt2.listFuelB body.toList + 1
  | .caseStmt subj items dflt _ _ =>
      max (subj.size + 1) (CaseItem2.listFuelB (Stmt2.optFuelB dflt) items.toList) + 1
  | .nbaAssign _ _ => 0
  | .unsupported _ _ => 0
termination_by structural s => s

/-- `Stmt2.fuelB` of an optional statement. -/
def Stmt2.optFuelB : Option Stmt2 → Nat
  | none => 0
  | some s => s.fuelB
termination_by structural o => o

/-- Fuel for `execStmts2` over a list (one unit per cell, the empty list
included). -/
def Stmt2.listFuelB : List Stmt2 → Nat
  | [] => 1
  | s :: ss => max s.fuelB (Stmt2.listFuelB ss) + 1
termination_by structural ss => ss

/-- Fuel for one `case` arm (its patterns and body). -/
def CaseItem2.fuelB : CaseItem2 → Nat
  | .mk pats body => max (Expr2.listSize pats.toList + 1) body.fuelB
termination_by structural it => it

/-- Fuel for `execCase2` over an arm list ending in a default of fuel
`fd`. -/
def CaseItem2.listFuelB (fd : Nat) : List CaseItem2 → Nat
  | [] => fd + 1
  | it :: rest => max it.fuelB (CaseItem2.listFuelB fd rest) + 1
termination_by structural its => its

end

/-! ## The lowering -/

/-- A window as a constant-slice assignment target `n[lo +: w]`. -/
def Win.lhs (W : Win) : Lhs2 := .slice W.1 W.2.1 W.2.2

namespace SymState

/-- The lowered target `{w₀, …, wₖ}` (entry order, MSB-first). -/
def target (S : SymState) : Lhs2 := .concat (S.map fun e => e.1.lhs)

/-- The lowered right-hand side `{E₀, …, Eₖ}`. -/
def rhs (S : SymState) : Expr2 := .concat (S.map Prod.snd).toArray

/-- The continuous assign an `always_comb` body lowers to. -/
def toAssign (S : SymState) : Process2 := .assign S.target S.rhs

/-- **No self-read**: no equation reads a window the body itself writes
(`Expr2.reads` of every entry, against every entry's window). Such a read is
the PRE-state value of a window the body overwrites: a read made before the
write (`y = t; t = a;`), or a value a join keeps (`Win.held` — a latch
`if (en) q = d;`, or `if (c) t = a; y = t; t = b;`). An event-driven
simulator runs an `always_comb` block once per wake-up and the block's own
writes never wake it again (IEEE 1800-2023 §9.2.2.2.1 leaves variables the
block writes out of its implicit sensitivity list; Icarus 12 measured
lagging on both bodies above), while the settle semantics re-runs every
comb process until nothing changes. The two agree on a block whose single
run is already a fixpoint of the block, and this check is what makes it one
(`runCombProcess2_alwaysComb_idem`). -/
def selfReadFree (S : SymState) : Bool :=
  (Expr2.listReads (S.map Prod.snd)).all fun r => (S.map Prod.fst).all fun W => !r.overlaps W

end SymState

/-- Lower one process: an assign is kept, an `always_comb` body in the
profile — symbolically executable (`Stmt2.symExec`) and free of self-reads
(`SymState.selfReadFree`) — becomes its `SymState.toAssign`, anything else
refuses. -/
def Process2.lowerComb (d : Design2) : Process2 → Option Process2
  | .assign t e => some (.assign t e)
  | .alwaysComb body =>
      (body.symExec d []).bind fun S => if S.selfReadFree then some S.toAssign else none
  | _ => none

/-- `Process2.lowerComb` over a process list (all or nothing). -/
def Design2.lowerProcs (d : Design2) : List Process2 → Option (List Process2)
  | [] => some []
  | p :: ps => (p.lowerComb d).bind fun q => (Design2.lowerProcs d ps).map (q :: ·)

/-- **Lower a design**: every `always_comb` body replaced by its continuous
assign; same name and declarations. `none` if some process is not an assign
or an `always_comb` in the profile. -/
def Design2.lowerComb (d : Design2) : Option Design2 :=
  (d.lowerProcs d.processes.toList).map fun ps => { d with processes := ps.toArray }

/-! ## Static facts -/

theorem Win.allDisjoint_iff : ∀ ws : List Win,
    Win.allDisjoint ws = true ↔ ws.Pairwise fun a b => Win.overlaps a b = false
  | [] => by simp [Win.allDisjoint]
  | W :: ws => by
      simp only [Win.allDisjoint, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
        List.pairwise_cons, Win.allDisjoint_iff ws]

/-- Two distinct members of a pairwise list are related (in one order). -/
theorem List.pairwise_of_mem_ne {α : Type} {R : α → α → Prop} (hsym : ∀ a b, R a b → R b a) :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b → R a b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: xs, h, a, b, ha, hb, hab => by
      rw [List.pairwise_cons] at h
      rcases List.mem_cons.mp ha with h1 | h1 <;> rcases List.mem_cons.mp hb with h2 | h2
      · exact absurd (h1.trans h2.symm) hab
      · subst h1; exact h.1 b h2
      · subst h2; exact hsym _ _ (h.1 a h1)
      · exact List.pairwise_of_mem_ne hsym h.2 h1 h2 hab

theorem Win.contains_iff {W V : Win} : Win.contains W V = true ↔
    W.1 = V.1 ∧ W.2.1 ≤ V.2.1 ∧ V.2.1 + V.2.2 ≤ W.2.1 + W.2.2 := by
  simp [Win.contains, and_assoc]

theorem Win.overlaps_symm_false {a b : Win} (h : Win.overlaps a b = false) :
    Win.overlaps b a = false := by rw [Win.overlaps_comm]; exact h

mutual
/-- `Expr2.same` is sound. -/
theorem Expr2.eq_of_same : ∀ (a b : Expr2), a.same b = true → a = b
  | .lit v, b, h => by cases b <;> simp_all [Expr2.same]
  | .ident n, b, h => by cases b <;> simp_all [Expr2.same]
  | .unsupported k x, b, h => by cases b <;> simp_all [Expr2.same]
  | .unary o a, b, h => by
      cases b <;> simp only [Expr2.same, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1, Expr2.eq_of_same _ _ h2]
  | .resizeSigned w a, b, h => by
      cases b <;> simp only [Expr2.same, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1, Expr2.eq_of_same _ _ h2]
  | .squash2 a, b, h => by
      cases b <;> simp only [Expr2.same, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h
      rw [Expr2.eq_of_same _ _ h]
  | .repl k a, b, h => by
      cases b <;> simp only [Expr2.same, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1, Expr2.eq_of_same _ _ h2]
  | .reduce o a, b, h => by
      cases b <;> simp only [Expr2.same, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1, Expr2.eq_of_same _ _ h2]
  | .resize w a, b, h => by
      cases b <;> simp only [Expr2.same, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [h1, Expr2.eq_of_same _ _ h2]
  | .binary o l r, b, h => by
      cases b <;> simp only [Expr2.same, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rw [h1, Expr2.eq_of_same _ _ h2, Expr2.eq_of_same _ _ h3]
  | .scmp o l r, b, h => by
      cases b <;> simp only [Expr2.same, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rw [h1, Expr2.eq_of_same _ _ h2, Expr2.eq_of_same _ _ h3]
  | .logical c l r, b, h => by
      cases b <;> simp only [Expr2.same, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rw [h1, Expr2.eq_of_same _ _ h2, Expr2.eq_of_same _ _ h3]
  | .index a i w, b, h => by
      cases b <;> simp only [Expr2.same, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rw [h1, Expr2.eq_of_same _ _ h2, Expr2.eq_of_same _ _ h3]
  | .ternary c t f, b, h => by
      cases b <;> simp only [Expr2.same, Bool.and_eq_true, reduceCtorEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rw [Expr2.eq_of_same _ _ h1, Expr2.eq_of_same _ _ h2, Expr2.eq_of_same _ _ h3]
  | .slice a lo w, b, h => by
      cases b <;> simp only [Expr2.same, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      rw [h1, h2, Expr2.eq_of_same _ _ h3]
  | .concat ps, b, h => by
      cases b <;> simp only [Expr2.same, reduceCtorEq] at h
      rename_i ps'
      have := Expr2.listEq_of_same ps.toList ps'.toList h
      cases ps; cases ps'; simp_all
termination_by structural a => a

/-- `Expr2.listSame` is sound. -/
theorem Expr2.listEq_of_same : ∀ (as bs : List Expr2), Expr2.listSame as bs = true → as = bs
  | [], bs, h => by cases bs <;> simp_all [Expr2.listSame]
  | a :: as, bs, h => by
      cases bs with
      | nil => simp [Expr2.listSame] at h
      | cons b bs =>
          simp only [Expr2.listSame, Bool.and_eq_true] at h
          rw [Expr2.eq_of_same _ _ h.1, Expr2.listEq_of_same _ _ h.2]
termination_by structural as => as
end

namespace SymState

theorem names_append (S T : SymState) : (S ++ T).names = S.names ++ T.names := by
  simp [names]

theorem mem_names {S : SymState} {n : String} : n ∈ S.names ↔ ∃ e ∈ S, e.1.1 = n := by
  simp [names]

theorem findWin_eq_some {S : SymState} {W : Win} {E : Expr2} (h : S.findWin W = some E) :
    (W, E) ∈ S := by
  simp only [findWin, Option.map_eq_some_iff] at h
  obtain ⟨⟨W', E'⟩, hf, rfl⟩ := h
  have hW : W' = W := by simpa using List.find?_some hf
  subst hW
  exact List.mem_of_find?_eq_some hf

theorem findWin_eq_none {S : SymState} {W : Win} (h : S.findWin W = none) :
    W ∉ S.map Prod.fst := by
  simp only [findWin, Option.map_eq_none_iff, List.find?_eq_none] at h
  intro hm
  obtain ⟨⟨W', E'⟩, hm', rfl⟩ := List.mem_map.mp hm
  simpa using h _ hm'

theorem findWin_of_mem {S : SymState} {W : Win} (h : W ∈ S.map Prod.fst) :
    ∃ E, S.findWin W = some E := by
  cases hf : S.findWin W with
  | none => exact absurd h (findWin_eq_none hf)
  | some E => exact ⟨E, rfl⟩

theorem findCover_eq_some {S : SymState} {V W : Win} {E : Expr2}
    (h : S.findCover V = some (W, E)) : (W, E) ∈ S ∧ Win.contains W V = true := by
  simp only [findCover] at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem findCover_eq_none {S : SymState} {V : Win} (h : S.findCover V = none) :
    ∀ e ∈ S, Win.contains e.1 V = false := by
  simp only [findCover, List.find?_eq_none] at h
  intro e he
  simpa using h e he

theorem overlapsAny_eq_false {S : SymState} {V : Win} (h : S.overlapsAny V = false) :
    ∀ W ∈ S.map Prod.fst, Win.overlaps W V = false := by
  simp only [overlapsAny, List.any_eq_false] at h
  intro W hW
  obtain ⟨⟨W', E'⟩, hm, rfl⟩ := List.mem_map.mp hW
  simpa using h _ hm

theorem writesName_eq_false {S : SymState} {n : String} (h : S.writesName n = false) :
    ∀ W ∈ S.map Prod.fst, W.1 ≠ n := by
  simp only [writesName, List.any_eq_false] at h
  intro W hW
  obtain ⟨⟨W', E'⟩, hm, rfl⟩ := List.mem_map.mp hW
  simpa using h _ hm

theorem writesName_eq_true {S : SymState} {n : String} (h : S.writesName n = true) :
    n ∈ S.names := by
  simp only [writesName, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨e, he, rfl⟩ := h
  exact mem_names.mpr ⟨e, he, rfl⟩

/-- The written signal is a name of the written symbolic state, and every
old name stays. -/
theorem write_names {S S' : SymState} {W : Win} {E : Expr2} (h : S.write W E = some S') :
    W.1 ∈ S'.names ∧ ∀ n ∈ S.names, n ∈ S'.names := by
  unfold write at h
  split at h
  · rename_i hany
    cases h
    refine ⟨?_, ?_⟩
    · simp only [List.any_eq_true, beq_iff_eq] at hany
      obtain ⟨e, he, hEq⟩ := hany
      refine mem_names.mpr ⟨(W, E), List.mem_map.mpr ⟨e, he, by simp [hEq]⟩, rfl⟩
    · intro n hn
      obtain ⟨e, he, rfl⟩ := mem_names.mp hn
      refine mem_names.mpr ⟨if e.1 == W then (W, E) else e, List.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
      by_cases hEq : e.1 = W
      · simp [hEq]
      · simp [hEq]
  · split at h
    · rename_i W0 E0 hc
      cases h
      obtain ⟨hm, hcont⟩ := findCover_eq_some hc
      have hn : W0.1 = W.1 := (Win.contains_iff.mp hcont).1
      refine ⟨?_, ?_⟩
      · refine mem_names.mpr ⟨(W0, Expr2.splice E0 W0.2.2 (W.2.1 - W0.2.1) W.2.2 E),
          List.mem_map.mpr ⟨(W0, E0), hm, by simp⟩, hn⟩
      · intro n hn'
        obtain ⟨e, he, rfl⟩ := mem_names.mp hn'
        refine mem_names.mpr ⟨_, List.mem_map.mpr ⟨e, he, rfl⟩, ?_⟩
        by_cases hEq : e.1 = W0
        · simp [hEq]
        · simp [hEq]
    · split at h
      · cases h
      · cases h
        exact ⟨by simp [names], fun n hn => by simp [names_append, hn]⟩

theorem mem_joinWins_left {Sa Sb : SymState} {W : Win} (h : W ∈ Sa.map Prod.fst) :
    W ∈ joinWins Sa Sb := List.mem_append_left _ h

theorem mem_joinWins_right {Sa Sb : SymState} {W : Win} (h : W ∈ Sb.map Prod.fst) :
    W ∈ joinWins Sa Sb := by
  by_cases ha : W ∈ Sa.map Prod.fst
  · exact List.mem_append_left _ ha
  · refine List.mem_append_right _ (List.mem_filter.mpr ⟨h, ?_⟩)
    simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq]
    intro e he hEq
    exact ha (List.mem_map.mpr ⟨e, he, hEq⟩)

theorem mem_joinWins {Sa Sb : SymState} {W : Win} (h : W ∈ joinWins Sa Sb) :
    W ∈ Sa.map Prod.fst ∨ W ∈ Sb.map Prod.fst := by
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_filter.mp h).1

/-- The windows of a join are the windows of its entries. -/
theorem join_wins {G : Expr2} {Sa Sb S' : SymState} (h : join G Sa Sb = some S') :
    S'.map Prod.fst = joinWins Sa Sb := by
  unfold join at h
  split at h
  · cases h; simp [List.map_map, Function.comp_def]
  · cases h

/-- Both branches' names are names of the join. -/
theorem join_names {G : Expr2} {Sa Sb S' : SymState} (h : join G Sa Sb = some S') :
    (∀ n ∈ Sa.names, n ∈ S'.names) ∧ (∀ n ∈ Sb.names, n ∈ S'.names) := by
  have hw := join_wins h
  have key : ∀ W ∈ joinWins Sa Sb, W.1 ∈ S'.names := by
    intro W hW
    rw [← hw] at hW
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hW
    exact mem_names.mpr ⟨e, he, rfl⟩
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨e, he, rfl⟩ := mem_names.mp hn
    exact key _ (mem_joinWins_left (List.mem_map_of_mem he))
  · obtain ⟨e, he, rfl⟩ := mem_names.mp hn
    exact key _ (mem_joinWins_right (List.mem_map_of_mem he))

end SymState

/-! ### Names only grow along symbolic execution -/

mutual

theorem Stmt2.symExec_names : ∀ (s : Stmt2) {d : Design2} {S S' : SymState},
    s.symExec d S = some S' → ∀ n ∈ S.names, n ∈ S'.names
  | .blockingAssign t e, d, S, S', h => by
      simp only [Stmt2.symExec] at h
      split at h
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨e', -, W, -, hw⟩ := h
        exact (SymState.write_names hw).2
      · cases h
  | .ifStmt c t e, d, S, S', h => by
      simp only [Stmt2.symExec] at h
      split at h
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨c', -, St, ht, Sf, -, hj⟩ := h
        exact fun n hn => (SymState.join_names hj).1 n (Stmt2.symExec_names t ht n hn)
      · cases h
  | .block body, d, S, S', h => by
      simp only [Stmt2.symExec] at h
      exact Stmt2.symExecList_names body.toList h
  | .caseStmt subj items dflt inside _, d, S, S', h => by
      simp only [Stmt2.symExec] at h
      split at h
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨subj', -, Sd, hd, hl⟩ := h
        exact fun n hn => CaseItem2.symExecList_names items.toList hl n
          (Stmt2.symExecOpt_names dflt hd n hn)
      · cases h
  | .nbaAssign _ _, d, S, S', h => by simp [Stmt2.symExec] at h
  | .unsupported _ _, d, S, S', h => by simp [Stmt2.symExec] at h
termination_by structural s => s

theorem Stmt2.symExecOpt_names : ∀ (o : Option Stmt2) {d : Design2} {S S' : SymState},
    Stmt2.symExecOpt d S o = some S' → ∀ n ∈ S.names, n ∈ S'.names
  | none, d, S, S', h => by
      simp only [Stmt2.symExecOpt, Option.some.injEq] at h
      subst h; exact fun _ h => h
  | some s, d, S, S', h => by
      simp only [Stmt2.symExecOpt] at h
      exact Stmt2.symExec_names s h
termination_by structural o => o

theorem Stmt2.symExecList_names : ∀ (ss : List Stmt2) {d : Design2} {S S' : SymState},
    Stmt2.symExecList d S ss = some S' → ∀ n ∈ S.names, n ∈ S'.names
  | [], d, S, S', h => by
      simp only [Stmt2.symExecList, Option.some.injEq] at h
      subst h; exact fun _ h => h
  | s :: ss, d, S, S', h => by
      simp only [Stmt2.symExecList, Option.bind_eq_some_iff] at h
      obtain ⟨S1, h1, h2⟩ := h
      exact fun n hn => Stmt2.symExecList_names ss h2 n (Stmt2.symExec_names s h1 n hn)
termination_by structural ss => ss

theorem CaseItem2.symExecList_names : ∀ (its : List CaseItem2) {d : Design2} {S : SymState}
    {subj : Expr2} {inside : Bool} {Sd S' : SymState},
    CaseItem2.symExecList d S subj inside Sd its = some S' →
      (∀ n ∈ Sd.names, n ∈ S'.names)
  | [], d, S, subj, inside, Sd, S', h => by
      simp only [CaseItem2.symExecList, Option.some.injEq] at h
      subst h; exact fun _ h => h
  | it :: rest, d, S, subj, inside, Sd, S', h => by
      simp only [CaseItem2.symExecList, Option.bind_eq_some_iff] at h
      obtain ⟨arm, -, Sr, hr, hj⟩ := h
      exact fun n hn => (SymState.join_names hj).2 n (CaseItem2.symExecList_names rest hr n hn)
termination_by structural its => its

end

/-- An arm's body state keeps the names of the starting state. -/
theorem CaseItem2.symArm_names : ∀ (it : CaseItem2) {d : Design2} {S : SymState}
    {pats : List Expr2} {Sb : SymState},
    it.symArm d S = some (pats, Sb) → ∀ n ∈ S.names, n ∈ Sb.names
  | .mk pats body, d, S, pats', Sb, h => by
      simp only [CaseItem2.symArm] at h
      split at h
      · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨p, -, Sb', hb, -, rfl⟩ := h
        exact Stmt2.symExec_names body hb
      · cases h

/-- The arms' names grow too: every name of the starting state reaches the
`case`'s result (through the default, which every arm list ends in). -/
theorem CaseItem2.symExecList_names_arm {d : Design2} {S : SymState} {subj : Expr2}
    {inside : Bool} {Sd S' : SymState} {its : List CaseItem2}
    (h : CaseItem2.symExecList d S subj inside Sd its = some S') {it : CaseItem2}
    (hit : it ∈ its) {pats : List Expr2} {Sb : SymState} (ha : it.symArm d S = some (pats, Sb)) :
    ∀ n ∈ Sb.names, n ∈ S'.names := by
  induction its generalizing S' with
  | nil => exact absurd hit List.not_mem_nil
  | cons it' rest ih =>
      simp only [CaseItem2.symExecList, Option.bind_eq_some_iff] at h
      obtain ⟨arm, harm, Sr, hr, hj⟩ := h
      rcases List.mem_cons.mp hit with rfl | hit
      · rw [ha, Option.some.injEq] at harm
        subst harm
        exact (SymState.join_names hj).1
      · exact fun n hn => (SymState.join_names hj).2 n (ih hr hit n hn)

/-! ## `LVec` facts used by the lowering -/

namespace LVec

/-- A vector resized to its own width is itself. -/
theorem resizeU_of_width {v : LVec} {w : Nat} (h : v.width = w) : v.resizeU w = v := by
  apply LVec.ext_getD (by simp [h])
  intro i hi
  simp only [LVec.width_resizeU] at hi
  simp only [LVec.resizeU, Array.getElem?_ofFn, hi, dite_true, Option.getD_some]
  have : i < v.bits.size := by rw [← h] at hi; exact hi
  simp [this]

/-- Bit `i` of a concatenation `{p, q}` (`q` in the low bits). -/
theorem getD_concat (p q : LVec) (i : Nat) :
    (p.concat q).bits[i]?.getD .lx =
      if i < q.width then q.bits[i]?.getD .lx else p.bits[i - q.width]?.getD .lx := by
  simp only [LVec.concat, LVec.width]
  rw [Array.getElem?_append]
  by_cases hi : i < q.bits.size <;> simp [hi]

@[simp] theorem width_concat (p q : LVec) : (p.concat q).width = p.width + q.width := by
  simp [LVec.concat, LVec.width, Nat.add_comm]

/-- The high part of `{p, q}` is `p`. -/
theorem extract_concat_hi (p q : LVec) : (p.concat q).extract q.width p.width = p := by
  apply LVec.ext_getD (by simp)
  intro i hi
  simp only [LVec.width_extract] at hi
  rw [LVec.getD_extract, if_pos hi, getD_concat, if_neg (by omega), Nat.add_sub_cancel_left]

/-- A window inside the low part of `{p, q}` is a window of `q`. -/
theorem extract_concat_lo (p q : LVec) {off w : Nat} (h : off + w ≤ q.width) :
    (p.concat q).extract off w = q.extract off w := by
  apply LVec.ext_getD (by simp)
  intro i hi
  simp only [LVec.width_extract] at hi
  rw [LVec.getD_extract, LVec.getD_extract, if_pos hi, if_pos hi, getD_concat, if_pos (by omega)]

/-- **A write inside a window, seen through the window**: writing `p` at
`lo` and reading the window `[lo0, lo0 + w0)` around it is writing `p` at the
relative offset into the window. -/
theorem extract_insertAt_inner {old p : LVec} {lo lo0 w0 : Nat} (h1 : lo0 ≤ lo)
    (h3 : lo + p.width ≤ old.width) :
    (old.insertAt lo p).extract lo0 w0 = (old.extract lo0 w0).insertAt (lo - lo0) p := by
  apply LVec.ext_getD (by simp)
  intro i hi
  simp only [LVec.width_extract] at hi
  rw [LVec.getD_extract, if_pos hi, LVec.getD_insertAt, LVec.getD_insertAt, LVec.width_extract,
    if_pos hi, LVec.getD_extract, if_pos hi]
  by_cases hin : lo - lo0 ≤ i ∧ i < lo - lo0 + p.width
  · rw [if_pos hin, if_pos ⟨by omega, by omega⟩, if_pos (by omega)]
    congr 2
    omega
  · rw [if_neg hin, if_neg (by omega)]

/-- **A write as a concatenation** `{v[w0-1 : r+k], p, v[r-1 : 0]}` (`k` the
part's width). -/
theorem insertAt_eq_concat {v p : LVec} {r : Nat} (h : r + p.width ≤ v.width) :
    v.insertAt r p =
      (v.extract (r + p.width) (v.width - (r + p.width))).concat (p.concat (v.extract 0 r)) := by
  apply LVec.ext_getD (by simp; omega)
  intro i hi
  simp only [LVec.width_insertAt] at hi
  rw [LVec.getD_insertAt, if_pos hi, getD_concat, getD_concat]
  simp only [LVec.width_concat, LVec.width_extract]
  by_cases hlo : i < r
  · rw [if_neg (by omega), if_pos (by omega), if_pos hlo, LVec.getD_extract, if_pos hlo,
      Nat.zero_add]
  · by_cases hmid : i < r + p.width
    · rw [if_pos ⟨by omega, hmid⟩, if_pos (by omega), if_neg hlo]
    · rw [if_neg (by omega), if_neg (by omega), LVec.getD_extract, if_pos (by omega)]
      congr 2
      omega

end LVec

/-! ## `ReadWin` helpers -/

/-- A window agreement whose right-hand state binds the signal hands over a
binding of the left-hand state with the same width and window. -/
theorem ReadWin.agree_win_some {st st' : SvState} {n : String} {lo w : Nat}
    (h : (ReadWin.win n lo w).agree st st') {u' : LVec}
    (hu' : SvState.lookup st' n = some u') :
    ∃ u, SvState.lookup st n = some u ∧ u.width = u'.width ∧ u.extract lo w = u'.extract lo w := by
  simp only [ReadWin.agree, hu', Option.map_some] at h
  cases hu : SvState.lookup st n with
  | none => rw [hu] at h; cases h
  | some u =>
      rw [hu] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨u, rfl, h.1, h.2⟩

/-- A 1-bit read of a bit inside a window that overlaps nothing overlaps
nothing. -/
theorem ReadWin.bit_overlaps_false {n : String} {lo w k : Nat} {V : Win} (hk : k < w)
    (h : Win.overlaps (n, lo, w) V = false) :
    (ReadWin.win n (lo + k) 1).overlaps V = false :=
  Bool.eq_false_iff.mpr fun hov => by
    have := Comb2Term.overlaps_win_of_bit hk hov
    simp only [ReadWin.overlaps] at this
    rw [h] at this
    cases this

/-! ## The semantics of a symbolic state -/

/-- **`S` describes `st` over the pre-state `st₀`**: same keys and widths;
the entry windows are pairwise disjoint; every entry window holds the value
of its expression in `st₀` (whenever that evaluates); every bit outside the
entry windows is `st₀`'s. -/
structure SymRel (st₀ : SvState) (S : SymState) (st : SvState) : Prop where
  /-- Same key list as the pre-state. -/
  keys : st.map Prod.fst = st₀.map Prod.fst
  /-- Same widths as the pre-state. -/
  width : ∀ n, (SvState.lookup st n).map LVec.width = (SvState.lookup st₀ n).map LVec.width
  /-- The entry windows are pairwise disjoint. -/
  disj : (S.map Prod.fst).Pairwise fun a b => Win.overlaps a b = false
  /-- Every entry window holds its expression's pre-state value. -/
  entry : ∀ W E, (W, E) ∈ S → ∀ v, evalPure2 st₀ E = .ok v →
    ∃ u, SvState.lookup st W.1 = some u ∧ u.extract W.2.1 W.2.2 = v
  /-- Every bit outside the entry windows is the pre-state's. -/
  frame : ∀ n b, (∀ W ∈ S.map Prod.fst, (ReadWin.win n b 1).overlaps W = false) →
    (ReadWin.win n b 1).agree st st₀

/-- The empty symbolic state describes the pre-state. -/
theorem SymRel.init (st₀ : SvState) : SymRel st₀ [] st₀ :=
  ⟨rfl, fun _ => rfl, List.Pairwise.nil, fun _ _ h => absurd h List.not_mem_nil,
    fun _ _ _ => ReadWin.agree_refl _ _⟩

/-- Width facts about the pre-state for the signals a symbolic state writes:
each is bound at its declared width. -/
def SymOk (d : Design2) (st₀ : SvState) (S : SymState) : Prop :=
  ∀ n ∈ S.names, ∀ dw, d.declWidth n = some dw → (SvState.lookup st₀ n).map LVec.width = some dw

theorem SymOk.mono {d : Design2} {st₀ : SvState} {S S' : SymState} (h : SymOk d st₀ S')
    (hm : ∀ n ∈ S.names, n ∈ S'.names) : SymOk d st₀ S :=
  fun n hn => h n (hm n hn)

namespace SymRel

variable {st₀ st : SvState} {S : SymState}

/-- A window disjoint from every entry window is the pre-state's. -/
theorem win_of_disjoint (hR : SymRel st₀ S st) {n : String} {lo w : Nat}
    (h : ∀ W ∈ S.map Prod.fst, Win.overlaps (n, lo, w) W = false) :
    (ReadWin.win n lo w).agree st st₀ :=
  ReadWin.agree_win_of_bits (hR.width n) fun _ hk =>
    hR.frame n _ fun W hW => ReadWin.bit_overlaps_false hk (h W hW)

/-- A signal no entry writes is the pre-state's. -/
theorem lookup_of_not_written (hR : SymRel st₀ S st) {n : String}
    (h : ∀ W ∈ S.map Prod.fst, W.1 ≠ n) : SvState.lookup st n = SvState.lookup st₀ n :=
  ReadWin.lookup_eq_of_agree_bits fun b => hR.frame n b fun W hW => by
    obtain ⟨m, lo, w⟩ := W
    have hne : n ≠ m := fun hnm => h _ hW hnm.symm
    simp [ReadWin.overlaps, Win.overlaps, hne]

/-- A bound signal stays bound. -/
theorem lookup_some (hR : SymRel st₀ S st) {n : String} {u₀ : LVec}
    (h : SvState.lookup st₀ n = some u₀) : ∃ u, SvState.lookup st n = some u ∧ u.width = u₀.width := by
  have := hR.width n
  rw [h] at this
  cases hu : SvState.lookup st n with
  | none => rw [hu] at this; cases this
  | some u => rw [hu] at this; exact ⟨u, rfl, by simpa using this⟩

end SymRel

/-! ### Substitution is sound -/

/-- `x` decides `.ok a` only if `y` decides `.ok a` too. -/
def ResOkImp {α : Type} (x y : Res α) : Prop := ∀ a, x = .ok a → y = .ok a

theorem ResOkImp.refl {α : Type} (x : Res α) : ResOkImp x x := fun _ h => h

theorem ResOkImp.bind {α β : Type} {x y : Res α} {f g : α → Res β} (h : ResOkImp x y)
    (hf : ∀ a, ResOkImp (f a) (g a)) : ResOkImp (x >>= f) (y >>= g) := by
  intro b hb
  cases hx : x with
  | ok a =>
      rw [hx] at hb
      rw [h a hx]
      exact hf a b hb
  | timeout => rw [hx] at hb; cases hb
  | unsupported msg => rw [hx] at hb; cases hb

/-- Substitution under a slice of a non-identifier is the slice of the
substituted base. -/
theorem Expr2.sliceSubst_of_not_ident {d : Design2} {S : SymState} {a : Expr2}
    (h : ∀ x, a ≠ .ident x) (lo w : Nat) (r : Option Expr2) :
    Expr2.sliceSubst d S a lo w r = r.map fun a' => .slice a' lo w := by
  cases a <;> first | rfl | exact absurd rfl (h _)

private theorem symSubst_aux {d : Design2} {S : SymState} {st₀ st : SvState}
    (hR : SymRel st₀ S st) (hok : SymOk d st₀ S) : ∀ n : Nat,
    (∀ e : Expr2, e.size < n → ∀ e', e.symSubst d S = some e' →
      ResOkImp (evalPure2 st₀ e') (evalPure2 st e)) ∧
    (∀ es : List Expr2, Expr2.listSize es < n → ∀ es', Expr2.listSymSubst d S es = some es' →
      ResOkImp (evalPures2 st₀ es') (evalPures2 st es))
  | 0 => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨ihE, ihL⟩ := symSubst_aux hR hok n
    refine ⟨fun e hs e' h => ?_, fun es hs es' h => ?_⟩
    · cases e with
      | lit v =>
          simp only [Expr2.symSubst, Option.some.injEq] at h
          subst h
          exact ResOkImp.refl _
      | ident x =>
          simp only [Expr2.symSubst] at h
          split at h
          · simp only [SymState.readWhole] at h
            split at h
            · next hwn =>
              simp only [Option.bind_eq_some_iff] at h
              obtain ⟨dw, hdw, hf⟩ := h
              have hm := SymState.findWin_eq_some hf
              intro v hv
              obtain ⟨u, hu, hext⟩ := hR.entry _ _ hm v hv
              have hw := (hR.width x).trans (hok x (SymState.writesName_eq_true hwn) dw hdw)
              rw [hu] at hw
              simp only [Option.map_some, Option.some.injEq] at hw
              simp only at hext
              rw [← hw, LVec.extract_full] at hext
              simp [evalPure2, readSignal, hu, hext]
            · next hwn =>
              cases h
              intro v hv
              have hl := hR.lookup_of_not_written
                (SymState.writesName_eq_false (Bool.eq_false_iff.mpr hwn))
              simpa [evalPure2, readSignal, hl] using hv
          · cases h
      | unsupported => simp [Expr2.symSubst] at h
      | unary op a =>
          simp only [Expr2.symSubst, Option.map_eq_some_iff] at h
          obtain ⟨a', ha, rfl⟩ := h
          simp only [Expr2.size] at hs
          simp only [evalPure2]
          exact ResOkImp.bind (ihE a (by omega) a' ha) fun _ => ResOkImp.refl _
      | resizeSigned w a =>
          simp only [Expr2.symSubst, Option.map_eq_some_iff] at h
          obtain ⟨a', ha, rfl⟩ := h
          simp only [Expr2.size] at hs
          simp only [evalPure2]
          exact ResOkImp.bind (ihE a (by omega) a' ha) fun _ => ResOkImp.refl _
      | squash2 a =>
          simp only [Expr2.symSubst, Option.map_eq_some_iff] at h
          obtain ⟨a', ha, rfl⟩ := h
          simp only [Expr2.size] at hs
          simp only [evalPure2]
          exact ResOkImp.bind (ihE a (by omega) a' ha) fun _ => ResOkImp.refl _
      | repl k a =>
          simp only [Expr2.symSubst, Option.map_eq_some_iff] at h
          obtain ⟨a', ha, rfl⟩ := h
          simp only [Expr2.size] at hs
          simp only [evalPure2]
          exact ResOkImp.bind (ihE a (by omega) a' ha) fun _ => ResOkImp.refl _
      | reduce op a =>
          simp only [Expr2.symSubst, Option.map_eq_some_iff] at h
          obtain ⟨a', ha, rfl⟩ := h
          simp only [Expr2.size] at hs
          simp only [evalPure2]
          exact ResOkImp.bind (ihE a (by omega) a' ha) fun _ => ResOkImp.refl _
      | resize w a =>
          simp only [Expr2.symSubst, Option.map_eq_some_iff] at h
          obtain ⟨a', ha, rfl⟩ := h
          simp only [Expr2.size] at hs
          simp only [evalPure2]
          exact ResOkImp.bind (ihE a (by omega) a' ha) fun _ => ResOkImp.refl _
      | binary op l r =>
          simp only [Expr2.symSubst, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
          obtain ⟨l', hl, r', hr, rfl⟩ := h
          simp only [Expr2.size] at hs
          simp only [evalPure2]
          exact ResOkImp.bind (ihE l (by omega) l' hl) fun _ =>
            ResOkImp.bind (ihE r (by omega) r' hr) fun _ => ResOkImp.refl _
      | scmp op l r =>
          simp only [Expr2.symSubst, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
          obtain ⟨l', hl, r', hr, rfl⟩ := h
          simp only [Expr2.size] at hs
          simp only [evalPure2]
          exact ResOkImp.bind (ihE l (by omega) l' hl) fun _ =>
            ResOkImp.bind (ihE r (by omega) r' hr) fun _ => ResOkImp.refl _
      | logical b l r =>
          simp only [Expr2.symSubst, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
          obtain ⟨l', hl, r', hr, rfl⟩ := h
          simp only [Expr2.size] at hs
          simp only [evalPure2]
          exact ResOkImp.bind (ihE l (by omega) l' hl) fun _ =>
            ResOkImp.bind (ihE r (by omega) r' hr) fun _ => ResOkImp.refl _
      | index a i w =>
          simp only [Expr2.symSubst, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
          obtain ⟨a', ha, i', hi, rfl⟩ := h
          simp only [Expr2.size] at hs
          simp only [evalPure2]
          exact ResOkImp.bind (ihE a (by omega) a' ha) fun _ =>
            ResOkImp.bind (ihE i (by omega) i' hi) fun _ => ResOkImp.refl _
      | ternary c t f =>
          simp only [Expr2.symSubst, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
          obtain ⟨c', hc, t', ht, f', hf, rfl⟩ := h
          simp only [Expr2.size] at hs
          simp only [evalPure2]
          exact ResOkImp.bind (ihE c (by omega) c' hc) fun _ =>
            ResOkImp.bind (ihE t (by omega) t' ht) fun _ =>
              ResOkImp.bind (ihE f (by omega) f' hf) fun _ => ResOkImp.refl _
      | concat parts =>
          simp only [Expr2.symSubst, Option.map_eq_some_iff] at h
          obtain ⟨ps, hps, rfl⟩ := h
          simp only [Expr2.size] at hs
          simp only [evalPure2]
          exact ResOkImp.bind (ihL parts.toList (by omega) ps hps) fun _ => ResOkImp.refl _
      | slice a lo w =>
          simp only [Expr2.symSubst] at h
          by_cases ha : ∃ x, a = .ident x
          · obtain ⟨x, rfl⟩ := ha
            simp only [Expr2.sliceSubst] at h
            split at h
            · simp only [SymState.readWin] at h
              split at h
              · next W E hc =>
                cases h
                obtain ⟨hm, hcont⟩ := SymState.findCover_eq_some hc
                obtain ⟨hn, hlo, hhi⟩ := Win.contains_iff.mp hcont
                intro v hv
                simp only [evalPure2, Pure2.res_bind_eq_ok, Pure2.res_pure_eq,
                  Res.ok.injEq] at hv
                obtain ⟨vE, hvE, rfl⟩ := hv
                obtain ⟨u, hu, hext⟩ := hR.entry _ _ hm vE hvE
                simp only at hn hlo hhi
                rw [hn] at hu
                have hx := LVec.extract_extract u (lo := W.2.1) (w := W.2.2) (lo' := lo - W.2.1)
                  (w' := w) (by omega)
                rw [Nat.add_sub_cancel' hlo, hext] at hx
                simp [evalPure2, readSignal, hu, hx]
              · next hc =>
                split at h
                · cases h
                · next hov =>
                  cases h
                  intro v hv
                  have hag := hR.win_of_disjoint (n := x) (lo := lo) (w := w) fun W hW =>
                    Win.overlaps_symm_false
                      (SymState.overlapsAny_eq_false (Bool.eq_false_iff.mpr hov) W hW)
                  rw [evalPure2_congr_reads (st := st) (st' := st₀) (e := .slice (.ident x) lo w)
                    (by intro r hr; simp [Expr2.reads, Expr2.sliceReads] at hr; subst hr; exact hag)]
                  exact hv
            · cases h
          · rw [Expr2.sliceSubst_of_not_ident (fun x hx => ha ⟨x, hx⟩)] at h
            simp only [Option.map_eq_some_iff] at h
            obtain ⟨a', ha', rfl⟩ := h
            simp only [Expr2.size] at hs
            simp only [evalPure2]
            exact ResOkImp.bind (ihE a (by omega) a' ha') fun _ => ResOkImp.refl _
    · cases es with
      | nil =>
          simp only [Expr2.listSymSubst, Option.some.injEq] at h
          subst h
          exact ResOkImp.refl _
      | cons e rest =>
          simp only [Expr2.listSymSubst, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
          obtain ⟨e', he, rest', hrest, rfl⟩ := h
          simp only [Expr2.listSize] at hs
          simp only [evalPures2]
          exact ResOkImp.bind (ihE e (by omega) e' he) fun _ =>
            ResOkImp.bind (ihL rest (by omega) rest' hrest) fun _ => ResOkImp.refl _

/-- **Substitution is sound**: if the substituted expression evaluates in
the pre-state, the original evaluates to the same value in any state the
symbolic state describes. -/
theorem Expr2.symSubst_sound {d : Design2} {S : SymState} {st₀ st : SvState}
    (hR : SymRel st₀ S st) (hok : SymOk d st₀ S) {e e' : Expr2} (h : e.symSubst d S = some e')
    {v : LVec} (hv : evalPure2 st₀ e' = .ok v) : evalPure2 st e = .ok v :=
  (symSubst_aux hR hok (e.size + 1)).1 e (Nat.lt_succ_self _) e' h v hv

/-- List twin of `Expr2.symSubst_sound`. -/
theorem Expr2.listSymSubst_sound {d : Design2} {S : SymState} {st₀ st : SvState}
    (hR : SymRel st₀ S st) (hok : SymOk d st₀ S) {es es' : List Expr2}
    (h : Expr2.listSymSubst d S es = some es') {vs : List LVec}
    (hv : evalPures2 st₀ es' = .ok vs) : evalPures2 st es = .ok vs :=
  (symSubst_aux hR hok (Expr2.listSize es + 1)).2 es (Nat.lt_succ_self _) es' h vs hv

/-! ### Guards -/

private theorem foldl_or_eq_l1 : ∀ (l : List Logic) (a : Logic),
    l.foldl Logic.or a = .l1 ↔ a = .l1 ∨ ∃ x ∈ l, x = .l1
  | [], a => by simp
  | x :: xs, a => by
      rw [List.foldl_cons, foldl_or_eq_l1 xs]
      have h : Logic.or a x = .l1 ↔ a = .l1 ∨ x = .l1 := by cases a <;> cases x <;> decide
      rw [h]
      simp only [List.mem_cons, exists_eq_or_imp]
      constructor
      · rintro ((h | h) | h) <;> simp_all
      · rintro (h | h | h) <;> simp_all

/-- `|v` is `1` exactly when `v` has a `1` bit — the `if` truthiness. -/
theorem LVec.redOr_eq_l1_iff (v : LVec) : v.redOr = .l1 ↔ v.condTrue = true := by
  rw [LVec.redOr, LVec.condTrue, ← Array.foldl_toList, foldl_or_eq_l1, Array.any_eq_true']
  simp

/-- `?:` on a known `1` picks the first arm. -/
theorem LVec.ternary_ofLogic_l1 (a b : LVec) : LVec.ternary (LVec.ofLogic .l1) a b = a := by
  simp only [LVec.ternary]; rw [if_pos (by simp [LVec.condTrue, LVec.ofLogic])]

/-- `?:` on a known `0` picks the second arm. -/
theorem LVec.ternary_ofLogic_l0 (a b : LVec) : LVec.ternary (LVec.ofLogic .l0) a b = b := by
  simp only [LVec.ternary]
  rw [if_neg (by simp [LVec.condTrue, LVec.ofLogic]),
    if_pos (by simp [LVec.isKnownZero, LVec.ofLogic])]

theorem LVec.ofLogic_beq_l1 (a : Logic) : (LVec.ofLogic a == LVec.ofLogic .l1) = (a == .l1) := by
  cases a <;> decide

theorem LVec.or_ofLogic (a b : Logic) :
    (LVec.ofLogic a).or (LVec.ofLogic b) = LVec.ofLogic (Logic.or a b) := by
  simp [LVec.or, LVec.zipWith, LVec.ofLogic, LVec.width]

/-- A boolean as a known bit. -/
abbrev Logic.ofB (b : Bool) : Logic := if b then .l1 else .l0

@[simp] theorem Logic.ofB_true : Logic.ofB true = .l1 := rfl
@[simp] theorem Logic.ofB_false : Logic.ofB false = .l0 := rfl

/-- **The `if` guard decides like `if`**: whenever it evaluates, its
condition evaluates, and the guard is the known bit of the condition's
truthiness. -/
theorem evalPure2_ifGuard {st : SvState} {c : Expr2} {g : LVec}
    (h : evalPure2 st c.ifGuard = .ok g) :
    ∃ cv, evalPure2 st c = .ok cv ∧ g = LVec.ofLogic (Logic.ofB cv.condTrue) := by
  simp only [Expr2.ifGuard, evalPure2, Pure2.res_bind_eq_ok, Pure2.res_pure_eq, Res.ok.injEq] at h
  obtain ⟨a, ⟨cv, hcv, rfl⟩, b, rfl, rfl⟩ := h
  refine ⟨cv, hcv, ?_⟩
  simp only [evalBinOp, evalRedOp, LVec.eqCase, LVec.ofLogic_beq_l1, Logic.ofB]
  by_cases hc : cv.condTrue = true
  · rw [if_pos hc, if_pos (by simpa using (LVec.redOr_eq_l1_iff cv).mpr hc)]
  · rw [if_neg hc, if_neg (by simpa using fun h => hc ((LVec.redOr_eq_l1_iff cv).mp h))]

/-- **A pattern guard decides like `caseHit`.** -/
theorem evalPure2_hitGuard {st : SvState} {inside : Bool} {subj pat : Expr2} {g : LVec}
    (h : evalPure2 st (Expr2.hitGuard inside subj pat) = .ok g) :
    ∃ sv pv, evalPure2 st subj = .ok sv ∧ evalPure2 st pat = .ok pv ∧
      g = LVec.ofLogic (Logic.ofB (caseHit inside sv pv)) := by
  cases inside with
  | false =>
      simp only [Expr2.hitGuard, Bool.false_eq_true, ↓reduceIte, evalPure2,
        Pure2.res_bind_eq_ok, Pure2.res_pure_eq, Res.ok.injEq] at h
      obtain ⟨sv, hsv, pv, hpv, rfl⟩ := h
      refine ⟨sv, pv, hsv, hpv, ?_⟩
      simp only [evalBinOp, LVec.eqCase, caseHit, Bool.false_eq_true, ↓reduceIte, Logic.ofB]
  | true =>
      simp only [Expr2.hitGuard, ↓reduceIte, evalPure2,
        Pure2.res_bind_eq_ok, Pure2.res_pure_eq, Res.ok.injEq] at h
      obtain ⟨a, ⟨sv, hsv, pv, hpv, rfl⟩, b, rfl, rfl⟩ := h
      refine ⟨sv, pv, hsv, hpv, ?_⟩
      simp only [evalBinOp, LVec.eqCase, LVec.ofLogic_beq_l1, caseHit, ↓reduceIte,
        LVec.matchesWild, Logic.ofB]

/-- **An arm guard decides like the arm's hit test** (`pvs.any (caseHit …)`),
whenever the subject's value is `sv`. -/
theorem evalPure2_anyGuard {st : SvState} {inside : Bool} {subj : Expr2} {sv : LVec}
    (hs : ∀ v, evalPure2 st subj = .ok v → v = sv) :
    ∀ {pats : List Expr2} {g : LVec}, evalPure2 st (Expr2.anyGuard inside subj pats) = .ok g →
      ∃ pvs, evalPures2 st pats = .ok pvs ∧
        g = LVec.ofLogic (Logic.ofB (pvs.any fun pv => caseHit inside sv pv))
  | [], g, h => by
      simp only [Expr2.anyGuard, evalPure2, Res.ok.injEq] at h
      exact ⟨[], rfl, by simp [h, Logic.ofB]⟩
  | p :: ps, g, h => by
      simp only [Expr2.anyGuard, evalPure2_binary, Pure2.res_bind_eq_ok, Pure2.res_pure_eq,
        Res.ok.injEq] at h
      obtain ⟨g1, h1, g2, h2, rfl⟩ := h
      obtain ⟨sv', pv, hsv', hpv, rfl⟩ := evalPure2_hitGuard h1
      obtain ⟨pvs, hpvs, rfl⟩ := evalPure2_anyGuard hs h2
      have hsv := hs sv' hsv'
      subst hsv
      refine ⟨pv :: pvs, by simp [evalPures2, hpv, hpvs], ?_⟩
      simp only [evalBinOp, LVec.or_ofLogic, List.any_cons, Logic.ofB]
      by_cases h1b : caseHit inside sv' pv = true <;>
        by_cases h2b : (pvs.any fun pv => caseHit inside sv' pv) = true <;>
        simp only [h1b, h2b, Bool.or_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte] <;>
        simp_all [Logic.or]

/-! ### Writes and joins are sound -/

/-- A held window evaluates to the pre-state window. -/
theorem evalPure2_held {st : SvState} {W : Win} {v : LVec} (h : evalPure2 st W.held = .ok v) :
    ∃ u, SvState.lookup st W.1 = some u ∧ v = u.extract W.2.1 W.2.2 := by
  cases hl : SvState.lookup st W.1 with
  | none => simp [Win.held, evalPure2, readSignal, hl] at h
  | some u =>
      simp [Win.held, evalPure2, readSignal, hl] at h
      exact ⟨u, rfl, h.symm⟩

/-- A splice evaluates to the concatenation of its three parts. -/
theorem evalPure2_splice {st : SvState} {E0 E : Expr2} {w0 r w : Nat} {v : LVec}
    (h : evalPure2 st (Expr2.splice E0 w0 r w E) = .ok v) :
    ∃ v0 p, evalPure2 st E0 = .ok v0 ∧ evalPure2 st E = .ok p ∧
      v = (v0.extract (r + w) (w0 - (r + w))).concat (p.concat (v0.extract 0 r)) := by
  cases h0 : evalPure2 st E0 with
  | ok v0 =>
      cases h1 : evalPure2 st E with
      | ok p =>
          simp [Expr2.splice, evalPure2, evalPures2, h0, h1] at h
          exact ⟨v0, p, rfl, rfl, h.symm⟩
      | timeout => simp [Expr2.splice, evalPure2, evalPures2, h0, h1] at h
      | unsupported m => simp [Expr2.splice, evalPure2, evalPures2, h0, h1] at h
  | timeout => simp [Expr2.splice, evalPure2, evalPures2, h0] at h
  | unsupported m => simp [Expr2.splice, evalPure2, evalPures2, h0] at h

namespace SymState

theorem map_fst_replace (S : SymState) (W : Win) (f : Expr2) :
    (S.map fun e => if e.1 == W then (W, f) else e).map Prod.fst = S.map Prod.fst := by
  induction S with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.map_cons, ih, List.cons.injEq, and_true]
      by_cases h : e.1 = W <;> simp [h]

theorem mem_replace {S : SymState} {W : Win} {f : Expr2} {V : Win} {F : Expr2}
    (h : (V, F) ∈ S.map fun e => if e.1 == W then (W, f) else e) :
    (V = W ∧ F = f) ∨ ((V, F) ∈ S ∧ V ≠ W) := by
  obtain ⟨e, he, heq⟩ := List.mem_map.mp h
  by_cases hW : e.1 = W
  · simp only [hW, beq_self_eq_true, ↓reduceIte, Prod.mk.injEq] at heq
    exact Or.inl ⟨heq.1.symm, heq.2.symm⟩
  · have : (e.1 == W) = false := by simpa using hW
    rw [this] at heq
    simp only [Bool.false_eq_true, ↓reduceIte] at heq
    subst heq
    exact Or.inr ⟨he, hW⟩

/-- Two distinct windows of a symbolic state described by `SymRel` are
disjoint. -/
theorem disj_of_ne {st₀ st : SvState} {S : SymState} (hR : SymRel st₀ S st) {V W : Win}
    (hV : V ∈ S.map Prod.fst) (hW : W ∈ S.map Prod.fst) (hne : V ≠ W) :
    Win.overlaps V W = false :=
  List.pairwise_of_mem_ne (fun _ _ h => Win.overlaps_symm_false h) hR.disj hV hW hne

/-- A 1-bit read outside a containing window is outside every contained one. -/
theorem bit_not_overlaps_of_contains {W0 W : Win} (hc : Win.contains W0 W = true) {m : String}
    {b : Nat} (h : (ReadWin.win m b 1).overlaps W0 = false) :
    (ReadWin.win m b 1).overlaps W = false := by
  obtain ⟨n0, lo0, w0⟩ := W0
  obtain ⟨n, lo, w⟩ := W
  obtain ⟨hn, hlo, hhi⟩ := Win.contains_iff.mp hc
  simp only at hn hlo hhi
  subst hn
  rw [← Bool.not_eq_true, ReadWin.overlaps_win_one] at h ⊢
  rintro ⟨hm, h1, h2⟩
  exact h ⟨hm, by omega, by omega⟩

/-- A window disjoint from a containing window is disjoint from every
contained one. -/
theorem overlaps_false_of_contains {W0 W V : Win} (hc : Win.contains W0 W = true)
    (h : Win.overlaps V W0 = false) : Win.overlaps V W = false := by
  obtain ⟨n0, lo0, w0⟩ := W0
  obtain ⟨n, lo, w⟩ := W
  obtain ⟨m, lo', w'⟩ := V
  obtain ⟨hn, hlo, hhi⟩ := Win.contains_iff.mp hc
  simp only at hn hlo hhi
  subst hn
  rw [Win.overlaps_eq_false] at h ⊢
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

/-- **A blocking write is sound**: writing `p` (the value the symbolic
expression `E` denotes) into window `W` (bound and in range) of a state the
symbolic state describes gives a state the written symbolic state
describes. -/
theorem write_sound {S S' : SymState} {W : Win} {E : Expr2} (hw : S.write W E = some S')
    {st₀ st : SvState} (hR : SymRel st₀ S st) {old p : LVec}
    (hold : SvState.lookup st W.1 = some old) (hin : W.2.1 + W.2.2 ≤ old.width)
    (hp : p.width = W.2.2) (hE : ∀ v, evalPure2 st₀ E = .ok v → v = p) :
    SymRel st₀ S' (SvState.set st W.1 (old.insertAt W.2.1 p)) := by
  obtain ⟨n, lo, w⟩ := W
  simp only at hold hin hp ⊢
  have hkeys : (SvState.set st n (old.insertAt lo p)).map Prod.fst = st₀.map Prod.fst := by
    rw [SvState.keys_set _ (SvState.lookup_isSome_iff.mp (by simp [hold])), hR.keys]
  have hwidth : ∀ m, (SvState.lookup (SvState.set st n (old.insertAt lo p)) m).map LVec.width =
      (SvState.lookup st₀ m).map LVec.width := by
    intro m
    rw [← hR.width m, SvState.lookup_set]
    by_cases h : n = m
    · subst h; simp [hold]
    · simp [h]
  have hframe : ∀ r : ReadWin, r.overlaps (n, lo, w) = false →
      r.agree st (SvState.set st n (old.insertAt lo p)) :=
    fun r hr => ReadWin.agree_set hold hp hr
  have hkeep : ∀ V F, (V, F) ∈ S → Win.overlaps V (n, lo, w) = false →
      ∀ v, evalPure2 st₀ F = .ok v →
        ∃ u, SvState.lookup (SvState.set st n (old.insertAt lo p)) V.1 = some u ∧
          u.extract V.2.1 V.2.2 = v := by
    intro V F hm hov v hv
    obtain ⟨u, hu, hext⟩ := hR.entry V F hm v hv
    obtain ⟨u', hu', -, hext'⟩ := ReadWin.agree_win_some
      (ReadWin.agree_symm (hframe (.win V.1 V.2.1 V.2.2) hov)) hu
    exact ⟨u', hu', hext'.trans hext⟩
  have hnew : SvState.lookup (SvState.set st n (old.insertAt lo p)) n =
      some (old.insertAt lo p) := SvState.lookup_set_self _ _ _
  have hbit : ∀ m b, (ReadWin.win m b 1).overlaps (n, lo, w) = false →
      (ReadWin.win m b 1).agree st st₀ →
      (ReadWin.win m b 1).agree (SvState.set st n (old.insertAt lo p)) st₀ :=
    fun m b hov hag => ReadWin.agree_trans (ReadWin.agree_symm (hframe _ hov)) hag
  unfold write at hw
  split at hw
  · -- the exact window is already an entry: replace it
    next hany =>
    cases hw
    have hWm : (n, lo, w) ∈ S.map Prod.fst := by
      simp only [List.any_eq_true, beq_iff_eq] at hany
      obtain ⟨e, he, hEq⟩ := hany
      exact List.mem_map.mpr ⟨e, he, hEq⟩
    refine ⟨hkeys, hwidth, by rw [map_fst_replace]; exact hR.disj, ?_, ?_⟩
    · intro V F hm v hv
      rcases mem_replace hm with ⟨rfl, rfl⟩ | ⟨hm, hne⟩
      · rw [hE v hv]
        exact ⟨_, hnew, LVec.extract_insertAt_self hp hin⟩
      · exact hkeep V F hm (disj_of_ne hR (List.mem_map_of_mem hm) hWm hne) v hv
    · intro m b hb
      rw [map_fst_replace] at hb
      exact hbit m b (hb _ hWm) (hR.frame m b hb)
  · split at hw
    · -- splice into the entry whose window contains the written one
      next W0 E0 hc =>
      cases hw
      obtain ⟨hm0, hcont⟩ := findCover_eq_some hc
      have hW0m : W0 ∈ S.map Prod.fst := List.mem_map_of_mem hm0
      obtain ⟨hn0, hlo0, hhi0⟩ := Win.contains_iff.mp hcont
      simp only at hn0 hlo0 hhi0
      refine ⟨hkeys, hwidth, by rw [map_fst_replace]; exact hR.disj, ?_, ?_⟩
      · intro V F hm v hv
        rcases mem_replace hm with ⟨rfl, rfl⟩ | ⟨hm, hne⟩
        · -- the spliced entry
          obtain ⟨v0, pE, h0, hb, rfl⟩ := evalPure2_splice hv
          have hbp := hE pE hb
          subst hbp
          obtain ⟨u, hu, hext⟩ := hR.entry _ _ hm0 v0 h0
          rw [hn0, hold, Option.some.injEq] at hu
          subst hu
          have hv0w : v0.width = V.2.2 := by rw [← hext]; simp
          refine ⟨_, by rw [hn0]; exact hnew, ?_⟩
          rw [LVec.extract_insertAt_inner hlo0 (by omega), hext,
            LVec.insertAt_eq_concat (by omega), hv0w, hp]
        · exact hkeep V F hm (overlaps_false_of_contains hcont
            (disj_of_ne hR (List.mem_map_of_mem hm) hW0m hne)) v hv
      · intro m b hb
        rw [map_fst_replace] at hb
        exact hbit m b (bit_not_overlaps_of_contains hcont (hb _ hW0m)) (hR.frame m b hb)
    · split at hw
      · cases hw
      · -- a fresh window: append it
        next hc hov =>
        cases hw
        have hdis := overlapsAny_eq_false (Bool.eq_false_iff.mpr hov)
        refine ⟨hkeys, hwidth, ?_, ?_, ?_⟩
        · rw [List.map_append, List.pairwise_append]
          refine ⟨hR.disj, by simp, ?_⟩
          intro V hV W hW
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hW
          subst hW
          exact hdis V hV
        · intro V F hm v hv
          rcases List.mem_append.mp hm with hm | hm
          · exact hkeep V F hm (hdis V (List.mem_map_of_mem hm)) v hv
          · simp only [List.mem_singleton, Prod.mk.injEq] at hm
            obtain ⟨rfl, rfl⟩ := hm
            rw [hE v hv]
            exact ⟨_, hnew, LVec.extract_insertAt_self hp hin⟩
        · intro m b hb
          have hb' : ∀ W ∈ S.map Prod.fst, (ReadWin.win m b 1).overlaps W = false :=
            fun W hW => hb W (by rw [List.map_append]; exact List.mem_append_left _ hW)
          exact hbit m b (hb _ (by simp)) (hR.frame m b hb')

/-- **A join is sound, first branch**: when the guard denotes `1` and the
first branch's symbolic state describes the state, the join describes it. -/
theorem join_sound_left {G : Expr2} {Sa Sb S' : SymState} (hj : join G Sa Sb = some S')
    {st₀ st : SvState} (hG : ∀ g, evalPure2 st₀ G = .ok g → g = LVec.ofLogic .l1)
    (hR : SymRel st₀ Sa st) : SymRel st₀ S' st := by
  have hws := join_wins hj
  unfold join at hj
  split at hj
  · next hd =>
    cases hj
    have hpw := (Win.allDisjoint_iff _).mp hd
    refine ⟨hR.keys, hR.width, by rw [hws]; exact hpw, ?_, ?_⟩
    · intro V F hm v hv
      obtain ⟨V', hV', hEq⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at hEq
      obtain ⟨rfl, rfl⟩ := hEq
      have ha : evalPure2 st₀ (Sa.lookupOr V') = .ok v := by
        unfold Expr2.joinIte at hv
        split at hv
        · exact hv
        · simp only [evalPure2, Pure2.res_bind_eq_ok, Pure2.res_pure_eq, Res.ok.injEq] at hv
          obtain ⟨g, hg, a, ha, b, -, rfl⟩ := hv
          rw [hG g hg, LVec.ternary_ofLogic_l1]
          exact ha
      clear hv
      simp only [lookupOr] at ha
      cases hf : Sa.findWin V' with
      | some E =>
          rw [hf, Option.getD_some] at ha
          exact hR.entry _ _ (findWin_eq_some hf) v ha
      | none =>
          rw [hf, Option.getD_none] at ha
          have hnot := findWin_eq_none hf
          have hdisj : ∀ U ∈ Sa.map Prod.fst, Win.overlaps V' U = false := by
            intro U hU
            refine List.pairwise_of_mem_ne (fun _ _ h => Win.overlaps_symm_false h) hpw hV'
              (mem_joinWins_left hU) ?_
            rintro rfl
            exact hnot hU
          have hag := hR.win_of_disjoint (n := V'.1) (lo := V'.2.1) (w := V'.2.2) hdisj
          obtain ⟨u₀, hu₀, rfl⟩ := evalPure2_held ha
          obtain ⟨u, hu, -, hext⟩ := ReadWin.agree_win_some hag hu₀
          exact ⟨u, hu, hext⟩
    · intro m b hb
      exact hR.frame m b fun U hU => hb U (by rw [hws]; exact mem_joinWins_left hU)
  · cases hj

/-- **A join is sound, second branch**: when the guard denotes `0` and the
second branch's symbolic state describes the state, the join describes it. -/
theorem join_sound_right {G : Expr2} {Sa Sb S' : SymState} (hj : join G Sa Sb = some S')
    {st₀ st : SvState} (hG : ∀ g, evalPure2 st₀ G = .ok g → g = LVec.ofLogic .l0)
    (hR : SymRel st₀ Sb st) : SymRel st₀ S' st := by
  have hws := join_wins hj
  unfold join at hj
  split at hj
  · next hd =>
    cases hj
    have hpw := (Win.allDisjoint_iff _).mp hd
    refine ⟨hR.keys, hR.width, by rw [hws]; exact hpw, ?_, ?_⟩
    · intro V F hm v hv
      obtain ⟨V', hV', hEq⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at hEq
      obtain ⟨rfl, rfl⟩ := hEq
      have hb : evalPure2 st₀ (Sb.lookupOr V') = .ok v := by
        unfold Expr2.joinIte at hv
        split at hv
        · next hsame => rw [← Expr2.eq_of_same _ _ hsame]; exact hv
        · simp only [evalPure2, Pure2.res_bind_eq_ok, Pure2.res_pure_eq, Res.ok.injEq] at hv
          obtain ⟨g, hg, a, -, b, hb, rfl⟩ := hv
          rw [hG g hg, LVec.ternary_ofLogic_l0]
          exact hb
      clear hv
      simp only [lookupOr] at hb
      cases hf : Sb.findWin V' with
      | some E =>
          rw [hf, Option.getD_some] at hb
          exact hR.entry _ _ (findWin_eq_some hf) v hb
      | none =>
          rw [hf, Option.getD_none] at hb
          have hnot := findWin_eq_none hf
          have hdisj : ∀ U ∈ Sb.map Prod.fst, Win.overlaps V' U = false := by
            intro U hU
            refine List.pairwise_of_mem_ne (fun _ _ h => Win.overlaps_symm_false h) hpw hV'
              (mem_joinWins_right hU) ?_
            rintro rfl
            exact hnot hU
          have hag := hR.win_of_disjoint (n := V'.1) (lo := V'.2.1) (w := V'.2.2) hdisj
          obtain ⟨u₀, hu₀, rfl⟩ := evalPure2_held hb
          obtain ⟨u, hu, -, hext⟩ := ReadWin.agree_win_some hag hu₀
          exact ⟨u, hu, hext⟩
    · intro m b hb
      exact hR.frame m b fun U hU => hb U (by rw [hws]; exact mem_joinWins_right hU)
  · cases hj

end SymState

/-! ## Symbolic execution is sound -/

/-- The static window of a blocking target, unpacked. -/
theorem Lhs2.symWin_spec {d : Design2} {t : Lhs2} {W : Win} (h : t.symWin d = some W) :
    (∀ ps, t ≠ .concat ps) ∧ t.window? d = some W ∧
      ∃ dw, d.declWidth W.1 = some dw ∧ W.2.1 + W.2.2 ≤ dw := by
  unfold Lhs2.symWin at h
  split at h
  · cases h
  · next hnc =>
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨W', hW', dw, hdw, h⟩ := h
    split at h
    · next hle =>
      cases h
      exact ⟨fun ps hps => hnc ps hps, hW', dw, hdw, hle⟩
    · cases h

theorem Expr2.wfB_spec {d : Design2} {e : Expr2} (h : e.wfB d = true) :
    e.unsupportedFree = true ∧ ∀ x ∈ e.idents, x ∈ d.symNames := by
  simpa [Expr2.wfB, List.all_eq_true] using h

theorem Expr2.listWfB_spec {d : Design2} {es : List Expr2} (h : Expr2.listWfB d es = true) :
    Expr2.listUnsupportedFree es = true ∧ ∀ x ∈ Expr2.listIdents es, x ∈ d.symNames := by
  simpa [Expr2.listWfB, List.all_eq_true] using h

/-- In a described state, a signal written by the symbolic state is bound at
its declared width. -/
theorem SymOk.lookup {d : Design2} {st₀ st : SvState} {S T : SymState} (hok : SymOk d st₀ S)
    (hR : SymRel st₀ T st) {n : String} (hn : n ∈ S.names) {dw : Nat}
    (hdw : d.declWidth n = some dw) : ∃ old, SvState.lookup st n = some old ∧ old.width = dw := by
  have h := (hR.width n).trans (hok n hn dw hdw)
  cases hl : SvState.lookup st n with
  | none => rw [hl] at h; cases h
  | some old => rw [hl] at h; exact ⟨old, rfl, by simpa using h⟩

/-- In a described state, every name bound in the pre-state is bound. -/
theorem SymRel.bound {st₀ st : SvState} {S : SymState} (hR : SymRel st₀ S st) {names : List String}
    (hb : ∀ x ∈ names, ∃ v, SvState.lookup st₀ x = some v) :
    ∀ x ∈ names, ∃ v, SvState.lookup st x = some v := by
  intro x hx
  obtain ⟨u₀, hu₀⟩ := hb x hx
  obtain ⟨u, hu, -⟩ := hR.lookup_some hu₀
  exact ⟨u, hu⟩

/-- **One blocking assignment, run**: a successful run is the symbolic
write. -/
theorem execStmt2_blocking_sound {d : Design2} {st₀ st : SvState} {S S' : SymState}
    {t : Lhs2} {e : Expr2} (hsym : (Stmt2.blockingAssign t e).symExec d S = some S')
    (hok : SymOk d st₀ S') (hR : SymRel st₀ S st) {f : Nat} {nba nba' : NbaQueue2}
    {st' : SvState} (hrun : execStmt2 (f + 1) st nba (.blockingAssign t e) = .ok (st', nba')) :
    nba' = nba ∧ SymRel st₀ S' st' := by
  simp only [Stmt2.symExec] at hsym
  split at hsym
  · simp only [Option.bind_eq_some_iff] at hsym
    obtain ⟨e', he', W, hW, hw⟩ := hsym
    obtain ⟨hnc, hwin, dw, hdw, hin⟩ := Lhs2.symWin_spec hW
    have hokS : SymOk d st₀ S := hok.mono (SymState.write_names hw).2
    obtain ⟨old, hold, hwold⟩ := hok.lookup hR (SymState.write_names hw).1 hdw
    obtain ⟨n, lo, w⟩ := W
    simp only at hold hin hdw hwold hwin
    have hres : resolveLhs2 (f + 1) st t = .ok (n, some (lo, w)) :=
      resolveLhs2_of_window? (by omega) hwin hold (by omega) (by rw [hdw, hwold])
    simp only [execStmt2, Res.bind_eq_ok] at hrun
    obtain ⟨v, hv, r, hr, hrun⟩ := hrun
    have hr' := resolveLhs2_mono hr (by simp) (f + 1) (by omega)
    rw [hres, Res.ok.injEq] at hr'
    subst hr'
    simp only [hold, Res.ok.injEq, Prod.mk.injEq, Pure2.res_pure_eq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    refine ⟨rfl, SymState.write_sound hw hR hold (by show lo + w ≤ old.width; omega)
      (LVec.width_resizeU _ _) ?_⟩
    intro x hx
    simp only [evalPure2, Pure2.res_bind_eq_ok, Pure2.res_pure_eq, Res.ok.injEq] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have := Expr2.symSubst_sound hR hokS he' ha
    rw [evalPure2_of_evalExpr2_ok hv, Res.ok.injEq] at this
    rw [this]
  · cases hsym

/-- **Symbolic execution is sound** (one fuel induction over the statement
interpreter's mutual block): a successful run of a statement (statement
list, `case` arm list) from a state the input symbolic state describes
leaves the NBA queue alone and ends in a state the output symbolic state
describes. -/
theorem symExec_sound {d : Design2} {st₀ : SvState} : ∀ fuel : Nat,
    (∀ (s : Stmt2) (S S' : SymState) (st : SvState) (nba : NbaQueue2) (st' : SvState)
        (nba' : NbaQueue2),
      s.symExec d S = some S' → SymOk d st₀ S' → SymRel st₀ S st →
      execStmt2 fuel st nba s = .ok (st', nba') → nba' = nba ∧ SymRel st₀ S' st') ∧
    (∀ (ss : List Stmt2) (S S' : SymState) (st : SvState) (nba : NbaQueue2) (st' : SvState)
        (nba' : NbaQueue2),
      Stmt2.symExecList d S ss = some S' → SymOk d st₀ S' → SymRel st₀ S st →
      execStmts2 fuel st nba ss = .ok (st', nba') → nba' = nba ∧ SymRel st₀ S' st') ∧
    (∀ (items : List CaseItem2) (S Sd S' : SymState) (subj : Expr2) (sv : LVec) (inside : Bool)
        (dflt : Option Stmt2) (st : SvState) (nba : NbaQueue2) (st' : SvState)
        (nba' : NbaQueue2),
      Stmt2.symExecOpt d S dflt = some Sd →
      CaseItem2.symExecList d S subj inside Sd items = some S' →
      (∀ v, evalPure2 st₀ subj = .ok v → v = sv) →
      SymOk d st₀ S' → SymRel st₀ S st →
      execCase2 fuel st nba sv items dflt inside = .ok (st', nba') →
        nba' = nba ∧ SymRel st₀ S' st')
  | 0 => by
      refine ⟨fun _ _ _ _ _ _ _ _ _ _ h => by simp [execStmt2] at h,
        fun _ _ _ _ _ _ _ _ _ _ h => by simp [execStmts2] at h, ?_⟩
      intro items _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
      cases items with
      | nil => simp [execCase2] at h
      | cons it rest => cases it; simp [execCase2] at h
  | f + 1 => by
      obtain ⟨ihS, ihL, ihC⟩ := symExec_sound (d := d) (st₀ := st₀) f
      refine ⟨?_, ?_, ?_⟩
      · intro s S S' st nba st' nba' hsym hok hR hrun
        cases s with
        | blockingAssign t e => exact execStmt2_blocking_sound hsym hok hR hrun
        | nbaAssign t e => simp [Stmt2.symExec] at hsym
        | unsupported k x => simp [Stmt2.symExec] at hsym
        | block body =>
            simp only [Stmt2.symExec] at hsym
            simp only [execStmt2] at hrun
            exact ihL _ S S' st nba st' nba' hsym hok hR hrun
        | ifStmt c t e =>
            simp only [Stmt2.symExec] at hsym
            split at hsym
            · simp only [Option.bind_eq_some_iff] at hsym
              obtain ⟨c', hc', St, ht, Sf, hf, hj⟩ := hsym
              have hokT : SymOk d st₀ St := hok.mono (SymState.join_names hj).1
              have hokF : SymOk d st₀ Sf := hok.mono (SymState.join_names hj).2
              have hokS : SymOk d st₀ S := hokT.mono (Stmt2.symExec_names t ht)
              simp only [execStmt2, Res.bind_eq_ok] at hrun
              obtain ⟨cv, hcv, hrun⟩ := hrun
              have hG : ∀ g, evalPure2 st₀ c'.ifGuard = .ok g →
                  g = LVec.ofLogic (Logic.ofB cv.condTrue) := by
                intro g hg
                obtain ⟨cv', hcv', rfl⟩ := evalPure2_ifGuard hg
                have := Expr2.symSubst_sound hR hokS hc' hcv'
                rw [evalPure2_of_evalExpr2_ok hcv, Res.ok.injEq] at this
                rw [this]
              by_cases hct : cv.condTrue = true
              · rw [if_pos hct] at hrun
                obtain ⟨hn, hRt⟩ := ihS t S St st nba st' nba' ht hokT hR hrun
                refine ⟨hn, SymState.join_sound_left hj (fun g hg => ?_) hRt⟩
                rw [hG g hg, hct, Logic.ofB_true]
              · rw [if_neg hct] at hrun
                have hG0 : ∀ g, evalPure2 st₀ c'.ifGuard = .ok g → g = LVec.ofLogic .l0 := by
                  intro g hg
                  rw [hG g hg, Bool.eq_false_iff.mpr hct, Logic.ofB_false]
                cases e with
                | none =>
                    simp only [Stmt2.symExecOpt, Option.some.injEq] at hf
                    subst hf
                    simp only [Res.ok.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨rfl, rfl⟩ := hrun
                    exact ⟨rfl, SymState.join_sound_right hj hG0 hR⟩
                | some s =>
                    simp only [Stmt2.symExecOpt] at hf
                    obtain ⟨hn, hRf⟩ := ihS s S Sf st nba st' nba' hf hokF hR hrun
                    exact ⟨hn, SymState.join_sound_right hj hG0 hRf⟩
            · cases hsym
        | caseStmt subj items dflt inside chk =>
            simp only [Stmt2.symExec] at hsym
            split at hsym
            · simp only [Option.bind_eq_some_iff] at hsym
              obtain ⟨subj', hs', Sd, hd, hl⟩ := hsym
              have hokS : SymOk d st₀ S :=
                (hok.mono (CaseItem2.symExecList_names _ hl)).mono (Stmt2.symExecOpt_names dflt hd)
              simp only [execStmt2, Res.bind_eq_ok] at hrun
              obtain ⟨sv, hsv, hrun⟩ := hrun
              refine ihC items.toList S Sd S' subj' sv inside dflt st nba st' nba' hd hl ?_ hok hR
                hrun
              intro v hv
              have := Expr2.symSubst_sound hR hokS hs' hv
              rw [evalPure2_of_evalExpr2_ok hsv, Res.ok.injEq] at this
              exact this.symm
            · cases hsym
      · intro ss S S' st nba st' nba' hsym hok hR hrun
        cases ss with
        | nil =>
            simp only [Stmt2.symExecList, Option.some.injEq] at hsym
            subst hsym
            simp only [execStmts2, Res.ok.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            exact ⟨rfl, hR⟩
        | cons s rest =>
            simp only [Stmt2.symExecList, Option.bind_eq_some_iff] at hsym
            obtain ⟨S1, h1, h2⟩ := hsym
            simp only [execStmts2, Res.bind_eq_ok] at hrun
            obtain ⟨⟨st1, nba1⟩, hr1, hr2⟩ := hrun
            obtain ⟨hn1, hR1⟩ := ihS s S S1 st nba st1 nba1 h1
              (hok.mono (Stmt2.symExecList_names rest h2)) hR hr1
            subst hn1
            exact ihL rest S1 S' st1 _ st' nba' h2 hok hR1 hr2
      · intro items S Sd S' subj sv inside dflt st nba st' nba' hd hl hsubj hok hR hrun
        cases items with
        | nil =>
            simp only [CaseItem2.symExecList, Option.some.injEq] at hl
            subst hl
            cases dflt with
            | none =>
                simp only [Stmt2.symExecOpt, Option.some.injEq] at hd
                subst hd
                simp only [execCase2, Res.ok.injEq, Prod.mk.injEq] at hrun
                obtain ⟨rfl, rfl⟩ := hrun
                exact ⟨rfl, hR⟩
            | some s =>
                simp only [Stmt2.symExecOpt] at hd
                simp only [execCase2] at hrun
                exact ihS s S Sd st nba st' nba' hd hok hR hrun
        | cons it rest =>
            obtain ⟨pats, body⟩ := it
            simp only [CaseItem2.symExecList, Option.bind_eq_some_iff] at hl
            obtain ⟨⟨pats', Sb⟩, harm, Sr, hr, hj⟩ := hl
            have hokB : SymOk d st₀ Sb := hok.mono (SymState.join_names hj).1
            have hokR : SymOk d st₀ Sr := hok.mono (SymState.join_names hj).2
            have hokS : SymOk d st₀ S := hokB.mono (CaseItem2.symArm_names _ harm)
            have harm' := harm
            simp only [CaseItem2.symArm] at harm'
            split at harm'
            · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at harm'
              obtain ⟨ps, hps, Sb', hb, rfl, rfl⟩ := harm'
              simp only [execCase2, Res.bind_eq_ok] at hrun
              obtain ⟨pvs, hpvs, hrun⟩ := hrun
              have hG : ∀ g, evalPure2 st₀ (Expr2.anyGuard inside subj ps) = .ok g →
                  g = LVec.ofLogic (Logic.ofB (pvs.any fun pv => caseHit inside sv pv)) := by
                intro g hg
                obtain ⟨pvs', hpvs', rfl⟩ := evalPure2_anyGuard hsubj hg
                have := Expr2.listSymSubst_sound hR hokS hps hpvs'
                rw [evalPures2_of_evalExprs2_ok hpvs, Res.ok.injEq] at this
                rw [this]
              by_cases hhit : (pvs.any fun pv => caseHit inside sv pv) = true
              · rw [if_pos hhit] at hrun
                obtain ⟨hn, hRb⟩ := ihS body S Sb' st nba st' nba' hb hokB hR hrun
                refine ⟨hn, SymState.join_sound_left hj (fun g hg => ?_) hRb⟩
                rw [hG g hg, hhit, Logic.ofB_true]
              · rw [if_neg hhit] at hrun
                obtain ⟨hn, hRr⟩ := ihC rest S Sd Sr subj sv inside dflt st nba st' nba' hd hr
                  hsubj hokR hR hrun
                refine ⟨hn, SymState.join_sound_right hj (fun g hg => ?_) hRr⟩
                rw [hG g hg, Bool.eq_false_iff.mpr hhit, Logic.ofB_false]
            · cases harm'

/-! ## Symbolic execution is total above the static fuel bound -/

/-- **Symbolic execution is total**: from a state the input symbolic state
describes (pre-state binding every declared name), at every fuel from the
static bound on, the statement (list, arm list) runs to completion. -/
theorem symExec_total {d : Design2} {st₀ : SvState}
    (hb : ∀ x ∈ d.symNames, ∃ v, SvState.lookup st₀ x = some v) : ∀ fuel : Nat,
    (∀ (s : Stmt2) (S S' : SymState) (st : SvState) (nba : NbaQueue2),
      s.symExec d S = some S' → SymOk d st₀ S' → SymRel st₀ S st → s.fuelB ≤ fuel →
      ∃ r, execStmt2 fuel st nba s = .ok r) ∧
    (∀ (ss : List Stmt2) (S S' : SymState) (st : SvState) (nba : NbaQueue2),
      Stmt2.symExecList d S ss = some S' → SymOk d st₀ S' → SymRel st₀ S st →
      Stmt2.listFuelB ss ≤ fuel → ∃ r, execStmts2 fuel st nba ss = .ok r) ∧
    (∀ (items : List CaseItem2) (S Sd S' : SymState) (subj : Expr2) (sv : LVec) (inside : Bool)
        (dflt : Option Stmt2) (st : SvState) (nba : NbaQueue2),
      Stmt2.symExecOpt d S dflt = some Sd →
      CaseItem2.symExecList d S subj inside Sd items = some S' →
      SymOk d st₀ S' → SymRel st₀ S st →
      CaseItem2.listFuelB (Stmt2.optFuelB dflt) items ≤ fuel →
      ∃ r, execCase2 fuel st nba sv items dflt inside = .ok r)
  | 0 => by
      refine ⟨fun s S S' _ _ hsym _ _ hf => ?_, fun ss _ _ _ _ _ _ _ hf => ?_,
        fun items _ _ _ _ _ _ _ _ _ _ _ _ _ hf => ?_⟩
      · cases s with
        | nbaAssign => simp [Stmt2.symExec] at hsym
        | unsupported => simp [Stmt2.symExec] at hsym
        | _ => simp [Stmt2.fuelB] at hf
      · cases ss <;> simp [Stmt2.listFuelB] at hf
      · cases items <;> simp [CaseItem2.listFuelB] at hf
  | f + 1 => by
      obtain ⟨ihS, ihL, ihC⟩ := symExec_total hb f
      refine ⟨?_, ?_, ?_⟩
      · intro s S S' st nba hsym hok hR hf
        have hbst := hR.bound hb
        cases s with
        | nbaAssign => simp [Stmt2.symExec] at hsym
        | unsupported => simp [Stmt2.symExec] at hsym
        | blockingAssign t e =>
            simp only [Stmt2.fuelB] at hf
            simp only [Stmt2.symExec] at hsym
            split at hsym
            · next hwf =>
              simp only [Option.bind_eq_some_iff] at hsym
              obtain ⟨e', -, W, hW, hw⟩ := hsym
              obtain ⟨hnc, hwin, dw, hdw, hin⟩ := Lhs2.symWin_spec hW
              obtain ⟨old, hold, hwold⟩ := hok.lookup hR (SymState.write_names hw).1 hdw
              obtain ⟨n, lo, w⟩ := W
              simp only at hold hin hdw hwold hwin
              obtain ⟨hu, hid⟩ := Expr2.wfB_spec hwf
              obtain ⟨v, hv⟩ := evalPure2_ok_of_wf hu fun x hx => hbst x (hid x hx)
              have hev : evalExpr2 f st e = .ok v := (evalExpr2_eq_evalPure2 (by omega)).trans hv
              have hres : resolveLhs2 f st t = .ok (n, some (lo, w)) :=
                resolveLhs2_of_window? (by omega) hwin hold (by omega) (by rw [hdw, hwold])
              simp only [execStmt2, hev, Res.ok_bind, hres, hold]
              exact ⟨_, rfl⟩
            · cases hsym
        | block body =>
            simp only [Stmt2.fuelB] at hf
            simp only [Stmt2.symExec] at hsym
            simp only [execStmt2]
            exact ihL _ S S' st nba hsym hok hR (by omega)
        | ifStmt c t e =>
            simp only [Stmt2.fuelB] at hf
            simp only [Stmt2.symExec] at hsym
            split at hsym
            · next hwf =>
              simp only [Option.bind_eq_some_iff] at hsym
              obtain ⟨c', -, St, ht, Sf, hfe, hj⟩ := hsym
              obtain ⟨hu, hid⟩ := Expr2.wfB_spec hwf
              obtain ⟨cv, hcv⟩ := evalPure2_ok_of_wf hu fun x hx => hbst x (hid x hx)
              have hev : evalExpr2 f st c = .ok cv := (evalExpr2_eq_evalPure2 (by omega)).trans hcv
              simp only [execStmt2, hev, Res.ok_bind]
              split
              · exact ihS t S St st nba ht (hok.mono (SymState.join_names hj).1) hR (by omega)
              · cases e with
                | none => exact ⟨_, rfl⟩
                | some s =>
                    simp only [Stmt2.symExecOpt] at hfe
                    simp only [Stmt2.optFuelB] at hf
                    exact ihS s S Sf st nba hfe (hok.mono (SymState.join_names hj).2) hR (by omega)
            · cases hsym
        | caseStmt subj items dflt inside chk =>
            simp only [Stmt2.fuelB] at hf
            simp only [Stmt2.symExec] at hsym
            split at hsym
            · next hwf =>
              simp only [Option.bind_eq_some_iff] at hsym
              obtain ⟨subj', -, Sd, hd, hl⟩ := hsym
              obtain ⟨hu, hid⟩ := Expr2.wfB_spec hwf
              obtain ⟨sv, hsv⟩ := evalPure2_ok_of_wf hu fun x hx => hbst x (hid x hx)
              have hev : evalExpr2 f st subj = .ok sv :=
                (evalExpr2_eq_evalPure2 (by omega)).trans hsv
              simp only [execStmt2, hev, Res.ok_bind]
              exact ihC items.toList S Sd S' subj' sv inside dflt st nba hd hl hok hR (by omega)
            · cases hsym
      · intro ss S S' st nba hsym hok hR hf
        cases ss with
        | nil => exact ⟨(st, nba), by simp [execStmts2]⟩
        | cons s rest =>
            simp only [Stmt2.listFuelB] at hf
            simp only [Stmt2.symExecList, Option.bind_eq_some_iff] at hsym
            obtain ⟨S1, h1, h2⟩ := hsym
            have hok1 : SymOk d st₀ S1 := hok.mono (Stmt2.symExecList_names rest h2)
            obtain ⟨⟨st1, nba1⟩, hr1⟩ := ihS s S S1 st nba h1 hok1 hR (by omega)
            obtain ⟨-, hR1⟩ := (symExec_sound f).1 s S S1 st nba st1 nba1 h1 hok1 hR hr1
            obtain ⟨r, hr2⟩ := ihL rest S1 S' st1 nba1 h2 hok hR1 (by omega)
            exact ⟨r, by simp only [execStmts2, hr1, Res.ok_bind]; exact hr2⟩
      · intro items S Sd S' subj sv inside dflt st nba hd hl hok hR hf
        have hbst := hR.bound hb
        cases items with
        | nil =>
            simp only [CaseItem2.listFuelB] at hf
            simp only [CaseItem2.symExecList, Option.some.injEq] at hl
            subst hl
            cases dflt with
            | none => exact ⟨(st, nba), by simp [execCase2]⟩
            | some s =>
                simp only [Stmt2.symExecOpt] at hd
                simp only [Stmt2.optFuelB] at hf
                simp only [execCase2]
                exact ihS s S Sd st nba hd hok hR (by omega)
        | cons it rest =>
            obtain ⟨pats, body⟩ := it
            simp only [CaseItem2.listFuelB, CaseItem2.fuelB] at hf
            simp only [CaseItem2.symExecList, Option.bind_eq_some_iff] at hl
            obtain ⟨⟨pats', Sb⟩, harm, Sr, hr, hj⟩ := hl
            simp only [CaseItem2.symArm] at harm
            split at harm
            · next hwf =>
              simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at harm
              obtain ⟨ps, -, Sb', hbd, rfl, rfl⟩ := harm
              obtain ⟨hu, hid⟩ := Expr2.listWfB_spec hwf
              obtain ⟨pvs, hpvs⟩ := evalPures2_ok_of_wf hu fun x hx => hbst x (hid x hx)
              have hev : evalExprs2 f st pats.toList = .ok pvs :=
                (evalExprs2_eq_evalPures2 (by omega)).trans hpvs
              simp only [execCase2, hev, Res.ok_bind]
              split
              · exact ihS body S Sb' st nba hbd (hok.mono (SymState.join_names hj).1) hR (by omega)
              · exact ihC rest S Sd Sr subj sv inside dflt st nba hd hr
                  (hok.mono (SymState.join_names hj).2) hR (by omega)
            · cases harm

/-! ## The lowered process is the body -/

namespace SymState

/-- The lowered target's leaves are constant slices, so its windows are the
entries' windows, in order, in every design. -/
theorem target_listWindows (d : Design2) : ∀ S : SymState,
    Lhs2.listWindows? d (S.map fun e => e.1.lhs) = some (S.map Prod.fst)
  | [] => by simp
  | e :: S => by
      rw [List.map_cons, Lhs2.listWindows?_cons, target_listWindows d S]
      simp [Win.lhs]

/-- The lowered target's window list. -/
theorem target_windows (d : Design2) (S : SymState) :
    S.target.windows? d = some (S.map Prod.fst) := by
  simp [target, target_listWindows]

/-- The lowered target's windows are the entries' windows. -/
theorem target_wins (d : Design2) (S : SymState) : S.target.wins d = S.map Prod.fst :=
  Lhs2.wins_of_windows? (target_windows d S)

/-- The lowered right-hand side reads what its entries read. -/
theorem rhs_reads (S : SymState) : S.rhs.reads = Expr2.listReads (S.map Prod.snd) := by
  simp [rhs, Expr2.reads]

/-- `selfReadFree` as a proposition: no read of the lowered right-hand side
overlaps a window of the lowered target. -/
theorem selfReadFree_iff {S : SymState} :
    S.selfReadFree = true ↔ ∀ r ∈ S.rhs.reads, ∀ W ∈ S.map Prod.fst, r.overlaps W = false := by
  rw [rhs_reads]
  unfold selfReadFree
  simp only [List.all_eq_true, Bool.not_eq_true']

/-- The concatenated right-hand side places each entry's value at its
window's offset (`Win.placed`), when every entry value has its window's
width. -/
theorem rhs_placed {st : SvState} : ∀ {S : SymState} {vs : List LVec},
    evalPures2 st (S.map Prod.snd) = .ok vs →
    (∀ W E, (W, E) ∈ S → ∀ v, evalPure2 st E = .ok v → v.width = W.2.2) →
    (LVec.concatMany vs.toArray).width = Win.sumWidth (S.map Prod.fst) ∧
    ∀ W E, (W, E) ∈ S → ∀ v, evalPure2 st E = .ok v →
      ∃ off, (W, off) ∈ Win.placed (S.map Prod.fst) ∧
        (LVec.concatMany vs.toArray).extract off W.2.2 = v
  | [], vs, h, _ => by
      simp only [List.map_nil, evalPures2, Res.ok.injEq] at h
      subst h
      exact ⟨rfl, fun _ _ hm => absurd hm List.not_mem_nil⟩
  | (W, E) :: S, vs, h, hw => by
      simp only [List.map_cons, evalPures2, Pure2.res_bind_eq_ok, Pure2.res_pure_eq,
        Res.ok.injEq] at h
      obtain ⟨v, hv, vs', hvs', rfl⟩ := h
      obtain ⟨ihw, ihp⟩ := rhs_placed hvs' fun W' E' hm => hw W' E' (List.mem_cons_of_mem _ hm)
      have hvw := hw W E (List.mem_cons_self ..) v hv
      rw [LVec.concatMany_cons]
      refine ⟨by simp only [LVec.width_concat, ihw, hvw, List.map_cons, Win.sumWidth_cons], ?_⟩
      intro W' E' hm v' hv'
      rcases List.mem_cons.mp hm with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [hv, Res.ok.injEq] at hv'
        subst hv'
        refine ⟨Win.sumWidth (S.map Prod.fst), by simp, ?_⟩
        rw [← ihw, ← hvw, LVec.extract_concat_hi]
      · obtain ⟨off, hoff, hext⟩ := ihp W' E' h v' hv'
        refine ⟨off, by simp [hoff], ?_⟩
        rw [LVec.extract_concat_lo _ _ (by rw [ihw]; exact Win.le_sumWidth_of_mem_placed hoff),
          hext]

end SymState

/-- A multi-window write keeps every width. -/
theorem SvState.writeWins_width {val : LVec} : ∀ {st : SvState} {pl : List (Win × Nat)}
    (m : String), (SvState.lookup (SvState.writeWins st val pl) m).map LVec.width =
      (SvState.lookup st m).map LVec.width
  | _, [], _ => rfl
  | st, ((n, lo, w), off) :: rest, m => by
      cases hl : SvState.lookup st n with
      | none => rw [SvState.writeWins_cons_none hl]; exact SvState.writeWins_width m
      | some old =>
          rw [SvState.writeWins_cons_some hl, SvState.writeWins_width m, SvState.lookup_set]
          by_cases h : n = m
          · subst h; simp [hl]
          · simp [h]

/-- **Two states one symbolic state describes are equal** (the entries
evaluating in the pre-state, its keys duplicate-free): every bit is either
in an entry window, holding the entry's value, or the pre-state's. -/
theorem SymRel.unique {st₀ s₁ s₂ : SvState} {S : SymState} (h₁ : SymRel st₀ S s₁)
    (h₂ : SymRel st₀ S s₂) (hev : ∀ W E, (W, E) ∈ S → ∃ v, evalPure2 st₀ E = .ok v)
    (hnd : (st₀.map Prod.fst).Nodup) : s₁ = s₂ := by
  refine SvState.ext (h₁.keys.trans h₂.keys.symm) (by rw [h₁.keys]; exact hnd) fun n =>
    ReadWin.lookup_eq_of_agree_bits fun b => ?_
  by_cases hc : ∃ W ∈ S.map Prod.fst, (ReadWin.win n b 1).overlaps W = true
  · obtain ⟨W, hW, hov⟩ := hc
    obtain ⟨⟨W', E⟩, hm, rfl⟩ := List.mem_map.mp hW
    obtain ⟨v, hv⟩ := hev _ _ hm
    obtain ⟨u₁, hu₁, he₁⟩ := h₁.entry _ _ hm v hv
    obtain ⟨u₂, hu₂, he₂⟩ := h₂.entry _ _ hm v hv
    have hw : u₁.width = u₂.width := by
      have := (h₁.width W'.1).trans (h₂.width W'.1).symm
      rw [hu₁, hu₂] at this
      simpa using this
    obtain ⟨m, lo, w⟩ := W'
    simp only at hu₁ hu₂ he₁ he₂
    rw [ReadWin.overlaps_win_one] at hov
    obtain ⟨rfl, hb₁, hb₂⟩ := hov
    exact Comb2Term.agree_bit_of_extract hu₁ hu₂ hw (he₁.trans he₂.symm) hb₁ hb₂
  · have hc' : ∀ W ∈ S.map Prod.fst, (ReadWin.win n b 1).overlaps W = false :=
      fun W hW => Bool.eq_false_iff.mpr fun h => hc ⟨W, hW, h⟩
    exact ReadWin.agree_trans (h₁.frame n b hc') (ReadWin.agree_symm (h₂.frame n b hc'))

/-- An evaluated list evaluates elementwise. -/
theorem evalPures2_ok_mem {st : SvState} : ∀ {es : List Expr2} {vs : List LVec},
    evalPures2 st es = .ok vs → ∀ e ∈ es, ∃ v, evalPure2 st e = .ok v
  | [], _, _, e, he => absurd he List.not_mem_nil
  | e :: es, vs, h, e', he' => by
      simp only [evalPures2, Pure2.res_bind_eq_ok, Pure2.res_pure_eq] at h
      obtain ⟨v, hv, vs', hvs', -⟩ := h
      rcases List.mem_cons.mp he' with rfl | he'
      · exact ⟨v, hv⟩
      · exact evalPures2_ok_mem hvs' e' he'

/-- `declWidth` reads only the declarations. -/
theorem Design2.declWidth_congr {d d' : Design2} (h : d'.decls = d.decls) :
    d'.declWidth = d.declWidth := by
  funext n; simp [Design2.declWidth, h]

/-- `symNames` reads only the declarations. -/
theorem Design2.symNames_congr {d d' : Design2} (h : d'.decls = d.decls) :
    d'.symNames = d.symNames := by
  simp [Design2.symNames, h]

/-- The right-hand side of the lowered assign, evaluated. -/
theorem SymState.evalPure2_rhs {st : SvState} {S : SymState} {v : LVec}
    (h : evalPure2 st S.rhs = .ok v) :
    ∃ vs, evalPures2 st (S.map Prod.snd) = .ok vs ∧ v = LVec.concatMany vs.toArray := by
  simp only [SymState.rhs, evalPure2, Pure2.res_bind_eq_ok,
    Pure2.res_pure_eq, Res.ok.injEq] at h
  obtain ⟨vs, hvs, rfl⟩ := h
  exact ⟨vs, hvs, rfl⟩

/-- **The lowered assign's write is described by the symbolic state**
(given a run that the symbolic state describes, which supplies the entries'
widths). -/
theorem SymRel.of_combWrite {d' : Design2} (hd' : CombDesign d') {st₀ : SvState}
    (hs : StateShape d' st₀) {i : Nat} {S : SymState}
    (hp : d'.processes[i]? = some S.toAssign) {st : SvState} (hR : SymRel st₀ S st) {v : LVec}
    (hv : evalPure2 st₀ S.rhs = .ok v) : SymRel st₀ S (combWrite d' st₀ S.target v) := by
  obtain ⟨vs, hvs, rfl⟩ := SymState.evalPure2_rhs hv
  have hwidth : ∀ W E, (W, E) ∈ S → ∀ x, evalPure2 st₀ E = .ok x → x.width = W.2.2 := by
    intro W E hm x hx
    obtain ⟨u, -, hext⟩ := hR.entry W E hm x hx
    rw [← hext, LVec.width_extract]
  obtain ⟨hvw, hplace⟩ := SymState.rhs_placed hvs hwidth
  have hres : (LVec.concatMany vs.toArray).resizeU (Win.sumWidth (S.target.wins d')) =
      LVec.concatMany vs.toArray := by
    rw [SymState.target_wins]; exact LVec.resizeU_of_width hvw
  have hsC := StateShape.combWrite hs S.target (LVec.concatMany vs.toArray)
  refine ⟨hsC.keys.trans hs.keys.symm, fun m => SvState.writeWins_width m, hR.disj, ?_, ?_⟩
  · intro W E hm x hx
    obtain ⟨off, hoff, hext⟩ := hplace W E hm x hx
    obtain ⟨n, lo, w⟩ := W
    obtain ⟨u, hu, hue⟩ := hd'.combWrite_readBack hs hp (LVec.concatMany vs.toArray)
      (n := n) (lo := lo) (w := w) (off := off) (by rw [SymState.target_wins]; exact hoff)
    rw [hres] at hue
    exact ⟨u, hu, hue.trans hext⟩
  · intro n b hb
    exact ReadWin.agree_symm (ReadWin.agree_combWrite fun wn hwn => by
      rw [SymState.target_wins] at hwn
      exact hb wn hwn)

/-- The pre-state width facts of an `always_comb` body whose lowered assign
is process `i` of a comb design, on a shaped state: every signal the body
writes is driven there, hence bound at its declared width. -/
theorem SymOk.of_shape {d d' : Design2} (hdecls : d'.decls = d.decls) {i : Nat} {S : SymState}
    (hp : d'.processes[i]? = some S.toAssign) {st : SvState} (hs : StateShape d' st) :
    SymOk d st S := by
  intro n hn dw hdw
  obtain ⟨⟨⟨m, lo, w⟩, E⟩, he, rfl⟩ := SymState.mem_names.mp hn
  have hW : d'.Writes i (m, lo, w) :=
    ⟨S.target, S.rhs, hp, by rw [SymState.target_wins]; exact List.mem_map_of_mem he⟩
  obtain ⟨v, hv, hvw⟩ := hs.driven m ⟨i, lo, w, hW⟩
  rw [Design2.declWidth_congr hdecls, hdw, Option.some.injEq] at hvw
  simp [hv, hvw]

/-- **An `always_comb` run is its lowered assign's write** (inversion, any
fuel): on a state with the comb shape of a design containing the lowered
assign, a successful run of the body is `combWrite` of the lowered
right-hand side's value. -/
theorem runCombProcess2_alwaysComb_ok {d d' : Design2} (hd' : CombDesign d')
    (hdecls : d'.decls = d.decls) {i : Nat} {body : Stmt2} {S : SymState}
    (hsym : body.symExec d [] = some S) (hp : d'.processes[i]? = some S.toAssign) {st : SvState}
    (hs : StateShape d' st) {f : Nat} {r : SvState}
    (h : runCombProcess2 f st (.alwaysComb body) = .ok r) :
    ∃ v, evalPure2 st S.rhs = .ok v ∧ r = combWrite d' st S.target v := by
  simp only [runCombProcess2, Res.bind_eq_ok] at h
  obtain ⟨⟨st', nba⟩, hrun, hr⟩ := h
  obtain ⟨rfl, hR⟩ := (symExec_sound f).1 body [] S st [] st' nba hsym
    (SymOk.of_shape hdecls hp hs) (SymRel.init st) hrun
  simp only [Res.ok.injEq] at hr
  subst hr
  obtain ⟨v, hv⟩ := hd'.evalPure2_ok hs hp
  refine ⟨v, hv, SymRel.unique hR (SymRel.of_combWrite hd' hs hp hR hv) ?_ ?_⟩
  · intro W E hm
    obtain ⟨vs, hvs, -⟩ := SymState.evalPure2_rhs hv
    exact evalPures2_ok_mem hvs E (List.mem_map_of_mem (f := Prod.snd) hm)
  · rw [hs.keys]; exact hd'.nodup

/-- **An `always_comb` run completes and is its lowered assign's write**
(forward): at every fuel from the body's static bound `Stmt2.fuelB` on. -/
theorem runCombProcess2_alwaysComb_fwd {d d' : Design2} (hd' : CombDesign d')
    (hdecls : d'.decls = d.decls) {i : Nat} {body : Stmt2} {S : SymState}
    (hsym : body.symExec d [] = some S) (hp : d'.processes[i]? = some S.toAssign) {st : SvState}
    (hs : StateShape d' st) {f : Nat} (hf : body.fuelB ≤ f) :
    ∃ v, evalPure2 st S.rhs = .ok v ∧
      runCombProcess2 f st (.alwaysComb body) = .ok (combWrite d' st S.target v) := by
  have hb : ∀ x ∈ d.symNames, ∃ v, SvState.lookup st x = some v := by
    intro x hx
    rw [← Design2.symNames_congr hdecls] at hx
    exact hs.lookup_of_mem hx
  have hok := SymOk.of_shape hdecls hp hs
  obtain ⟨⟨st', nba⟩, hrun⟩ := (symExec_total hb f).1 body [] S st [] hsym hok (SymRel.init st) hf
  obtain ⟨rfl, -⟩ := (symExec_sound f).1 body [] S st [] st' nba hsym hok (SymRel.init st) hrun
  have h : runCombProcess2 f st (.alwaysComb body) = .ok st' := by
    simp [runCombProcess2, hrun]
  obtain ⟨v, hv, rfl⟩ := runCombProcess2_alwaysComb_ok hd' hdecls hsym hp hs h
  exact ⟨v, hv, h⟩

/-! ## The lowering, structurally -/

theorem Design2.lowerProcs_spec {d : Design2} : ∀ {ps qs : List Process2},
    d.lowerProcs ps = some qs → qs.length = ps.length ∧
      ∀ i : Nat, qs[i]? = ps[i]?.bind (Process2.lowerComb d)
  | [], qs, h => by
      simp only [Design2.lowerProcs, Option.some.injEq] at h
      subst h
      exact ⟨rfl, fun _ => rfl⟩
  | p :: ps, qs, h => by
      simp only [Design2.lowerProcs, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, qs', hqs', rfl⟩ := h
      obtain ⟨hlen, hget⟩ := Design2.lowerProcs_spec hqs'
      refine ⟨by simp [hlen], fun i => ?_⟩
      cases i with
      | zero => simp [hq]
      | succ i => simp [hget i]

/-- **What the lowering does**: same name and declarations, same number of
processes, and process `i` of the lowered design is process `i` of `d`
lowered. -/
theorem Design2.lowerComb_spec {d d' : Design2} (h : d.lowerComb = some d') :
    d'.name = d.name ∧ d'.decls = d.decls ∧ d'.processes.size = d.processes.size ∧
      ∀ i : Nat, d'.processes[i]? = d.processes[i]?.bind (Process2.lowerComb d) := by
  simp only [Design2.lowerComb, Option.map_eq_some_iff] at h
  obtain ⟨qs, hqs, rfl⟩ := h
  obtain ⟨hlen, hget⟩ := Design2.lowerProcs_spec hqs
  refine ⟨rfl, rfl, by simp [hlen], fun i => ?_⟩
  simp only [List.getElem?_toArray, hget, Array.getElem?_toList]

/-- Every process of `d` has its lowered counterpart at the same index. -/
theorem Design2.lowerComb_proc {d d' : Design2} (h : d.lowerComb = some d') {i : Nat}
    {p : Process2} (hp : d.processes[i]? = some p) :
    ∃ q, p.lowerComb d = some q ∧ d'.processes[i]? = some q := by
  obtain ⟨-, -, hsize, hget⟩ := Design2.lowerComb_spec h
  have hi : i < d'.processes.size := by
    rw [hsize]; exact (Array.getElem?_eq_some_iff.mp hp).1
  obtain ⟨q, hq⟩ : ∃ q, d'.processes[i]? = some q := ⟨_, Array.getElem?_eq_getElem hi⟩
  rw [hget i, hp, Option.bind_some] at hq
  exact ⟨q, hq, by rw [hget i, hp, Option.bind_some, hq]⟩

/-- Every process of the lowered design comes from a process of `d`. -/
theorem Design2.lowerComb_proc' {d d' : Design2} (h : d.lowerComb = some d') {i : Nat}
    {q : Process2} (hq : d'.processes[i]? = some q) :
    ∃ p, d.processes[i]? = some p ∧ p.lowerComb d = some q := by
  obtain ⟨-, -, -, hget⟩ := Design2.lowerComb_spec h
  rw [hget i] at hq
  cases hp : d.processes[i]? with
  | none => rw [hp] at hq; cases hq
  | some p => rw [hp, Option.bind_some] at hq; exact ⟨p, rfl, hq⟩

/-- An `always_comb` the lowering accepts: its body executes symbolically to
a self-read-free state, whose assign is the lowered process. -/
theorem Process2.lowerComb_alwaysComb {d : Design2} {body : Stmt2} {q : Process2}
    (h : (Process2.alwaysComb body).lowerComb d = some q) :
    ∃ S, body.symExec d [] = some S ∧ S.selfReadFree = true ∧ q = S.toAssign := by
  simp only [Process2.lowerComb, Option.bind_eq_some_iff] at h
  obtain ⟨S, hS, h⟩ := h
  split at h
  · exact ⟨S, hS, by assumption, (Option.some.inj h).symm⟩
  · cases h

/-- The two process shapes the lowering accepts. -/
theorem Process2.lowerComb_eq_some {d : Design2} {p q : Process2} (h : p.lowerComb d = some q) :
    (∃ t e, p = .assign t e ∧ q = .assign t e) ∨
      (∃ body S, p = .alwaysComb body ∧ body.symExec d [] = some S ∧ q = S.toAssign) := by
  cases p with
  | assign t e =>
      simp only [Process2.lowerComb, Option.some.injEq] at h
      exact Or.inl ⟨t, e, rfl, h.symm⟩
  | alwaysComb body =>
      obtain ⟨S, hS, -, rfl⟩ := Process2.lowerComb_alwaysComb h
      exact Or.inr ⟨body, S, rfl, hS, rfl⟩
  | _ => simp [Process2.lowerComb] at h

/-- A design whose lowering succeeds has only comb-phase processes, none of
them an edge or reset process. -/
theorem Design2.lowerComb_phases {d d' : Design2} (h : d.lowerComb = some d') :
    d.edgeIndices = [] ∧ (∀ a b, d.resetIndices a b = []) ∧
      d.combIndices = List.range d.processes.size := by
  have hk : ∀ i, i < d.processes.size → ∃ p, d.processes[i]? = some p ∧
      ((∃ t e, p = .assign t e) ∨ ∃ body, p = .alwaysComb body) := by
    intro i hi
    obtain ⟨q, hq, -⟩ := Design2.lowerComb_proc h (Array.getElem?_eq_getElem hi)
    rcases Process2.lowerComb_eq_some hq with ⟨t, e, hpe, -⟩ | ⟨body, S, hpe, -, -⟩
    · exact ⟨_, Array.getElem?_eq_getElem hi, Or.inl ⟨t, e, hpe⟩⟩
    · exact ⟨_, Array.getElem?_eq_getElem hi, Or.inr ⟨body, hpe⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold Design2.edgeIndices
    rw [List.filter_eq_nil_iff]
    intro i hi
    obtain ⟨p, hp, hk⟩ := hk i (List.mem_range.mp hi)
    rcases hk with ⟨t, e, rfl⟩ | ⟨body, rfl⟩ <;> simp [hp, Process2.isEdgePhase]
  · intro a b
    unfold Design2.resetIndices
    rw [List.filter_eq_nil_iff]
    intro i hi
    obtain ⟨p, hp, hk⟩ := hk i (List.mem_range.mp hi)
    rcases hk with ⟨t, e, rfl⟩ | ⟨body, rfl⟩ <;> simp [hp]
  · unfold Design2.combIndices
    rw [List.filter_eq_self]
    intro i hi
    obtain ⟨p, hp, hk⟩ := hk i (List.mem_range.mp hi)
    rcases hk with ⟨t, e, rfl⟩ | ⟨body, rfl⟩ <;> simp [hp, Process2.isCombPhase]

/-! ## Run-level simulation -/

/-- A cycle of a design with no edge and no reset process is the input
settle followed by the post-edge settle (`cycleStep2_of_comb` without the
comb profile). -/
theorem cycleStep2_of_noEdge {d : Design2} (he : d.edgeIndices = [])
    (hr : ∀ a b, d.resetIndices a b = []) (σ : ScheduleOracle) (fuel : Nat)
    (inputs st : SvState) (k : Nat) :
    cycleStep2 d σ fuel inputs st k =
      (combSettle2 d σ fuel (applyInputs2 d inputs st) k >>=
        fun p => combSettle2 d σ fuel p.1 (p.2 + 1)) := by
  unfold cycleStep2
  simp only [hr, he, ScheduleOracle.choose_nil]
  cases combSettle2 d σ fuel (applyInputs2 d inputs st) k with
  | ok p => obtain ⟨st1, k1⟩ := p; rfl
  | timeout => rfl
  | unsupported msg => rfl

/-- `applyInputs2` reads only the declarations. -/
theorem applyInputs2_congr {d d' : Design2} (h : d'.decls = d.decls) (inputs st : SvState) :
    applyInputs2 d' inputs st = applyInputs2 d inputs st := by
  simp [applyInputs2, Design2.inputNames, h]

/-- `initState2` reads only the declarations. -/
theorem initState2_congr {d d' : Design2} (h : d'.decls = d.decls) :
    initState2 d' = initState2 d := by
  simp [initState2, h]

/-- **`d₂` simulates the comb runs of `d₁` on the states `I`**: same
declarations and comb ready list, no edge or reset process in either, and
every process of `d₁` is matched (same index) by a process of `d₂` that, on
every `I`-state, reaches the same result at some fuel whenever it succeeds;
`I` holds initially, survives `applyInputs2`, and every successful process
run. -/
structure CombSim (d₁ d₂ : Design2) (I : SvState → Prop) : Prop where
  decls : d₂.decls = d₁.decls
  comb : d₂.combIndices = d₁.combIndices
  edge₁ : d₁.edgeIndices = []
  edge₂ : d₂.edgeIndices = []
  reset₁ : ∀ a b, d₁.resetIndices a b = []
  reset₂ : ∀ a b, d₂.resetIndices a b = []
  none : ∀ i : Nat, d₁.processes[i]? = none → d₂.processes[i]? = none
  proc : ∀ (i : Nat) (p₁ : Process2), d₁.processes[i]? = some p₁ →
    ∃ p₂, d₂.processes[i]? = some p₂ ∧ ∀ st, I st → ∀ f r, runCombProcess2 f st p₁ = .ok r →
      I r ∧ ∃ f', runCombProcess2 f' st p₂ = .ok r
  init : I (initState2 d₁)
  inputs : ∀ inputs st, I st → I (applyInputs2 d₁ inputs st)

namespace CombSim

variable {d₁ d₂ : Design2} {I : SvState → Prop}

/-- A pass simulates. -/
theorem combPass2 (h : CombSim d₁ d₂ I) : ∀ (is : List Nat) (st : SvState) (f : Nat)
    (r : SvState), I st → LeanModels.Sv.combPass2 d₁ f st is = .ok r →
      I r ∧ ∃ f', LeanModels.Sv.combPass2 d₂ f' st is = .ok r
  | [], st, f, r, hI, hp => by
      simp only [LeanModels.Sv.combPass2, Res.ok.injEq] at hp
      subst hp
      exact ⟨hI, 0, rfl⟩
  | i :: is, st, f, r, hI, hp => by
      cases h1 : d₁.processes[i]? with
      | none =>
          rw [combPass2_cons_none h1] at hp
          obtain ⟨hIr, f', hf'⟩ := h.combPass2 is st f r hI hp
          exact ⟨hIr, f', by rw [combPass2_cons_none (h.none i h1)]; exact hf'⟩
      | some p₁ =>
          obtain ⟨p₂, h2, hsim⟩ := h.proc i p₁ h1
          rw [combPass2_cons_some h1, Res.bind_eq_ok] at hp
          obtain ⟨m, hm, hrest⟩ := hp
          obtain ⟨hIm, f1, hf1⟩ := hsim st hI f m hm
          obtain ⟨hIr, f2, hf2⟩ := h.combPass2 is m f r hIm hrest
          refine ⟨hIr, max f1 f2, ?_⟩
          rw [combPass2_cons_some h2, runCombProcess2_mono hf1 (by simp) _ (Nat.le_max_left _ _),
            Res.ok_bind]
          exact combPass2_mono hf2 (by simp) _ (Nat.le_max_right _ _)

/-- A settle simulates. -/
theorem combSettle2 (h : CombSim d₁ d₂ I) (σ : ScheduleOracle) : ∀ (f : Nat) (st : SvState)
    (k : Nat) (S : SvState) (k' : Nat), I st →
      LeanModels.Sv.combSettle2 d₁ σ f st k = .ok (S, k') →
        I S ∧ ∃ f', LeanModels.Sv.combSettle2 d₂ σ f' st k = .ok (S, k')
  | 0, _, _, _, _, _, hs => by simp [LeanModels.Sv.combSettle2] at hs
  | f + 1, st, k, S, k', hI, hs => by
      simp only [LeanModels.Sv.combSettle2, Res.bind_eq_ok] at hs
      obtain ⟨st', hpass, hrest⟩ := hs
      rw [← h.comb] at hpass
      obtain ⟨hI', fp, hfp⟩ := h.combPass2 _ st f st' hI hpass
      by_cases heq : (st' == st) = true
      · rw [if_pos heq] at hrest
        simp only [Res.ok.injEq, Prod.mk.injEq] at hrest
        obtain ⟨rfl, rfl⟩ := hrest
        refine ⟨hI', fp + 1, ?_⟩
        simp only [LeanModels.Sv.combSettle2, hfp, Res.ok_bind, if_pos heq]
      · rw [if_neg heq] at hrest
        obtain ⟨hIS, fr, hfr⟩ := h.combSettle2 σ f st' (k + 1) S k' hI' hrest
        refine ⟨hIS, max fp fr + 1, ?_⟩
        simp only [LeanModels.Sv.combSettle2]
        rw [combPass2_mono hfp (by simp) _ (Nat.le_max_left _ _), Res.ok_bind, if_neg heq]
        exact combSettle2_mono hfr (by simp) _ (Nat.le_max_right _ _)

/-- A cycle simulates. -/
theorem cycleStep2 (h : CombSim d₁ d₂ I) (σ : ScheduleOracle) {f : Nat} {inputs st : SvState}
    {k : Nat} {S : SvState} {k' : Nat} (hI : I st)
    (hc : LeanModels.Sv.cycleStep2 d₁ σ f inputs st k = .ok (S, k')) :
    I S ∧ ∃ f', LeanModels.Sv.cycleStep2 d₂ σ f' inputs st k = .ok (S, k') := by
  rw [cycleStep2_of_noEdge h.edge₁ h.reset₁, Res.bind_eq_ok] at hc
  obtain ⟨⟨st1, k1⟩, h1, h2⟩ := hc
  obtain ⟨hI1, f1, hf1⟩ := h.combSettle2 σ f _ k st1 k1 (h.inputs inputs st hI) h1
  obtain ⟨hIS, f2, hf2⟩ := h.combSettle2 σ f st1 (k1 + 1) S k' hI1 h2
  refine ⟨hIS, max f1 f2, ?_⟩
  rw [cycleStep2_of_noEdge h.edge₂ h.reset₂, applyInputs2_congr h.decls,
    combSettle2_mono hf1 (by simp) _ (Nat.le_max_left _ _), Res.ok_bind]
  exact combSettle2_mono hf2 (by simp) _ (Nat.le_max_right _ _)

/-- A run from an `I`-state simulates. -/
theorem runFrom2 (h : CombSim d₁ d₂ I) (σ : ScheduleOracle) : ∀ (stim : List SvState) (f : Nat)
    (st : SvState) (k : Nat) (tr : List SvState), I st →
      LeanModels.Sv.runFrom2 d₁ σ f st k stim = .ok tr →
        ∃ f', LeanModels.Sv.runFrom2 d₂ σ f' st k stim = .ok tr
  | [], f, st, k, tr, _, hr => ⟨0, by simpa [LeanModels.Sv.runFrom2] using hr⟩
  | inputs :: rest, f, st, k, tr, hI, hr => by
      simp only [LeanModels.Sv.runFrom2, Res.bind_eq_ok] at hr
      obtain ⟨⟨st', k'⟩, hc, tr', hrest, htr⟩ := hr
      obtain ⟨hI', f1, hf1⟩ := h.cycleStep2 σ hI hc
      obtain ⟨f2, hf2⟩ := h.runFrom2 σ rest f st' k' tr' hI' hrest
      refine ⟨max f1 f2, ?_⟩
      simp only [LeanModels.Sv.runFrom2]
      rw [cycleStep2_mono hf1 (by simp) _ (Nat.le_max_left _ _), Res.ok_bind,
        runFrom2_mono hf2 (by simp) _ (Nat.le_max_right _ _), Res.ok_bind]
      exact htr

/-- **A completed run simulates.** -/
theorem runs2 (h : CombSim d₁ d₂ I) {σ : ScheduleOracle} {stim tr : List SvState}
    (hr : Runs2 d₁ σ stim tr) : Runs2 d₂ σ stim tr := by
  obtain ⟨f, hf⟩ := hr
  obtain ⟨f', hf'⟩ := h.runFrom2 σ stim f _ 0 tr h.init hf
  exact ⟨f', by unfold run2; rw [initState2_congr h.decls]; exact hf'⟩

end CombSim

/-! ## The lowered design simulates the design, and back -/

section Lowered

variable {d d' : Design2}

/-- The design and its lowering have the same comb ready list. -/
theorem Design2.lowerComb_combIndices (hl : d.lowerComb = some d') (hd' : CombDesign d') :
    d'.combIndices = d.combIndices := by
  rw [hd'.combIndices_eq, (Design2.lowerComb_phases hl).2.2, (Design2.lowerComb_spec hl).2.2.1]

/-- **The lowered design simulates the design** (on shaped states). -/
theorem CombSim.of_lowerComb (hl : d.lowerComb = some d') (hd' : CombDesign d') :
    CombSim d d' (StateShape d') where
  decls := (Design2.lowerComb_spec hl).2.1
  comb := Design2.lowerComb_combIndices hl hd'
  edge₁ := (Design2.lowerComb_phases hl).1
  edge₂ := hd'.edgeIndices_eq
  reset₁ := (Design2.lowerComb_phases hl).2.1
  reset₂ := hd'.resetIndices_eq
  none := fun i h => by rw [(Design2.lowerComb_spec hl).2.2.2 i, h]; rfl
  proc := by
    intro i p hp
    obtain ⟨q, hq, hq'⟩ := Design2.lowerComb_proc hl hp
    refine ⟨q, hq', fun st hs f r hr => ?_⟩
    rcases Process2.lowerComb_eq_some hq with ⟨t, e, rfl, rfl⟩ | ⟨body, S, rfl, hsym, rfl⟩
    · obtain ⟨v, -, rfl⟩ := runCombProcess2_assign_write_ok hd' hs hq' hr
      exact ⟨hs.combWrite t v, f, by rw [hr]⟩
    · obtain ⟨v, hv, rfl⟩ := runCombProcess2_alwaysComb_ok hd' (Design2.lowerComb_spec hl).2.1
        hsym hq' hs hr
      exact ⟨hs.combWrite _ v, S.rhs.size + 1,
        runCombProcess2_assign_write hd' hs hq' (Nat.lt_succ_self _) hv⟩
  init := by rw [← initState2_congr (Design2.lowerComb_spec hl).2.1]; exact StateShape.of_initState2 hd'
  inputs := fun inputs st hs => by
    rw [← applyInputs2_congr (Design2.lowerComb_spec hl).2.1]
    exact StateShape.of_applyInputs2 hd' hs inputs

/-- **The design simulates its lowering** (on shaped states). -/
theorem CombSim.of_lowerComb' (hl : d.lowerComb = some d') (hd' : CombDesign d') :
    CombSim d' d (StateShape d') where
  decls := (Design2.lowerComb_spec hl).2.1.symm
  comb := (Design2.lowerComb_combIndices hl hd').symm
  edge₁ := hd'.edgeIndices_eq
  edge₂ := (Design2.lowerComb_phases hl).1
  reset₁ := hd'.resetIndices_eq
  reset₂ := (Design2.lowerComb_phases hl).2.1
  none := fun i h => by
    cases hp : d.processes[i]? with
    | none => rfl
    | some p =>
        obtain ⟨q, -, hq'⟩ := Design2.lowerComb_proc hl hp
        rw [h] at hq'; cases hq'
  proc := by
    intro i q hq'
    obtain ⟨p, hp, hq⟩ := Design2.lowerComb_proc' hl hq'
    refine ⟨p, hp, fun st hs f r hr => ?_⟩
    rcases Process2.lowerComb_eq_some hq with ⟨t, e, rfl, rfl⟩ | ⟨body, S, rfl, hsym, rfl⟩
    · obtain ⟨v, -, rfl⟩ := runCombProcess2_assign_write_ok hd' hs hq' hr
      exact ⟨hs.combWrite t v, f, by rw [hr]⟩
    · obtain ⟨v, hv, rfl⟩ := runCombProcess2_assign_write_ok hd' hs hq' hr
      obtain ⟨v', hv', hrun⟩ := runCombProcess2_alwaysComb_fwd hd'
        (Design2.lowerComb_spec hl).2.1 hsym hq' hs (Nat.le_refl body.fuelB)
      rw [hv, Res.ok.injEq] at hv'
      subst hv'
      exact ⟨hs.combWrite _ v, body.fuelB, hrun⟩
  init := StateShape.of_initState2 hd'
  inputs := fun inputs st hs => StateShape.of_applyInputs2 hd' hs inputs

/-- **The design and its lowering have the same completed runs** — under
every schedule, for every stimulus, with the same trace. -/
theorem Runs2.lowerComb_iff (hl : d.lowerComb = some d') (hd' : CombDesign d')
    {σ : ScheduleOracle} {stim tr : List SvState} :
    Runs2 d σ stim tr ↔ Runs2 d' σ stim tr :=
  ⟨(CombSim.of_lowerComb hl hd').runs2, (CombSim.of_lowerComb' hl hd').runs2⟩

/-- **`⊨₂` transfers from the lowered design.** -/
theorem Models2.of_lowerComb (hl : d.lowerComb = some d') (hd' : CombDesign d')
    {P : List SvState → List SvState → Prop} (h : d' ⊨₂ spec2 P) : d ⊨₂ spec2 P :=
  fun σ stim tr hr => h σ stim tr ((Runs2.lowerComb_iff hl hd').mp hr)

/-- **Termination transfers from the lowered design.** -/
theorem Terminates2.of_lowerComb (hl : d.lowerComb = some d') (hd' : CombDesign d')
    (h : Terminates2 d') : Terminates2 d := fun σ stim => by
  obtain ⟨tr, hr⟩ := h σ stim
  exact ⟨tr, (Runs2.lowerComb_iff hl hd').mpr hr⟩

/-- **The termination theorem for `always_comb`**: a design whose lowering
is in the comb profile with an acyclicity certificate terminates — the
certificate ranks every `always_comb` process by its read set (the reads of
its symbolic right-hand side) against every write window. -/
theorem Terminates2.of_lowerComb_acyclic (hl : d.lowerComb = some d') (hd' : CombDesign d')
    (ha : Acyclic d') : Terminates2 d :=
  Terminates2.of_lowerComb hl hd' (Terminates2.of_acyclic hd' ha)

/-- **`⊨₂` from the lowered equations** (the basic form, `Models2.of_comb`
for `always_comb` designs). -/
theorem Models2.of_combProc (hl : d.lowerComb = some d') (hd' : CombDesign d')
    {P : List SvState → List SvState → Prop}
    (hP : ∀ stim tr,
      (∀ (c : Nat) (st : SvState), tr[c]? = some st → CombEqs d' st ∧ StateShape d' st) →
        P stim tr) :
    d ⊨₂ spec2 P :=
  Models2.of_lowerComb hl hd' (Models2.of_comb hd' hP)

/-- `Models2.of_comb_inputs` for `always_comb` designs: the hypothesis also
receives, per cycle, that every input port bound by the cycle's stimulus
entry holds that value. -/
theorem Models2.of_combProc_inputs (hl : d.lowerComb = some d') (hd' : CombDesign d')
    {P : List SvState → List SvState → Prop}
    (hP : ∀ stim tr,
      (∀ (c : Nat) (st : SvState), tr[c]? = some st → CombEqs d' st ∧ StateShape d' st ∧
        ∀ inputs, stim[c]? = some inputs → ∀ n ∈ d'.inputNames.toList, ∀ v,
          SvState.lookup inputs n = some v → SvState.lookup st n = some v) →
        P stim tr) :
    d ⊨₂ spec2 P :=
  Models2.of_lowerComb hl hd' (Models2.of_comb_inputs hd' hP)

/-- **Pointwise `⊨₂`** for `always_comb` designs. -/
theorem Models2.of_combProc_pointwise (hl : d.lowerComb = some d') (hd' : CombDesign d')
    {Q : SvState → Prop} (hQ : ∀ st, CombEqs d' st → StateShape d' st → Q st) :
    d ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st → Q st :=
  Models2.of_lowerComb hl hd' (Models2.of_comb_pointwise hd' hQ)

/-! ## The fixpoint characterization -/

/-- **Every process maps `S` to itself** (running each assign, and each
`always_comb` body, on `S` yields `S`, at every fuel from some bound on) —
the settled-state condition for designs with `always_comb`. -/
def ProcFixpoint (d : Design2) (S : SvState) : Prop :=
  ∀ (i : Nat) (p : Process2), d.processes[i]? = some p →
    ∃ F, ∀ f, F ≤ f → runCombProcess2 f S p = .ok S

/-- **The generalized equations are the fixpoint condition**: on a shaped
state, every process of `d` maps `S` to itself iff `S` solves the lowered
design's equations (one per written window of every assign and every
`always_comb` body). -/
theorem procFixpoint_iff_combEqs (hl : d.lowerComb = some d') (hd' : CombDesign d')
    {S : SvState} (hs : StateShape d' S) : ProcFixpoint d S ↔ CombEqs d' S := by
  constructor
  · intro hfix i t e n lo w off hp hm
    obtain ⟨p, hpd, -⟩ := Design2.lowerComb_proc' hl hp
    obtain ⟨F, hF⟩ := hfix i p hpd
    obtain ⟨q, hq, hsim⟩ := (CombSim.of_lowerComb hl hd').proc i p hpd
    rw [hp, Option.some.injEq] at hq
    subst hq
    obtain ⟨-, f', hf'⟩ := hsim S hs F S (hF F (Nat.le_refl _))
    obtain ⟨v, hv, hS⟩ := runCombProcess2_assign_write_ok hd' hs hp hf'
    obtain ⟨u, hu, hue⟩ := hd'.combWrite_readBack hs hp v hm
    rw [← hS] at hu
    exact ⟨u, v, hu, hv, hue⟩
  · intro heqs i p hp
    obtain ⟨q, -, hq'⟩ := Design2.lowerComb_proc hl hp
    obtain ⟨t, e, ws, rfl, -⟩ := hd'.assign i q hq'
    obtain ⟨v, hv⟩ := hd'.evalPure2_ok hs hq'
    have hid : combWrite d' S t v = S := combWrite_eq_self fun n lo w off hm => by
      obtain ⟨old, v', hold, hv', hext⟩ := heqs i t e n lo w off hq' hm
      rw [hv, Res.ok.injEq] at hv'
      subst hv'
      exact ⟨old, hold, hext⟩
    have hrun : runCombProcess2 (e.size + 1) S (.assign t e) = .ok S := by
      rw [runCombProcess2_assign_write hd' hs hq' (Nat.lt_succ_self _) hv, hid]
    obtain ⟨p', hp', hsim⟩ := (CombSim.of_lowerComb' hl hd').proc i _ hq'
    rw [hp, Option.some.injEq] at hp'
    subst hp'
    obtain ⟨-, f', hf'⟩ := hsim S hs _ S hrun
    exact ⟨f', fun f hf => runCombProcess2_mono hf' (by simp) f hf⟩

/-- **Snapshots of a run of an `always_comb` design**: every snapshot is a
fixpoint of every process, solves the lowered equations and has the comb
shape. -/
theorem Runs2.combProc_snapshot (hl : d.lowerComb = some d') (hd' : CombDesign d')
    {σ : ScheduleOracle} {stim tr : List SvState} (hr : Runs2 d σ stim tr) {c : Nat}
    {st : SvState} (hc : tr[c]? = some st) :
    ProcFixpoint d st ∧ CombEqs d' st ∧ StateShape d' st := by
  obtain ⟨heqs, hs, -⟩ := ((Runs2.lowerComb_iff hl hd').mp hr).comb_snapshot hd' hc
  exact ⟨(procFixpoint_iff_combEqs hl hd' hs).mpr heqs, heqs, hs⟩

/-- **One equation per written window of an `always_comb` body**: in a
shaped solution of the lowered equations, every window the body's symbolic
execution wrote holds the value, in that same state, of its symbolic
expression. -/
theorem CombEqs.symWindow (hl : d.lowerComb = some d') (hd' : CombDesign d') {S : SvState}
    (heqs : CombEqs d' S) (hs : StateShape d' S) {i : Nat} {body : Stmt2}
    (hp : d.processes[i]? = some (.alwaysComb body)) {sy : SymState}
    (hsym : body.symExec d [] = some sy) {W : Win} {E : Expr2} (hm : (W, E) ∈ sy) {v : LVec}
    (hv : evalPure2 S E = .ok v) :
    ∃ u, SvState.lookup S W.1 = some u ∧ u.extract W.2.1 W.2.2 = v := by
  obtain ⟨F, hF⟩ := (procFixpoint_iff_combEqs hl hd' hs).mpr heqs i _ hp
  have hrun := hF F (Nat.le_refl _)
  obtain ⟨q, hq, hq'⟩ := Design2.lowerComb_proc hl hp
  obtain ⟨sy', hsy', -, rfl⟩ := Process2.lowerComb_alwaysComb hq
  rw [hsym, Option.some.injEq] at hsy'
  subst hsy'
  simp only [runCombProcess2, Res.bind_eq_ok] at hrun
  obtain ⟨⟨st', nba⟩, hexec, hr⟩ := hrun
  obtain ⟨rfl, hR⟩ := (symExec_sound F).1 body [] sy S [] st' nba hsym
    (SymOk.of_shape (Design2.lowerComb_spec hl).2.1 hq' hs) (SymRel.init S) hexec
  simp only [Res.ok.injEq] at hr
  subst hr
  exact hR.entry W E hm v hv

/-- **A whole-signal window, read back**: if the body's symbolic execution
wrote all of `n` (window `(n, 0, w)`, `w` its declared width), then in a
shaped solution `n` holds its symbolic expression's value. -/
theorem CombEqs.symWindow_ident (hl : d.lowerComb = some d') (hd' : CombDesign d')
    {S : SvState} (heqs : CombEqs d' S) (hs : StateShape d' S) {i : Nat} {body : Stmt2}
    (hp : d.processes[i]? = some (.alwaysComb body)) {sy : SymState}
    (hsym : body.symExec d [] = some sy) {n : String} {w : Nat} {E : Expr2}
    (hm : ((n, 0, w), E) ∈ sy) (hw : d.declWidth n = some w) {v : LVec}
    (hv : evalPure2 S E = .ok v) : SvState.lookup S n = some v := by
  obtain ⟨u, hu, hext⟩ := CombEqs.symWindow hl hd' heqs hs hp hsym hm hv
  obtain ⟨q, hq, hq'⟩ := Design2.lowerComb_proc hl hp
  obtain ⟨sy', hsy', -, rfl⟩ := Process2.lowerComb_alwaysComb hq
  rw [hsym, Option.some.injEq] at hsy'
  subst hsy'
  have hok := SymOk.of_shape (Design2.lowerComb_spec hl).2.1 hq' hs
  have hwu := hok n (SymState.mem_names.mpr ⟨_, hm, rfl⟩) w hw
  rw [hu] at hwu
  simp only [Option.map_some, Option.some.injEq] at hwu
  simp only at hext
  rw [← hwu, LVec.extract_full] at hext
  rw [hu, hext]

/-- **One run of a lowered body is already its own fixpoint**: on a shaped
state, re-running an `always_comb` body of the profile on the state its
run produced changes nothing. This is why the settle semantics (which
re-runs a comb process until nothing changes) and an event-driven simulator
(which runs an `always_comb` block once per wake-up and is never woken by
the block's own writes, IEEE 1800-2023 §9.2.2.2.1) give a body of the
profile the same result. The lowering's self-read check
(`SymState.selfReadFree`) is the hypothesis that makes it true: the lowered
right-hand side reads nothing the run writes. -/
theorem runCombProcess2_alwaysComb_idem (hl : d.lowerComb = some d') (hd' : CombDesign d')
    {i : Nat} {body : Stmt2} (hp : d.processes[i]? = some (.alwaysComb body)) {st : SvState}
    (hs : StateShape d' st) {f : Nat} (hf : body.fuelB ≤ f) {r : SvState}
    (h : runCombProcess2 f st (.alwaysComb body) = .ok r) :
    runCombProcess2 f r (.alwaysComb body) = .ok r := by
  obtain ⟨q, hq, hq'⟩ := Design2.lowerComb_proc hl hp
  obtain ⟨S, hsym, hfree, rfl⟩ := Process2.lowerComb_alwaysComb hq
  have hdecls := (Design2.lowerComb_spec hl).2.1
  obtain ⟨v, hv, rfl⟩ := runCombProcess2_alwaysComb_ok hd' hdecls hsym hq' hs h
  obtain ⟨v', hv', hrun⟩ :=
    runCombProcess2_alwaysComb_fwd hd' hdecls hsym hq' (hs.combWrite S.target v) hf
  have hsame : evalPure2 (combWrite d' st S.target v) S.rhs = evalPure2 st S.rhs := by
    refine (evalPure2_congr_reads fun rd hrd => ReadWin.agree_combWrite fun wn hwn => ?_).symm
    rw [SymState.target_wins] at hwn
    exact SymState.selfReadFree_iff.mp hfree rd hrd wn hwn
  rw [hsame, hv, Res.ok.injEq] at hv'
  subst hv'
  rw [hrun]
  congr 1
  exact combWrite_eq_self fun n lo w off hm => hd'.combWrite_readBack hs hq' v hm

end Lowered

/-! ## Single-process designs: the profile as decidable checks

A design whose only process is one `always_comb` lowers to a design whose
only process is one assign. For such a design the comb profile and the
acyclicity certificate reduce to finitely many checks on closed data, each
discharged by `decide` (or `rfl`) on a concrete design. -/

/-- **The comb profile of a one-assign design**, from static checks. -/
theorem CombDesign.of_single {d : Design2} {t : Lhs2} {e : Expr2}
    (hp : d.processes = #[.assign t e]) (hnodup : (d.decls.toList.map Decl.name).Nodup)
    {ws : List Win} (hws : t.windows? d = some ws)
    (hin : ∀ W ∈ ws, ((d.declWidth W.1).map fun dw => decide (W.2.1 + W.2.2 ≤ dw)) = some true)
    (hni : ∀ W ∈ ws, W.1 ∉ d.inputNames.toList)
    (hdisj : Win.allDisjoint ws = true) (hfree : e.unsupportedFree = true)
    (hdecl : ∀ x ∈ e.idents, x ∈ d.decls.toList.map Decl.name)
    (hinit : ∀ dc ∈ d.decls.toList, dc.name ∈ ws.map Prod.fst →
      dc.init.all (fun v => v.width == dc.width) = true)
    (hfour : ∀ dc ∈ d.decls.toList, dc.isInput = true → dc.twoState = false) :
    CombDesign d := by
  have hproc : ∀ {i : Nat} {p : Process2}, d.processes[i]? = some p → i = 0 ∧ p = .assign t e := by
    intro i p h
    rw [hp] at h
    match i, h with
    | 0, h => simpa [eq_comm] using h
  have hwins : t.wins d = ws := Lhs2.wins_of_windows? hws
  have hW : ∀ {i : Nat} {wn : Win}, d.Writes i wn → i = 0 ∧ wn ∈ ws := by
    rintro i wn ⟨t', e', h, hm⟩
    obtain ⟨rfl, hpe⟩ := hproc h
    simp only [Process2.assign.injEq] at hpe
    obtain ⟨rfl, rfl⟩ := hpe
    exact ⟨rfl, hwins ▸ hm⟩
  refine ⟨hnodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfour⟩
  · intro i p h
    obtain ⟨-, rfl⟩ := hproc h
    exact ⟨t, e, ws, rfl, hws⟩
  · intro i n lo w h
    have := hin _ (hW h).2
    cases hdw : d.declWidth n with
    | none => simp [hdw] at this
    | some dw => simp only [hdw, Option.map_some, Option.some.injEq,
        decide_eq_true_eq] at this; exact ⟨dw, rfl, this⟩
  · rintro n ⟨i, lo, w, h⟩
    exact hni _ (hW h).2
  · intro i j wi wj hij hi hj
    exact absurd ((hW hi).1.trans (hW hj).1.symm) hij
  · intro i t' e' h
    obtain ⟨-, hpe⟩ := hproc h
    simp only [Process2.assign.injEq] at hpe
    obtain ⟨rfl, rfl⟩ := hpe
    rw [hwins]
    exact (Win.allDisjoint_iff ws).mp hdisj
  · intro i t' e' h
    obtain ⟨-, hpe⟩ := hproc h
    simp only [Process2.assign.injEq] at hpe
    obtain ⟨rfl, rfl⟩ := hpe
    exact hfree
  · intro i t' e' h
    obtain ⟨-, hpe⟩ := hproc h
    simp only [Process2.assign.injEq] at hpe
    obtain ⟨rfl, rfl⟩ := hpe
    exact hdecl
  · rintro n ⟨i, lo, w, h⟩ dc hdc rfl v hv
    have := hinit dc hdc (List.mem_map.mpr ⟨_, (hW h).2, rfl⟩)
    simpa [hv] using this

/-- **Acyclicity of a one-assign design**: its right-hand side reads none of
its own windows (any rank works). -/
theorem Acyclic.of_single {d : Design2} {t : Lhs2} {e : Expr2}
    (hp : d.processes = #[.assign t e])
    (h : ∀ r ∈ e.reads, ∀ W ∈ t.wins d, r.overlaps W = false) : Acyclic d := by
  refine ⟨fun _ => 0, ?_⟩
  intro i j ti ei tj ej wj hi hj hw ⟨r, hr, hov⟩
  exfalso
  rw [hp] at hi hj
  match i, j, hi, hj with
  | 0, 0, hi, hj =>
      simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq,
        Process2.assign.injEq] at hi hj
      obtain ⟨rfl, rfl⟩ := hi
      obtain ⟨rfl, rfl⟩ := hj
      rw [h r hr wj hw] at hov
      cases hov

/-- **The lowering of a one-`always_comb` design is acyclic, for free**: the
self-read check the lowering already ran (`SymState.selfReadFree`) is the
whole acyclicity obligation of a single process. -/
theorem Acyclic.of_lowerComb_single {d d' : Design2} (hl : d.lowerComb = some d')
    {body : Stmt2} (hp : d.processes = #[.alwaysComb body]) : Acyclic d' := by
  obtain ⟨-, -, hsize, hget⟩ := Design2.lowerComb_spec hl
  have hq : d'.processes[0]? = (Process2.alwaysComb body).lowerComb d := by
    rw [hget 0, hp]; rfl
  have h1 : d'.processes.size = 1 := by rw [hsize, hp]; rfl
  cases hq' : (Process2.alwaysComb body).lowerComb d with
  | none =>
      rw [hq', Array.getElem?_eq_getElem (by omega : 0 < d'.processes.size)] at hq
      cases hq
  | some q =>
      obtain ⟨S, -, hfree, rfl⟩ := Process2.lowerComb_alwaysComb hq'
      rw [hq'] at hq
      refine ⟨fun _ => 0, ?_⟩
      intro i j ti ei tj ej wj hi hj hw ⟨rd, hrd, hov⟩
      exfalso
      have hi0 : i = 0 := by have := (Array.getElem?_eq_some_iff.mp hi).1; omega
      have hj0 : j = 0 := by have := (Array.getElem?_eq_some_iff.mp hj).1; omega
      subst hi0 hj0
      rw [hq] at hi hj
      simp only [SymState.toAssign, Option.some.injEq, Process2.assign.injEq] at hi hj
      obtain ⟨rfl, rfl⟩ := hi
      obtain ⟨rfl, rfl⟩ := hj
      rw [SymState.target_wins] at hw
      rw [SymState.selfReadFree_iff.mp hfree rd hrd wj hw] at hov
      cases hov

/-- **Termination of a one-`always_comb` design** from the lowering and the
comb profile alone (`Acyclic.of_lowerComb_single` supplies the
certificate). -/
theorem Terminates2.of_lowerComb_single {d d' : Design2} (hl : d.lowerComb = some d')
    (hd' : CombDesign d') {body : Stmt2} (hp : d.processes = #[.alwaysComb body]) :
    Terminates2 d :=
  Terminates2.of_lowerComb_acyclic hl hd' (Acyclic.of_lowerComb_single hl hp)

end LeanModels.Sv
