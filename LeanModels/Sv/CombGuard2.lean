import LeanModels.Sv.Sem2

/-!
# The self-read guard for `always_comb` (`LeanModels.Sv` — Design2, WP4)

**Decided by Thomas, 2026-10-28: refuse self-reading `always_comb` bodies,
loudly.** `combSettle2` (`Sem2.lean`) re-runs every comb-phase process until
no signal changes. An event-driven simulator runs an `always_comb` block once
at time zero and then once per change of a variable in its implicit
sensitivity list, and IEEE 1800-2023 §9.2.2.2.1 leaves out of that list
"b) Any expression that is also written within the block": the block is never
woken by its own writes. So when one run of a body reads a bit and LATER
writes it, the value read is the previous run's end value, while the settle
semantics re-runs the block and reads the value the block settles to.
Measured on `always_comb begin if (c) t = a; y = t; t = b; end`
(`Examples/system-verilog/sem2/rbw_held`) and `y = t; t = a;` (`sem2/rbw_comb`):
Icarus 12, Xcelium 24.03/26.09 and mox-sim show the stale value; Verilator
5.042, Yosys 0.53 and the settle semantics give the combinational one. No
answer is safe for every tool, so such a block is refused.

## The rule (path-sensitive, per bit)

A body is refused when, on some control path through it, a bit is READ before
the path has written it AND the path WRITES that bit later. Only then can the
value read (the previous run's) differ from the value the block settles to.
So `y = t; t = a;` is refused, `if (c) t = a; y = t; t = b;` is refused (the
`c = 0` path), a latch `if (en) q = d;` is admitted, and so is a latch that
reads its own held value, `if (en) q = d; y = q;` (the held bit is not
written later on that path). Bits, not whole variables: `t[0] = a; y = t[1];
t[1] = b;` is refused, `t[0] = a; y = t[0]; t[1] = b;` is not.

The check is a static walk (`Stmt2.combViol`) carrying two bit sets:

* `M`, the bits written on EVERY path from the start of the body to the
  current point (`Stmt2.mustW`: an `if` without `else` and a `case` without
  `default` must-write nothing; a run-time index target must-writes nothing);
* `A`, the bits written on SOME path from the end of the current statement to
  the end of the body (`Stmt2.mayW`: a run-time index target may write every
  bit of its signal).

A read of a bit outside `M` that some later statement — or the current
assignment itself — may write is a violation. Because the body has no loops,
every path through a point is a prefix reaching the point followed by a
suffix leaving it, chosen independently, so "outside `M`, inside `A`" is
exactly "some path reads the bit unwritten and writes it later". Conditions
are treated as independent: a body whose only violating path is statically
infeasible (`if (c) t = a; y = t; if (c) t = b;`) is refused too — the
conservative direction.

Reads (`Expr2.rdW`, `Lhs2.rdW`): every identifier read — `if` conditions,
`case` subjects and item patterns, index expressions of reads and of targets,
and the operands of compound assignments (the symbolic extractor currently
refuses `y += t` itself, `AssignmentExpression:compound`; lowered to
`y = y + t` its operands are ordinary reads, pinned below). A constant slice `n[lo +: w]` reads exactly its bits; a
whole-signal read reads every declared bit (the width table `wd`); a run-time
index read `n[i]` reads every bit of `n` (a may-overlap is an overlap). After
instantiation every constant index is a constant slice (`instExpr2`,
`instLhsLeaf2`), so run-time indices are exactly the `.index` nodes and
constant ones are decided exactly. Writes (`Lhs2.mayW`/`Lhs2.mustW`): a
whole-signal or constant-slice target writes exactly its bits; a
part-select writes only its bits; a procedural concatenation target may write
its leaves and must-writes nothing.

## Where it applies

Every `Process2` kind that `combSettle2` re-runs to a fixpoint and an
event-driven simulator runs once per wake-up: in the sv-0.2 tier that is
`Process2.alwaysComb` alone. Continuous `assign`s are re-evaluated on every
change of their right-hand side — their own writes included — by the LRM as
by the settle semantics, and `always_ff`/plain `always @(posedge …)`/
`alwaysFFR` run once per edge in both; they are untouched. `always @*`,
`always @(a or b)`, `always @(a)` and `always_latch` never reach `Process2`:
the symbolic extractor refuses them (`TimedStatement:ImplicitEventControl`,
`TimedStatement:EventListControl`, `SignalEventControl:None_`,
`ProceduralBlockSymbol:AlwaysLatch`; measured 2026-10-28). Should one of
them be admitted later as a comb-phase process, it must go through
`combGuardProc` too.

The guard is applied per process, at every parameter point, where an
instantiated `always_comb` is built (`instProcess2`, `Param2.lean`): a
refused body becomes `Process2.unsupported "AlwaysComb:self-read" msg`
(`combGuardProc`), whose message names the signal, the bits and IEEE
1800-2023 §9.2.2.2.1, so `run2`, the differential runner and every
`name.sem` are loud on it, and `load_design_sv2` refuses the envelope at the
defaults with the same message.

## Justification

`CombGuard2Sound.lean` proves that a body the guard admits is idempotent on
shaped states: running it on the state its own run produced changes nothing
(`CombGuard.execStmt2_idem_of_admits`, and at the process level
`runCombProcess2_alwaysComb_idem_of_admits`). An admitted block therefore
reaches the fixpoint the settle semantics computes in the ONE run an
event-driven simulator makes per wake-up.

## Symbolic parameters

The walk is ordinary structural recursion: `decide`/`rfl` evaluate it on a
closed body, and at a symbolic width `simp [Stmt2.combViol, …]` evaluates it
whenever every read/may-write pair it compares is on two DIFFERENT signals
(the window intersection is then empty without looking at a width) — the
case of every body that reads only signals it does not write, and of the
usual "write the temporary, then read it" bodies, whose reads of a written
signal meet only the windows written BEFORE them (`Comb2ProcExample.as_admits`
is the worked example). A read of a signal that is also written later needs
the bit arithmetic of `BWin.subAll` at the symbolic width.
-/

namespace LeanModels.Sv

namespace CombGuard

/-! ## Bit windows -/

/-- A bit window `(signal, lo, w)`: bits `lo ≤ i < lo + w` of `signal`. -/
abbrev BWin := String × Nat × Nat

/-- Bit `(n, i)` lies in window `W`. -/
def BWin.Mem (W : BWin) (n : String) (i : Nat) : Prop :=
  W.1 = n ∧ W.2.1 ≤ i ∧ i < W.2.1 + W.2.2

/-- Bit `(n, i)` lies in some window of `L`. -/
def InSet (L : List BWin) (n : String) (i : Nat) : Prop := ∃ W ∈ L, W.Mem n i

/-- The intersection of two windows (empty — width `0` — on different
signals). -/
def BWin.inter (a b : BWin) : BWin :=
  if a.1 = b.1 then
    (a.1, max a.2.1 b.2.1, min (a.2.1 + a.2.2) (b.2.1 + b.2.2) - max a.2.1 b.2.1)
  else (a.1, a.2.1, 0)

/-- `a` minus `b`: at most two non-empty windows. -/
def BWin.sub (a b : BWin) : List BWin :=
  if a.1 = b.1 then
    (if a.2.1 < min (a.2.1 + a.2.2) b.2.1 then [(a.1, a.2.1, min (a.2.1 + a.2.2) b.2.1 - a.2.1)]
     else []) ++
    (if max a.2.1 (b.2.1 + b.2.2) < a.2.1 + a.2.2 then
       [(a.1, max a.2.1 (b.2.1 + b.2.2), a.2.1 + a.2.2 - max a.2.1 (b.2.1 + b.2.2))]
     else [])
  else if a.2.2 = 0 then [] else [a]

/-- `a` minus every window of `bs`: the non-empty pieces left over. -/
def BWin.subAll (a : BWin) : List BWin → List BWin
  | [] => if a.2.2 = 0 then [] else [a]
  | b :: bs => (a.sub b).flatMap fun p => BWin.subAll p bs

/-- Pairwise intersections of two window lists (`InSet` of the result is
the conjunction, `CombGuard2Sound.inSet_interL`). -/
def interL (X Y : List BWin) : List BWin := X.flatMap fun x => Y.map fun y => x.inter y

/-- The first bits of a read set `R` that lie in `A` but not in `M`: `none`
when every read bit `A` may write is already in `M`. -/
def readsViol (M A R : List BWin) : Option BWin :=
  R.findSome? fun r => A.findSome? fun x => ((r.inter x).subAll M).head?

/-! ## Read and write sets -/

/-- The whole of signal `n` (its declared width from `wd`; an undeclared
name is never present in a shaped state). -/
def whole (wd : String → Option Nat) (n : String) : BWin := (n, 0, (wd n).getD 0)

/-- Reads under a slice: a slice of an identifier reads exactly its bits;
any other slice reads what its base reads. -/
def sliceRd : Expr2 → Nat → Nat → List BWin → List BWin
  | .ident n, lo, w, _ => [(n, lo, w)]
  | _, _, _, r => r

end CombGuard

open CombGuard

mutual
/-- The bits an expression may read (`wd`: declared widths). -/
def Expr2.rdW (wd : String → Option Nat) : Expr2 → List BWin
  | .lit _ => []
  | .ident n => [whole wd n]
  | .unsupported _ _ => []
  | .unary _ a => a.rdW wd
  | .resizeSigned _ a => a.rdW wd
  | .squash2 a => a.rdW wd
  | .repl _ a => a.rdW wd
  | .reduce _ a => a.rdW wd
  | .resize _ a => a.rdW wd
  | .binary _ l r => l.rdW wd ++ r.rdW wd
  | .scmp _ l r => l.rdW wd ++ r.rdW wd
  | .logical _ l r => l.rdW wd ++ r.rdW wd
  | .ternary c t f => c.rdW wd ++ (t.rdW wd ++ f.rdW wd)
  | .slice a lo w => sliceRd a lo w (a.rdW wd)
  | .index a i _ => a.rdW wd ++ i.rdW wd
  | .concat ps => Expr2.listRdW wd ps.toList
termination_by structural e => e

/-- `Expr2.rdW` of a list. -/
def Expr2.listRdW (wd : String → Option Nat) : List Expr2 → List BWin
  | [] => []
  | e :: es => e.rdW wd ++ Expr2.listRdW wd es
termination_by structural es => es
end

mutual
/-- The bits evaluating an assignment target reads (its run-time index
expressions). -/
def Lhs2.rdW (wd : String → Option Nat) : Lhs2 → List BWin
  | .ident _ => []
  | .slice _ _ _ => []
  | .index _ i _ => i.rdW wd
  | .concat ps => Lhs2.listRdW wd ps
termination_by structural t => t

/-- `Lhs2.rdW` of a list. -/
def Lhs2.listRdW (wd : String → Option Nat) : List Lhs2 → List BWin
  | [] => []
  | t :: ts => t.rdW wd ++ Lhs2.listRdW wd ts
termination_by structural ts => ts
end

mutual
/-- The bits an assignment target may write: a run-time index may write any
bit of its signal. -/
def Lhs2.mayW (wd : String → Option Nat) : Lhs2 → List BWin
  | .ident n => [whole wd n]
  | .slice n lo w => [(n, lo, w)]
  | .index n _ _ => [whole wd n]
  | .concat ps => Lhs2.listMayW wd ps
termination_by structural t => t

/-- `Lhs2.mayW` of a list. -/
def Lhs2.listMayW (wd : String → Option Nat) : List Lhs2 → List BWin
  | [] => []
  | t :: ts => t.mayW wd ++ Lhs2.listMayW wd ts
termination_by structural ts => ts
end

/-- The bits an assignment target surely writes: a whole signal or a
constant slice; nothing for a run-time index (an x/z or out-of-range index
writes nothing) or a concatenation (conservatively). -/
def Lhs2.mustW (wd : String → Option Nat) : Lhs2 → List BWin
  | .ident n => [whole wd n]
  | .slice n lo w => [(n, lo, w)]
  | .index _ _ _ => []
  | .concat _ => []

mutual
/-- The bits a statement may write (on some path). Nonblocking assignments
write nothing during the run. -/
def Stmt2.mayW (wd : String → Option Nat) : Stmt2 → List BWin
  | .blockingAssign t _ => t.mayW wd
  | .nbaAssign _ _ => []
  | .ifStmt _ a b => a.mayW wd ++ Stmt2.optMayW wd b
  | .block ss => Stmt2.listMayW wd ss.toList
  | .caseStmt _ its d _ _ => CaseItem2.listMayW wd its.toList ++ Stmt2.optMayW wd d
  | .unsupported _ _ => []
termination_by structural s => s

/-- `Stmt2.mayW` of an optional statement. -/
def Stmt2.optMayW (wd : String → Option Nat) : Option Stmt2 → List BWin
  | none => []
  | some s => s.mayW wd
termination_by structural o => o

/-- `Stmt2.mayW` of a statement list. -/
def Stmt2.listMayW (wd : String → Option Nat) : List Stmt2 → List BWin
  | [] => []
  | s :: ss => s.mayW wd ++ Stmt2.listMayW wd ss
termination_by structural ss => ss

/-- `Stmt2.mayW` of a case arm's body. -/
def CaseItem2.mayW (wd : String → Option Nat) : CaseItem2 → List BWin
  | .mk _ b => b.mayW wd
termination_by structural it => it

/-- `CaseItem2.mayW` of an arm list. -/
def CaseItem2.listMayW (wd : String → Option Nat) : List CaseItem2 → List BWin
  | [] => []
  | it :: rest => it.mayW wd ++ CaseItem2.listMayW wd rest
termination_by structural its => its
end

mutual
/-- The bits a statement writes on EVERY path: the intersection over the
branches of an `if`/`else` or of a `case` with `default`; nothing for an
`if` without `else` or a `case` without `default`. -/
def Stmt2.mustW (wd : String → Option Nat) : Stmt2 → List BWin
  | .blockingAssign t _ => t.mustW wd
  | .nbaAssign _ _ => []
  | .ifStmt _ a b =>
      match Stmt2.optMustW wd b with
      | some mb => interL (a.mustW wd) mb
      | none => []
  | .block ss => Stmt2.listMustW wd ss.toList
  | .caseStmt _ its d _ _ =>
      match Stmt2.optMustW wd d with
      | some md => CaseItem2.listMustW wd md its.toList
      | none => []
  | .unsupported _ _ => []
termination_by structural s => s

/-- `Stmt2.mustW` of an optional statement (`none`: absent). -/
def Stmt2.optMustW (wd : String → Option Nat) : Option Stmt2 → Option (List BWin)
  | none => none
  | some s => some (s.mustW wd)
termination_by structural o => o

/-- The union of `Stmt2.mustW` over a statement list (a sequence). -/
def Stmt2.listMustW (wd : String → Option Nat) : List Stmt2 → List BWin
  | [] => []
  | s :: ss => s.mustW wd ++ Stmt2.listMustW wd ss
termination_by structural ss => ss

/-- `Stmt2.mustW` of a case arm's body. -/
def CaseItem2.mustW (wd : String → Option Nat) : CaseItem2 → List BWin
  | .mk _ b => b.mustW wd
termination_by structural it => it

/-- The intersection of the arms' `mustW` with the default's `md`. -/
def CaseItem2.listMustW (wd : String → Option Nat) (md : List BWin) :
    List CaseItem2 → List BWin
  | [] => md
  | it :: rest => interL (it.mustW wd) (CaseItem2.listMustW wd md rest)
termination_by structural its => its
end

/-! ## The check -/

mutual
/-- **The first self-read violation** of statement `s` (`none`: none),
given the bits `M` written on every path before `s` and the bits `A` some
path may write after `s` (module docstring). An assignment reads its
right-hand side and its target's index expressions BEFORE it writes its
target. -/
def Stmt2.combViol (wd : String → Option Nat) (M A : List BWin) : Stmt2 → Option BWin
  | .blockingAssign t e => readsViol M (t.mayW wd ++ A) (e.rdW wd ++ t.rdW wd)
  | .nbaAssign t e => readsViol M A (e.rdW wd ++ t.rdW wd)
  | .ifStmt c a b =>
      readsViol M (a.mayW wd ++ Stmt2.optMayW wd b ++ A) (c.rdW wd) <|>
        a.combViol wd M A <|> Stmt2.optCombViol wd M A b
  | .block ss => Stmt2.listCombViol wd M A ss.toList
  | .caseStmt subj its d _ _ =>
      readsViol M (CaseItem2.listMayW wd its.toList ++ Stmt2.optMayW wd d ++ A) (subj.rdW wd) <|>
        CaseItem2.listCombViol wd M A (Stmt2.optMayW wd d) (Stmt2.optCombViol wd M A d) its.toList
  | .unsupported _ _ => none
termination_by structural s => s

/-- `Stmt2.combViol` of an optional statement. -/
def Stmt2.optCombViol (wd : String → Option Nat) (M A : List BWin) :
    Option Stmt2 → Option BWin
  | none => none
  | some s => s.combViol wd M A
termination_by structural o => o

/-- A sequence: each statement sees the must-writes of the ones before it
and the may-writes of the ones after it. -/
def Stmt2.listCombViol (wd : String → Option Nat) (M A : List BWin) :
    List Stmt2 → Option BWin
  | [] => none
  | s :: ss =>
      s.combViol wd M (Stmt2.listMayW wd ss ++ A) <|>
        Stmt2.listCombViol wd (M ++ s.mustW wd) A ss
termination_by structural ss => ss

/-- The arms of a `case` (`dA`: the default's may-writes, `dV`: the
default's violation): arm `k`'s patterns are read before arm `k`'s body and
every later arm's body or the default may run. -/
def CaseItem2.listCombViol (wd : String → Option Nat) (M A dA : List BWin)
    (dV : Option BWin) : List CaseItem2 → Option BWin
  | [] => dV
  | .mk pats body :: rest =>
      readsViol M (body.mayW wd ++ CaseItem2.listMayW wd rest ++ dA ++ A)
          (Expr2.listRdW wd pats.toList) <|>
        body.combViol wd M A <|> CaseItem2.listCombViol wd M A dA dV rest
termination_by structural its => its
end

/-! ## The guard -/

/-- **The admission test**: the bit-level walk from an empty must-set and an
empty may-after set finds no self-read. -/
def Stmt2.combAdmits (wd : String → Option Nat) (body : Stmt2) : Bool :=
  (body.combViol wd [] []).isNone

/-- A design's declared-width table, as `instProcess2` hands it to the guard
(`env.widths.lookup` over the instantiated declarations; the first
declaration of a name wins). -/
def Design2.combWd (d : Design2) (n : String) : Option Nat :=
  (d.decls.toList.map fun dc => (dc.name, dc.width)).lookup n

/-- The refusal message for a violating window `(n, lo, w)`. -/
def selfReadMsg (W : BWin) : String :=
  let bits := if W.2.2 = 1 then s!"bit [{W.2.1}]" else s!"bits [{W.2.1 + W.2.2 - 1}:{W.2.1}]"
  let them := if W.2.2 = 1 then "it" else "them"
  s!"always_comb block reads {bits} of '{W.1}' before writing {them} on some path through its body, and writes {them} later on that path: IEEE 1800-2023 §9.2.2.2.1 leaves the variables a block writes out of its implicit sensitivity list, so an event-driven simulator runs the block once per wake-up and that read sees the PREVIOUS run's value (Icarus 12, Xcelium), while the settle semantics re-runs the block to its fixpoint (as Verilator 5.042 and Yosys 0.53 do): no answer is safe, so the block is refused (write the bits before every read of them, or move the read after the last write)"

/-- **The guard on one instantiated `always_comb` body** (`wd`: declared
widths at this parameter point): the process itself when admitted, else a
loud `AlwaysComb:self-read` process naming the first violating bits. -/
def combGuardProc (wd : String → Option Nat) (body : Stmt2) : Process2 :=
  if body.combAdmits wd then .alwaysComb body
  else
    match body.combViol wd [] [] with
    | some W => .unsupported "AlwaysComb:self-read" (selfReadMsg W)
    | none => .alwaysComb body

/-- An admitted body passes through unchanged. -/
theorem combGuardProc_of_admits {wd : String → Option Nat} {body : Stmt2}
    (h : body.combAdmits wd = true) : combGuardProc wd body = .alwaysComb body := by
  simp [combGuardProc, h]

/-- A body whose walk finds the window `W` is refused with `W`'s message. -/
theorem combGuardProc_of_viol {wd : String → Option Nat} {body : Stmt2} {W : BWin}
    (h : body.combViol wd [] [] = some W) :
    combGuardProc wd body = .unsupported "AlwaysComb:self-read" (selfReadMsg W) := by
  simp [combGuardProc, Stmt2.combAdmits, h]

/-! ## Pinned shapes (`#guard`; the SV twins are the `sem2/rbw_*` and
`sem2/acg_*` fixtures of `harness/sv/cases2.json`) -/

private def wd4 : String → Option Nat
  | "t" => some 2 | "u" => some 4 | "y" => some 2 | "q" => some 1
  | "a" => some 2 | "b" => some 2 | "c" => some 1 | "en" => some 1
  | "s" => some 2 | "d" => some 1
  | _ => none

private def ba (n : String) (e : Expr2) : Stmt2 := .blockingAssign (.ident n) e
private def bs (n : String) (lo w : Nat) (e : Expr2) : Stmt2 := .blockingAssign (.slice n lo w) e
private def id' (n : String) : Expr2 := .ident n
private def blk (ss : List Stmt2) : Stmt2 := .block ss.toArray

-- `y = t; t = a;` (rbw_comb): refused on all of `t`.
#guard (blk [ba "y" (id' "t"), ba "t" (id' "a")]).combViol wd4 [] [] == some ("t", 0, 2)
-- `if (c) t = a; y = t; t = b;` (rbw_held): refused (the c = 0 path).
#guard (blk [.ifStmt (id' "c") (ba "t" (id' "a")) none, ba "y" (id' "t"), ba "t" (id' "b")]).combViol
    wd4 [] [] == some ("t", 0, 2)
-- a latch `if (en) q = d;`: admitted.
#guard (blk [.ifStmt (id' "en") (ba "q" (id' "d")) none]).combAdmits wd4
-- a latch reading its held value `if (en) q = d; y = q;`: admitted.
#guard (blk [.ifStmt (id' "en") (ba "q" (id' "d")) none, ba "y" (id' "q")]).combAdmits wd4
-- bits: `t[0] = a; y = t[1]; t[1] = b;` refused on bit 1 only …
#guard (blk [bs "t" 0 1 (id' "a"), ba "y" (.slice (id' "t") 1 1), bs "t" 1 1 (id' "b")]).combViol
    wd4 [] [] == some ("t", 1, 1)
-- … `t[0] = a; y = t[0]; t[1] = b;` admitted.
#guard (blk [bs "t" 0 1 (id' "a"), ba "y" (.slice (id' "t") 0 1), bs "t" 1 1 (id' "b")]).combAdmits wd4
-- a temporary written on every path before the read: admitted.
#guard (blk [.ifStmt (id' "c") (ba "t" (id' "a")) (some (ba "t" (id' "b"))), ba "y" (id' "t")]).combAdmits wd4
-- two part-select writes covering `u` before a whole read: admitted (widths).
#guard (blk [bs "u" 0 2 (id' "a"), bs "u" 2 2 (id' "b"), ba "y" (id' "u")]).combAdmits wd4
-- … one of them after the read: refused on bits [3:2].
#guard (blk [bs "u" 0 2 (id' "a"), ba "y" (.slice (id' "u") 2 2), bs "u" 2 2 (id' "b")]).combViol
    wd4 [] [] == some ("u", 2, 2)
-- a read in a condition before the write: refused; after it: admitted.
#guard ((blk [.ifStmt (id' "t") (ba "y" (id' "a")) (some (ba "y" (id' "b"))), ba "t" (id' "c")]).combViol
    wd4 [] []).isSome
#guard (blk [ba "t" (id' "a"), .ifStmt (id' "t") (ba "y" (id' "a")) (some (ba "y" (id' "b")))]).combAdmits wd4
-- a run-time index read before a write: refused (may-overlap = overlap) …
#guard ((blk [ba "q" (.index (id' "t") (id' "s") 1), ba "t" (id' "a")]).combViol wd4 [] []).isSome
-- … after a whole write, followed by a run-time write and a whole read: admitted.
#guard (blk [ba "t" (id' "a"), ba "q" (.index (id' "t") (id' "s") 1),
    .blockingAssign (.index "t" (id' "s") 1) (id' "c"), ba "y" (id' "t")]).combAdmits wd4
-- a case item reading a later-written signal: refused.
#guard ((blk [.caseStmt (id' "s") #[.mk #[id' "t"] (ba "q" (id' "c"))] (some (ba "q" (id' "d"))) false .none,
    ba "t" (id' "a")]).combViol wd4 [] []).isSome
-- a case writing `t` in every arm and the default, then a read: admitted.
#guard (blk [.caseStmt (id' "s") #[.mk #[.lit (LVec.ofNat 2 0)] (ba "t" (id' "a"))]
    (some (ba "t" (id' "b"))) false .none, ba "y" (id' "t")]).combAdmits wd4
-- … without the default: refused (the no-match path reads `t` unwritten,
-- and `t = a` follows).
#guard ((blk [.caseStmt (id' "s") #[.mk #[.lit (LVec.ofNat 2 0)] (ba "t" (id' "a"))] none false .none,
    ba "y" (id' "t"), ba "t" (id' "a")]).combViol wd4 [] []).isSome
-- the operand of a compound assignment (`y += t` is `y = y + t`): refused.
#guard ((blk [ba "y" (id' "a"), ba "y" (.binary .add (id' "y") (id' "t")), ba "t" (id' "b")]).combViol
    wd4 [] []).isSome
-- a pure function body is admitted.
#guard (blk [ba "y" (.binary .add (id' "a") (id' "b"))]).combAdmits wd4

end LeanModels.Sv
