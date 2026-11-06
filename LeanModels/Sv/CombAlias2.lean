import LeanModels.Sv.Hier2
import LeanModels.Sv.CombAliasCore

/-!
# The `always_comb` alias guard (`LeanModels.Sv` — WP4 round 6, lane B)

**Decided by Thomas, 2026-10-29: refuse an `always_comb` block that reads a
continuous copy of a variable it writes, loudly.** The self-read guard
(`CombGuard2.lean`) sees one process on its own result. It cannot see this
design:

```systemverilog
assign w = t;
always_comb begin y = w; t = a; end
```

The block reads `w` and writes `t` — different variables — yet `w` follows
`t` through a continuous assignment, so the block's own write of `t` changes
a signal the block read earlier in the same run. IEEE 1800-2023 §9.2.2.2.1
puts `w` in the block's implicit sensitivity list (it is read and not written
by the block), so the update of `w` must wake the block. Whether it does
depends on WHEN the simulator applies the update: §4.7 ("the simulator may
suspend execution and place the partially completed event as a pending event
in the event region") and §4.8 (its `assign p = q; … q = 0; $display(p);`
example: "the simulator is correct in displaying either a 1 or a 0") leave
both orders open. Xcelium 24.03 and Verilator 5.042 apply the update after
the block suspends at its event control, which re-runs the block (`y = a`);
Icarus 12.0 applies it SYNCHRONOUSLY inside the block's run, the block is
not waiting yet, the wake-up is lost, and `y` keeps the previous `w`
(`docs/sv-oracle-disagreements.md`, "Icarus propagates a copy inside the
block's own run"). The model's settle semantics gives Xcelium's answer. The
tools split, so the block is refused (policy: refuse where the tools split).

## The rule

A body is refused when, on some control path through it, a statement reads
a bit that is **downstream, through at least one continuous assignment, of a
bit the path writes at that statement or later**. "Continuous assignment"
means every `Process2.assign` of the flat design — after `Hier2.lean`'s
flattening these include the port connections, so a port loop (a child's
input and output port tied to one parent variable) exists only at this
level — and the check does not look at what the right-hand side computes:
`assign w = t`, `assign w = ~t`, `assign w = t[1:0]`, a chain of such
assigns and a port loop are all refused, not by the kind of functor the
simulator builds for them.

Not refused, because every tool agrees on them (measured, round 3 and 4):

* write-then-read, `assign w = t; always_comb begin t = a; y = w; end`: the
  read comes after the last write of its source on every path;
* a SEPARATE `always_comb` copy, `always_comb w = t;` beside the block: the
  copy is a process, not an `assign`, and is woken like any other process;
* a read of a copy of a variable the block does not write.

## The check

`fanOut fl A` is the set of windows reached from the windows `A` through
at least one hop of the design's continuous assignments `fl` (each
`(reads, writes)`, `Process2.aflow`): an assignment fires when one of its
read windows overlaps `A` or an already reached window, and then contributes
its write windows. The walk `Stmt2.aliasViol` is `Stmt2.combViol`
(`CombGuard2.lean`) with two changes: the written-after set `A` is replaced
by its fan-out before it is compared with the reads (`readsViol [] (fanOut …)`,
the self-read guard's own `readsViol` with an empty must-write set — a copy
is never written by the block, so "already written on every path" never
excuses a read of it), and the zero-hop case is left to the self-read guard
(`fanOut` contains only windows reached by an assignment). Reads (`Expr2.rdW`)
and may-writes (`Stmt2.mayW`) are the self-read guard's, so the bit
granularity is the same: constant slices are exact, run-time indices cover
their whole signal.

## Where it applies (BESIDE `name.sem`, like `RangeGuard2.lean`)

`Design2.aliasGuard` replaces each `Process2.alwaysComb` whose body the walk
refuses by `Process2.unsupported "AlwaysComb:alias-read" msg`; every other
process is untouched. The guard needs the whole flat design, so it runs on
the INSTANTIATED design: `load_design_sv2` (`Ingest2.lean`) at the defaults
and at every point of the probe sidecar, the differential runner
(`harness/sv/runner2.lean`) at each row's point, and
`PDesign.aliasReport` for any other tool. It is NOT part of `name.sem`:
the recorded lemmas `PDesign.instantiate2_eq`, `PDesign.assemble2_processes`,
`PDesign.instantiateG2_of_ok`, `PDesign.instantiateGD2_of_ok`,
`PDesign.instantiateGD2_eq_driverGuard`, `Design2.driverGuard_of_ok`,
`PDesign.instantiateH_of_rec` and the ∀-N proofs of `ripple_add`, `mul2d`,
`partsel`, `ripple_fa` (and `CombViewMain.lean`, which unfolds
`instantiateGD2`) are stated for the unguarded family, so a guard inside
`instantiate2`/`instantiateG2`/`instantiateGD2` would falsify them
(`RangeGuard2.lean` records the same constraint for the legacy-range guard).
A ∀-N proof that wants the guard gone uses
`Design2.aliasGuard_of_noComb` (a design without `always_comb` is its own
guard — `ripple_add`, `mul2d` and `ripple_fa` are continuous-only; `partsel`
has two `always_comb` blocks that read only the input `b` and write `w_hi` /
`w_lo`, which no `assign` reads, so the census finds it admitted at every row's
point but no ∀-N statement of that is recorded),
`Design2.aliasGuard_of_noAssign` (no continuous assignment: the proof API's
designs, `CombAlias2Example.lean`) or `Design2.aliasGuard_of_admits` (the
admission is decided by the walk, `decide`/`simp` at a closed or a symbolic
width).

A hierarchy is checked ONCE, on the flattened design: a child's signals
carry the instance prefix (`u.w`), and the message names the instance when
the violating signal is one of an instance's (`aliasMsg`).

## Justification (`CombAlias2Sound.lean`)

Proved there, and only that: the walk is sound for control paths — on EVERY
control path of an admitted body, no read of a bit is downstream (through
the design's continuous assignments, at bit granularity) of a bit the path
writes at or after the read (`Stmt2.aliasViol_epaths`, via
`Down.mem_fanOut`/`fanOut_closed`) — and the design-level facts the examples need
(identity on admitted designs, idempotence, no assigns ⇒ no violation). The
event-driven schedule equivalence (a simulator that applies the copy's
update inside the block's run reads the same value as one that defers it) is
NOT formalized: `Sem2.lean` has no intra-block propagation semantics to
prove it against, and the argument that the two schedules agree on an
admitted body is the measured mechanism in `docs/sv-oracle-disagreements.md`.
-/

namespace LeanModels.Sv

open CombGuard

/-! ## Parameter-point adapter -/

/-- **The alias guard at a parameter point** (`args`, the design already
brought to the point by `PDesign.atPoint`): the module (an instance-free one
through `instantiateG2`, a hierarchical one through `instantiateH`, as the
differential runner and `Probe2.instAtOverrides` instantiate it) under
`Design2.aliasReport`. An instantiation failure is not this guard's to
report (`none`: the semantic family is loud there already). -/
def PDesign.aliasReport (d : PDesign) (lib : List PDesign) (args : List Int) : Option String :=
  let F := PDesign.surfaceFuel args
  match (if lib.isEmpty || GenItem.listInstFree d.generates then d.instantiateG2 args F
          else d.instantiateH lib args F) with
  | .ok m => m.aliasReport
  | _ => none

/-! ## Pinned shapes (`#guard`; the SV twins are the `sem2/acg_alias_*`
fixtures of `harness/sv/cases2.json`) -/

section pins

private def dcl (n : String) (w : Nat) (i : Bool := false) (o : Bool := false) : Decl :=
  { name := n, width := w, isInput := i, isOutput := o }

private def ba (n : String) (e : Expr2) : Stmt2 := .blockingAssign (.ident n) e
private def id' (n : String) : Expr2 := .ident n
private def blk (ss : List Stmt2) : Stmt2 := .block ss.toArray

private def aliasDecls : Array Decl :=
  #[dcl "a" 2 (i := true), dcl "y" 2 (o := true), dcl "t" 2, dcl "w" 2, dcl "v" 2, dcl "z" 2]

private def mk (ps : List Process2) : Design2 :=
  { name := "pin", decls := aliasDecls, processes := ps.toArray }

private def mkW (w : Nat) (ps : List Process2) : Design2 :=
  { name := s!"pin_w{w}"
    decls := #[dcl "a" w true, dcl "y" w false true, dcl "t" w, dcl "w" w]
    processes := ps.toArray }

private def isAliasRefused : Process2 → Bool
  | .unsupported "AlwaysComb:alias-read" _ => true
  | _ => false

private def assignWT : Process2 := .assign (.ident "w") (id' "t")
private def assignVW : Process2 := .assign (.ident "v") (id' "w")

-- `assign w = t; always_comb begin y = w; t = a; end` (acg_alias_assign): refused, on all of `w`.
#guard ((mk [assignWT, .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasReport.isSome)
#guard isAliasRefused (mk [assignWT, .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasGuard.processes[1]!
#guard (mkW 2 [assignWT, .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasReport.isSome
#guard (mkW 7 [assignWT, .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasReport.isSome
-- write then read (admitted): `t = a; y = w;`
#guard (mk [assignWT, .alwaysComb (blk [ba "t" (id' "a"), ba "y" (id' "w")])]).aliasAdmits
-- the copy through a SEPARATE always_comb is not an `assign`: admitted.
#guard (mk [.alwaysComb (ba "w" (id' "t")),
    .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasAdmits
-- a chain `assign w = t; assign v = w; … y = v; t = a;`: refused (transitive).
#guard !(mk [assignWT, assignVW, .alwaysComb (blk [ba "y" (id' "v"), ba "t" (id' "a")])]).aliasAdmits
-- … and in the other order of the assigns.
#guard !(mk [assignVW, assignWT, .alwaysComb (blk [ba "y" (id' "v"), ba "t" (id' "a")])]).aliasAdmits
-- three hops in the scrambled order (the shape of `acg_alias_thru` after
-- flattening: t -> u.i -> u.o -> w, two port connections around the child's
-- own assign, here v, z standing for u.i, u.o): refused.
#guard !(mk [.assign (.ident "w") (id' "z"), .assign (.ident "v") (id' "t"),
    .assign (.ident "z") (id' "v"),
    .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasAdmits
-- … and the same chain with the write BEFORE the read: admitted.
#guard (mk [.assign (.ident "w") (id' "z"), .assign (.ident "v") (id' "t"),
    .assign (.ident "z") (id' "v"),
    .alwaysComb (blk [ba "t" (id' "a"), ba "y" (id' "w")])]).aliasAdmits
-- not by the functor: `assign w = ~t` is refused as well.
#guard !(mk [.assign (.ident "w") (.unary .bnot (id' "t")),
    .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasAdmits
-- a copy of something the block does not write: admitted.
#guard (mk [.assign (.ident "w") (id' "a"), .alwaysComb (blk [ba "y" (id' "w"), ba "t" (id' "a")])]).aliasAdmits
-- a read after the first write but before a LATER write of the source: refused.
#guard !(mk [assignWT,
    .alwaysComb (blk [ba "t" (id' "a"), ba "y" (id' "w"), ba "t" (id' "a")])]).aliasAdmits
-- a conditional write after the read: refused (some path).
#guard !(mk [assignWT, .alwaysComb (blk [ba "y" (id' "w"),
    .ifStmt (id' "a") (ba "t" (id' "a")) none])]).aliasAdmits
-- the read in a condition, the write in a branch: refused.
#guard !(mk [assignWT, .alwaysComb (.ifStmt (id' "w") (ba "t" (id' "a")) none)]).aliasAdmits
-- one statement reading the copy of its own target: `t = w` — a loop through the copy.
#guard !(mk [assignWT, .alwaysComb (ba "t" (id' "w"))]).aliasAdmits
-- bit precision: the copy of bit 0 read, bit 1 written later — admitted …
#guard (mk [.assign (.ident "w") (.slice (id' "t") 0 1),
    .alwaysComb (blk [ba "y" (id' "w"), .blockingAssign (.slice "t" 1 1) (id' "a")])]).aliasAdmits
-- … bit 0 written later — refused.
#guard !(mk [.assign (.ident "w") (.slice (id' "t") 0 1),
    .alwaysComb (blk [ba "y" (id' "w"), .blockingAssign (.slice "t" 0 1) (id' "a")])]).aliasAdmits
-- no assigns at all: nothing to refuse.
#guard (mk [.alwaysComb (blk [ba "y" (id' "t"), ba "t" (id' "a")])]).aliasAdmits
-- the self-read (zero hops) is the other guard's: here `y = t; t = a;` is not an alias read.
#guard (mk [.alwaysComb (blk [ba "t" (id' "a"), ba "y" (id' "t")])]).aliasAdmits

end pins

/-! ## Axiom pins

Standard axioms only; the `#guard_msgs` wrappers make the build fail if any of
these drifts (the rest of the file's theorems are pinned in
`CombAlias2Sound.lean` and `CombAlias2Example.lean`). -/

/--
info: 'LeanModels.Sv.Design2.aliasGuard_of_noComb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Design2.aliasGuard_of_noComb

/--
info: 'LeanModels.Sv.Design2.aliasGuard_of_admits' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Design2.aliasGuard_of_admits


end LeanModels.Sv
