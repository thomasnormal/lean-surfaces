# `sv_comb`: design note and plan (2026-10-29)

> **Where the cited `svgolf/` paths live.** The svGolf proof-golf framework
> (`svgolf/`: the tasks, the checker, the reference proofs and the plain-Lean
> drafts this note cites) is not part of this branch; it lives on the
> `svgolf-prep` golf branch. Only the ls-sv infrastructure (`LeanModels/Sv/`,
> this note and the census) is merged here, so the `svgolf/...` paths below
> name files on that branch.

Status: design, not built. This note records the result of the 10/29
discussion between Thomas and the svGolf lane about proof automation for
parametric combinational ls-sv designs, and the plan for the first day of
building it. The tactic is general ls-sv proof infrastructure, so it lives
in `LeanModels/Sv/`. svGolf uses it as an outside user would.

## 1. The problem, measured

The two for-all-N reference proofs, `svgolf/tasks/add/reference/add_n.lean`
(770 lines) and `svgolf/tasks/mul/reference/mul_n.lean` (1800 lines), spend
most of their lines on bookkeeping about the design, before any arithmetic:

| | structure: process table, one-driver rule, `CombDesign`, `Acyclic` | the rest: settled state, gate algebra, arithmetic, statement |
|---|---|---|
| `add_n.lean` | about 520 lines (68%) | about 250 |
| `mul_n.lean` | about 1370 lines (76%) | about 430 |

Only the bit-level induction (the carry chain, the row invariant) is real
mathematics. A player should spend their effort there.

## 2. What the ideal proof looks like

We drafted the proof first and chose the tactic second. After the tactic
has done its work, the goal is plain Lean about bits. For `add_n.sv` the
signals are Lean values and the hypotheses are the SV `assign`s transcribed
one to one:

```lean
theorem ideal_add {N : Nat} (hN : 1 ≤ N) (a b : BitVec N) (cin : Bool)
    (c : Nat → Bool) (s : BitVec N) (cout : Bool)
    (hc0 : c 0 = cin)
    (hc : ∀ i < N, c (i + 1) =
        ((a.getLsbD i && b.getLsbD i) || (c i && (a.getLsbD i ^^ b.getLsbD i))))
    (hs : ∀ i < N, s.getLsbD i = (a.getLsbD i ^^ b.getLsbD i ^^ c i))
    (hco : cout = c N) :
    s = BitVec.ofNat N (a.toNat + b.toNat + cin.toNat) ∧
    BitVec.ofBool cout = BitVec.ofNat 1 ((a.toNat + b.toNat + cin.toNat) / 2 ^ N)
```

The proof of this is 53 lines of ordinary Lean (induction for the carry,
`BitVec.carry` lemmas, one `decide` for the carry gate). It is checked:
`svgolf/design/ideal_add.lean` compiles with the plain toolchain and no
ls-sv imports. Compare about 250 non-structural lines today.

**What this draft tests, and what it does not.** It is the consumer half
only: it assumes the four equations. It does not test `sv_comb`. The real
acceptance test composes the two halves: the equations must be obtained from
the actual `add_n.sem N` through `sv_structure` and `sv_equations`, and then
fed to the arithmetic proof. A hand-supplied set of equations would let the
structural part be bypassed. Likewise, a precise contract for the producer
is needed, and it is a named object (principle 12): `AddNetlistView` in
`svgolf/design/ideal_add.lean`, whose four fields are the four hypotheses
above (the consumer `ideal_add_view` takes it), stated over the settled
state.

Consequence: the proof layer does not need to be clever, it needs to be a
faithful translator from `design.sem N` to this view. Sparkle gets the view
for free because a Sparkle circuit already is a Lean function; ls-sv has to
earn it.

The multiplier's version of this view has 2-D arrays (`pp i j`, `s i j`,
`c i j`) and its proof is a row induction on top of a reusable ripple-row
lemma (a row of full adders computes a sum). That lemma is also what the
adder's proof is made of, so it belongs in a shared library of gate-level
lemmas. Drafting the multiplier is part of today's plan.

## 2b. The multiplier draft, and what it taught us

`svgolf/design/ideal_mul.lean` (198 lines, plain Lean, axioms
`propext`, `Classical.choice`, `Quot.sound`) proves `mul_n.sv` correct from
its transcribed `assign`s: 2-D signals are bit functions `Nat → Nat → Bool`
(row, column), with 13 hypotheses that are the SV's assigns one to one.
About 90 lines are a reusable gate-level library, about 105 are the
player's proof (the row invariant). Compare about 430 non-structural lines
in `mul_n.lean` today.

The library is built on one definition, `bfVal f n = Σ_{j<n} 2^j · f j`,
the value of a bit function. Its core is the **ripple-row lemma**: if
`t = x ^^ y`, `s = t ^^ c` and `c (j+1) = (x j && y j) || (c j && t j)` for
`j < N`, then `val s + 2^N · c N = val x + val y + c 0`. The multiplier's
row step is one application of it; the invariant is
`low output bits + 2^i · row i = a · (b mod 2^(i+1))`.

Considerations this raised, most of them new:

1. **Build the library on bit functions, not `BitVec`.** `bfVal` over
   functions avoids dependent-width rewrites (`BitVec (2*N)` made `rw` fail
   with a motive error) and makes shift and split lemmas one-line
   inductions. The adder would likely get shorter too (the ripple-row lemma
   replaces the `BitVec.carry` detour and the `xor_assoc` step), which is to
   be confirmed. Proposal: all internal signals are bit functions, `BitVec`
   appears only at the ports, and a bridge lemma
   (`bfVal x.getLsbD w = v → v < 2^w → x = BitVec.ofNat w v`) closes the
   statement. This also settles open question 1.
2. **The tactic must hide row-major flattening.** In ls-sv the 2-D arrays
   are flat vectors (`s` has rows of `N+1` bits, `pp` rows of `N`), so
   `s i j` is bit `i*(N+1) + j` of the state. The view must define `s i j`
   once, as a flat read, and keep it opaque; the player must never see the
   product. That is where the row-major lemmas are used, inside the tactic.
3. **Generate-loop domains become hypotheses.** `for (i = 1; i < N; i++)`
   gives `1 ≤ i → i < N → …`, and `s[i-1]` is then a natural subtraction
   with a guard. The view has to carry the loop bounds from `PDesign`.
4. **Vector assigns split into pointwise equations.** `assign s[0] =
   {1'b0, pp[0]}` becomes two kinds of equation (`j < N` and `j = N`),
   `assign c[0] = '0` a fill over `j ≤ N`, and `assign p[2*N-1:N] =
   s[N-1][N:1]` an offset equation `p (N + j) = s (N-1) (j+1)`. So the
   footprint rules need offsets and concatenation sources, not only
   point windows.
5. **Nonlinear identities need `grind`, not `omega`.** Three steps
   (the shift lemma, the row invariant step, the final assembly) involve
   products of variables; `omega` cannot, `grind` can once the powers are
   generalized. So the policy on permitted tactics must allow `grind`
   (its proofs are kernel-checked; axioms stay standard).
6. **Unused equations are still produced.** Row 0's `c` and `t` equations
   are never used. The view should not prune them: it transcribes the
   design, and the player decides what matters.
7. **`1 ≤ N` is genuinely needed here** (row `N-1` must exist), unlike in
   the adder's arithmetic lemmas.
8. **Knownness is still not shown.** Both drafts assume all signals are
   known Booleans. The knownness theorem remains a separate step of the
   tactic (principle 5).

## 3. Design principles (decided)

1. **Obligations are visible; the tactic does not discharge the player's
   mathematics.** Three categories, after an external review (10/29):
   * *The tactic does these internally*: unfolding and normalizing `PDesign`
     and `Gen2`, building the family schemas, definitional equalities,
     applying generic library lemmas, exposing the equation view, assembling
     `CombDesign` from its components.
   * *It leaves these as explicit goals*: rank-decrease side conditions,
     footprint disjointness, coverage of generated ranges, row-major
     injectivity, user-supplied module-summary premises, knownness premises
     not covered by registered gate summaries. Stated compactly (for
     example `∀ i j, i < N → j < N → …`), never as process nodes and `List`
     membership facts. The player closes them with `omega`, `grind`,
     `decide +kernel` or by hand; `omega` is not a decision procedure (its
     docstring says so), so nothing's soundness depends on it.
   * *It rejects these*: dynamic writes without a summary, arbitrary
     procedural control flow, constructs whose reads or writes cannot be
     extracted, equations whose widths cannot be determined.
2. **What the tactic computes** is what the design determines, with no
   choices: the normalized `Gen2` generator and its family-level
   declarations, footprints, dependency schemas and equation schemas. It
   never expands a symbolic generator into an `N`-length process list. (What
   `Gen2` states today is a closed-form list term over `N`, a `flatMap` over
   the index range, not an enumeration. The tactic works with that form.)
3. **Stages are separately callable.** Internal stages, in order:
   `sv_structure` (families, declarations, driver coverage and uniqueness,
   dependency graph, acyclicity); `sv_equations` (equations over the actual
   signal domain, `LVec`); `sv_known` (knownness of the relevant settled
   signals under explicit assumptions); `sv_bitvec` (conversion of the known
   `LVec` equations into `BitVec`/`Bool` equations). `sv_comb` chains all
   four; the player may call any of them. An `sv_comb?` hint mode prints
   the families, footprints, site identities and the required rank relation.
4. **Rank is a certificate, not a number.** A rank hint is a well-founded
   relation plus a proof that every read-to-write edge decreases it.
   Constructors ship with it: `rippleRank`, and `lexRank` for two
   dimensions. A lexicographic rank on `(i, j)` removes the nonlinear
   `i*N + j` from the acyclicity argument, which is the worst arithmetic in
   the multiplier's structural part.
5. **Four-state values are never silently erased, and structure does not
   imply knownness.** `LVec` values can be x or z, and acyclic logic fed by
   an unknown input still produces unknown outputs. Knownness needs its own
   premises: all external inputs known, all constants known, every gate
   operation preserving knownness, the process semantics propagating x and z
   as expected, and the settled-state theorem being total over every
   declared net. The rank proof is one premise among these. The equations
   from `sv_equations` are over `LVec`; only `sv_bitvec`, after `sv_known`,
   produces `BitVec`/`Bool` equations. The drafts in section 2 and 2b are the
   output of `sv_bitvec`.
6. **Build on what exists, with a derived summary.** The template language
   (`PDesign`, generate items) and the expansion lemmas in `Gen2` already
   exist; no fourth design representation. A small transient summary derived
   from `PDesign` (per family: reads, writes, source location, equation
   schema) is allowed, because without one the tactic would keep
   inspecting raw terms. It must come with a soundness theorem against
   `instantiate2`, of the shape
   `summary p = s → FootprintOf (instantiate2 p) = s.footprint`. That
   theorem is likely the most important piece of the first implementation.
7. **Recognized designs with unproved footprint facts become goals;
   constructs whose reads and writes cannot be extracted are rejected.**
   The tactic can only hand the player a useful goal for something it has
   extracted. If a family writes `i - (1 << k)`, the tactic identifies the
   window and leaves its disjointness as an explicit goal. If it cannot
   determine the writes or reads at all (a write `state[idx] := rhs` with an
   arbitrary runtime `idx`), there is no generic structural theorem to
   apply: it fails with a source-located message, or the player supplies a
   manual summary. Real submissions will write `i - (1 << k)`, strided
   carries and flat `i*N + j` windows, so the first category must be
   generous.
8. **Failure messages name the mathematical content that is missing:**
   unsupported construct, failed certificate (overlap, coverage), or missing
   rank hint.
9. **Plain tactic first, reflection later.** The first version unfolds and
   applies stable library lemmas, generating named goals. That shows which
   obligations really occur. A verified checker for the finite structural
   bookkeeping can come later as an optional accelerator; the plain mode
   stays available so a failing proof always shows its goals.

10. **The netlist view preserves the design's own expressions.** The
    equations keep the gate structure of the SV (`(a && b) || (c && (a ^^ b))`,
    with `^` left-associated as in the source). Normalizing to library forms
    (`BitVec.carry_succ`, `Bool.atLeastTwo`) is a separate, named bridge
    lemma (for example `fullAdderCarry_eq_atLeastTwo`) or an opt-in option,
    never the default, so that the player sees the circuit they wrote.
11. **Index convention for v0: `Nat` indices with explicit bounds.** The
    standard BitVec lemmas (`getLsbD_add_add_bool`, `carry_succ`) take `Nat`
    indices and `< N` hypotheses, so the view matches them. `Fin`-indexed
    equations (`Fin N` for sum bits, `Fin (N+1)` for carries) would read
    better but need typed wrapper lemmas; revisit once the wrappers exist.
    The one canonical shape is `i + 1`, never `Nat.succ i`.

12. **The producer contract is a named object.** The consumer half
    (`ideal_add_view`, `ideal_mul_view`) takes one structure, not a bundle of
    hypotheses: `AddNetlistView` and `MulNetlistView` in the drafts, one field
    per group of `assign`s. This stops producer and consumer drifting apart,
    gives diagnostics field names (`carry_step`, `sum_bit`), and lets the
    acceptance test check that the actual `add_n.sem N` inhabits the exact
    contract. Named views are the library-facing interface (what a reusable
    theorem such as the ripple-adder spec consumes). For an arbitrary
    contestant design `sv_equations` generates the equations in the shape of
    that design, and the player shows they imply the library's view, usually
    by `exact ⟨…⟩`. Contestants are not required to write views.
13. **Rank sites have stable identities.** A rank certificate needs a domain
    users can refer to, and it cannot be a position in an unexpanded list.
    Sites are `plain (id)` or `family (id) (indices)`, where a family id is
    the generate block's label plus the position of the assign inside it
    (`g_bit`, assign 0) and `indices` are the loop variables. Diagnostics
    print the same names. A ripple rank is then `family _ [i] ↦ i`, and a
    2-D one `family _ [i, j] ↦ (i, j)` under a lexicographic relation. (The
    present proofs rank by position `j` in the flattened process table,
    which this replaces.)

14. **Knownness is a one-time theorem about an x-free fragment, not a
    per-design step.** The static checks already guarantee that no x source
    exists (the `fourstate` stage: no x literals, no unknown constants, no
    out-of-range reads, no undriven nets or latches, no division by zero).
    For designs in that fragment, with known inputs, every settled signal is
    known by induction along the rank. Prove that once, for the operator
    forms of `Expr2`, and `sv_known` becomes an application of it plus the
    static check. (Suggested by the Sparkle comparison, section 5: a
    two-state HDL has no knownness obligation because it has no x.)
15. **The backend's expected shape is part of the contract.** Fixed-size
    subgoals closed by `bv_decide` fail on user-defined helpers (row-major
    flattening, dynamic extraction, custom cells), which it abstracts into
    opaque variables. So the netlist view must come with a normalization set
    (bridge lemmas for `getLsbD`, concatenation, the carry recurrence,
    `i * W + j` extraction), and `sv_comb?` prints the equation shape and
    the bridge lemmas needed before `omega`, `grind` or `bv_decide` apply.
    The fdiv16 certificate bridge will hit this first.

## 4. Sharing across the lane family

The repo's doctrine (`docs/family-architecture.md` §3.4, §3.8) is a thin
shared substrate: one outcome monad, one `mvcgen` over a `WPMonad`
instance (about 120 lines per new language, per its pilot), and per-language
semantics and congruences. That substrate is for interpreters, meaning
programs that run over a world with fuel. The combinational part of ls-sv
is a judgment, a fixed-point settle over a process table, and is closer to
the Lean-kernel lane that the doc calls a non-fit. So the static
combinational judgment does not need to depend on `Std.WP`, `mvcgen` or
`vcgen`. If the sequential SV interpreter later exposes a command language
with a weakest-precondition interpretation, it may use `vcgen`
independently. Version note: this repository pins Lean `v4.33.0-rc1`, where
`mvcgen` is the documented tactic and `vcgen` is labelled an experimental
drop-in. A newer upstream Lean is said to make `vcgen` the successor
(supporting deeply embedded command languages through `Std.WP.WP`); that
was not verified here, and the conclusion above does not depend on it.

What is language-neutral is the arithmetic underneath: disjointness of index
windows, row-major injectivity, lexicographic ranks. The same problem shows
up wherever a loop writes `a[i]` or `a[i*N + j]` for symbolic N. Plan:
write those lemmas as their own module with no `LeanModels.Sv` imports, so
promoting them to `Core` is a file move once a second consumer appears (the
doc's own trigger and "consolidation by touch" rules). No language-generic
tactic up front.

## 5. Prior art, and its licences

* **Lean's `mvcgen` / `vcgen`.** Source of the structure we borrow: a
  registry of spec lemmas, user-supplied invariants, a hint mode, an
  optional discharge step. `vcgen` is labelled experimental on our toolchain
  (v4.33.0-rc1); we do not depend on `Std.Do`.
* **Sparkle** (Verilean, Apache 2.0). An HDL embedded in Lean. No tactics of
  note (one `bv_decide` macro); its proofs are easy because circuits are Lean
  functions. Possible later use: a differential oracle and an alternative
  authoring route for contestants.
* **Ember** (Verilean). Proof macros for a TCP stack built on custom
  simp-attribute registries (`tcp_sym`, `wp_simp`, `pres`). It has no
  licence file, so it was read and not copied; the pattern is already in
  this repo (`py_simp`).
* **External review of the adder draft** (a model's review, 10/29). Kept:
  the producer/consumer distinction, the three-level library factoring,
  canonical expression shapes, `Fin` indices as a later option. Not kept: a
  new envelope type (principle 6) and any reflected decision procedure as
  the default (principle 9).
* **Sparkle port experiment** (a model's, 10/29, not re-run here). Fixed
  width 8 adder and a 4x4 grid proved by `decide` / `native_decide`; its
  `#verify_eq` macro and plain `bv_decide` failed on the structural cone.
  Taken from it: principles 14 and 15, and a finite-width sanity layer for
  the hand-written views (evaluate `run2` at N = 1, 2, 4, 8 and check the
  view's equations on the settled state, to catch transcription errors in a
  contract before it is proved). Not taken: its proofs as evidence about
  symbolic N (they are fixed-width, and `native_decide` is banned here).
* **Aristotle** output carries a restrictive use notice and is deliberately
  not used as a source of methods.

## 6. Open design questions

1. **How are signals presented in the netlist view?** Proposed after the
   multiplier draft (section 2b, item 1): bit functions for all internal
   signals (`Nat → Bool`, `Nat → Nat → Bool`), `Nat` indices with bounds
   (principle 11), `BitVec` only at the ports, bridged by a library lemma.
   One-bit ports appear as `Bool`; both forms are offered. CONFIRMED by
   re-deriving the adder in this style (`svgolf/design/ideal_add_lib.lean`):
   the player's proof shrinks from 53 lines to about 13 (`add_value` 6
   lines via the ripple-row lemma, `add_spec` 7 lines via `sum_split`), with
   no `BitVec.carry`, no `xor_assoc` and no `1 ≤ N` hypothesis.
2. **Library factoring (decided, three levels).**
   * *General BitVec arithmetic*, no SV content: `add_add_bool_eq_ofNat`,
     `ofBool_carry_eq_quotient` (the current `sum_eq_ofNat` and
     `carry_eq_ofNat` under better names), the bound estimate on the sum.
     These are width-generic; both hold at `N = 0` (checked), so the
     `1 ≤ N` hypothesis in the draft is an artifact of its proof, not
     needed by the lemmas. The task's own range `1 ≤ N` stays a property of
     the task statement, and ls-sv's range guard refuses collapsed ranges.
   * *Gate-level lemmas*: the ripple-adder theorem (`rippleAdder_spec`,
     which is what `ideal_add` implements), the full-adder identity, the
     ripple-row lemma shared with the multiplier. Circuit knowledge, not
     semantics, so they live under `svgolf/`.
   * *SV equation extraction*: `sv_equations` and its generated
     `add_n_equations`, in `LeanModels/Sv/`.
3. **Footprint language.** The v0 set is points, intervals, strides and
   row-major windows. What do prefix adders need beyond that?
4. **Hint syntax** for rank and for supplying missing footprint facts, for
   example `sv_structure (rank := …) footprints | write_disjoint … => by
   omega`. Site identities are decided (principle 13); the syntax can wait.

## 7. Plan (revised 10/29 after a second external review)

Constraint: rounds 3 to 5 of the ls-sv gaps and the svGolf restructure are
still being verified in the same tree, and they edit `LeanModels/Sv`
files. The work goes in new files only, and nothing is committed into
existing modules until those rounds land.

Order:

0. **Pin and record the environment**: Lean and Std versions, which of
   `mvcgen`/`vcgen` exists, the imports the prototype uses, the axioms of the
   baseline proofs. (Lean `v4.33.0-rc1`, drafts depend only on core.)
1. **Freeze the producer contracts** (DONE for the drafts:
   `AddNetlistView`, `MulNetlistView`). Still to fix: signal types, index
   conventions, boundary bits, `LVec` versus `BitVec`, orientation, the
   canonical `i + 1`. For the multiplier: whether rows range over `N` or
   `N + 1`, the final carry column, the diagonal output boundary, `N = 0` and
   `N = 1`, the row-major width, and the type of a partial product.
2. **Move generic lemmas out** (DONE, `svgolf/design/ideal_add_lib.lean`,
   plain Lean, 184 lines with the adder): `bfVal` and its lemmas
   (`bfVal_congr`, `bfVal_shift`, `bfVal_split`, `bfVal_and`, `bfVal_bv`),
   the full-adder identity, the ripple-row theorem, `rowMajor_inj` (the one
   nonlinear fact behind 2-D disjointness), `lexLt` with its well-foundedness
   proof, the bridges `sum_split` / `BitVec.eq_ofNat_of_val`, and the adder
   re-derived on it. Still to do: split into a Lake module under `svgolf/`
   (the draft files are standalone because plain `lean` cannot import
   siblings), and port the multiplier to import it.
3. **Obligation census** of `add_n.lean` and `mul_n.lean`: family shapes,
   write and read windows, coverage facts, rank sites, current `omega`
   failures, source locations, `LVec` versus `BitVec`, definitional versus
   arithmetic obligations.
4. **Normalized proof view**: the derived footprint and equation summary
   from `PDesign`/`Gen2`, with its soundness theorem against `instantiate2`.
   It never expands symbolic `N`.
5. **Prototype `sv_structure` on the adder**: normalize `Gen2`, produce
   stable site identities, construct declarations, apply the generic
   driver/acyclicity lemmas, leave only compact certificate goals.
6. **Prototype `sv_equations` on the adder**: produce the real
   `AddNetlistView` from `add_n.sem N`. The first full composition test:
   actual `add_n` → `sv_structure` → `sv_equations` → `AddNetlistView` →
   `ideal_add_view`.
7. **Knownness as a separately tested stage** (`sv_known`, `sv_bitvec`),
   never an implicit side effect of equation extraction.
8. **Multiplier producer**: use `MulNetlistView` to settle the 2-D footprint
   and rank-site API.
9. **Reflection last**: once the explicit-goal path gives the intended
   compact goals, reflect only the stable finite structural checks, keeping
   the same producer-contract and certificate API.

Realistic scope for 10/29: steps 0 to 3, and the start of 4. The tactic
prototypes (5 and 6) follow once the in-flight rounds have landed.

Not now: reflection, module instances, `always_comb` loops, the `Core`
promotion, anything touching existing `LeanModels/Sv` files.

### Status (10/29, end of day): stages 1 and 2 built

All of the following are in `LeanModels/Sv/` (not in the umbrella build; build
the examples by module name) and each lane was verified by an independent agent
that re-ran everything and found no blocker or major issue.

| Stage | Files | Result |
|---|---|---|
| `sv_structure` | `CombView{,Thm,Plain,Sound,Main,Diag,Tactic,Arith}.lean` | `CombDesign` and `Acyclic` for symbolic N. Adder: 2 tactic lines each. Array multiplier (nested loops, 2-D arrays, part-select and concat targets, lexicographic rank): 2 lines for `CombDesign`, 2 plus a 13-line rank key for `Acyclic`, against about 1370 by hand. `using hc` skips the one-driver goals only. The multiplier's `Acyclic` needs `maxHeartbeats 400000`. A FLAT netlist (every site plain, no parameter: the 113-gate `aes_sbox`) has its four obligations decided as closed statements about the site list (`CombViewPlain.lean`) instead of normalized: linear, 12 s at 113 sites, no goal left. |
| x-free knownness | `CombKnownBits.lean`, `CombKnownThm.lean` | Proved once: for a design in the x-free fragment (`Design2.XFree`), with every read driven (`Covered`) and known inputs, every driven bit is known and equals the Boolean evaluation of its right-hand side. Strong induction on the rank. Operators outside the fragment (width-mismatched operands, dynamic index, `/ % **`, signed forms, wildcard equality) are listed in the module docstring. |
| `sv_equations` | `CombEq{Base,Shape,Thm,Plain,Tactic}.lean`, `CombBridge.lean`, `CombCover.lean`, `CombLib.lean` | The netlist view: pointwise Boolean equations of every site with the SV gate shape preserved, plus the knownness of each site, from `CombDesign`, `Acyclic` and a settled state. With `sv_cover` for the coverage goals (a site as the witness is picked by name; a 2-D read is solved from its row and column equations, `CombCover.lean`, with an error that names the read and the conditions each writer would need) and `sv_bridge` (`CombBridge.lean`) for turning a printed equation into the Nat-indexed row-major fact (`SvState.cell`) a proof's arithmetic uses. For a flat netlist `auto`, `inRange`, `width`, `bitRead` and `cover` are decided too (`CombEqPlain.lean`): only the main goal and `inputsKnown` are returned. |

Acceptance (the plan's test): the equations come from the real `add_n.sem N` and
`mul_n.sem N`; nothing is typed in. Complete for-all-N correctness proofs:
`Examples/system-verilog/ripple_add/comb_proof.lean` (adder: 108 code lines, of
which the main theorem is 20 proof lines and the arithmetic bridge 72, against
537 by hand) and `Examples/system-verilog/mul_array/comb_proof.lean`
(multiplier: 197 code lines against 1380 by hand). Tampered adders (wrong gate,
wrong carry direction, wrong offset: `ripple_add/neg/`) are accepted by the
tactics but their correctness proofs fail, so the producer is not vacuous.
Standard axioms only, pinned by `#guard_msgs`.

Honest limits: (1) a one-time library of about 6000 lines; (2) the multiplier's
six nested 2-D coverage goals are closed by hand (about 65 lines), because
`sv_cover`'s witness search does not reach them; (3) the knownness side has no
separate `sv_known` or `sv_bitvec` tactic (it is delivered inside
`sv_equations` and the player applies the port bridge); (4) several fragment
refusals are not source-located (they report a `decide` failure); (5) some
obligations are closed internally by `intros; omega` or `try simp` (visible as
tagged goals only when they fail); (6) module instances, `always_comb` bodies
and edge-triggered processes are out of scope; (7) the `1 ≤ N` range and the
Int/`toNat` presentation are still visible to the player.

### Earlier status (10/29 evening, adder prototype)

Steps 0 to 5 are done for the adder shape. `sv_structure` (files
`LeanModels/Sv/CombView{,Thm,Sound,Main,Diag,Tactic,Example}.lean`, about
2700 lines, one-time library) proves `CombDesign` and `Acyclic` of
`ripple_add.sem N` for every `N ≥ 1` in 13 proof lines, against 518 raw
(359 kernel) lines by hand. It leaves exactly the intended goals (in-range,
two one-driver goals, two rank-decrease goals), each closed by
`intros; omega`. Axioms: standard three, pinned by `#guard_msgs`. Four
negative tests (overlapping writers, an out-of-range carry, a rank that does
not decrease, a dynamic write) fail with specific messages. Elaboration is
about 6.5 s (not faster than by hand in absolute time, but independent of
`N`). Fragment: flat top, scalar or 1-D affine declarations, `& | ^` over
identifiers, selects and literals, at most one non-nested `generate for`.
Not done: `sv_equations`, `sv_known`, `sv_bitvec`; nested or several
generate loops, 2-D arrays, part-select and concat targets (so the
multiplier is untested), `always_comb`, instances; `lexRank` is proved but
not exercised end to end.

Open questions the prototype raised, with the lead's recommendations:
`sv_structure using hc` to skip the in-range and one-driver goals when a
`CombDesign` is already in hand (yes, about 10 lines); soundness stated as
"reads included in the promised reads" (accepted for the structural stage,
since a larger read set only makes the rank obligation stronger; equality is
needed by `sv_equations`); `Int` indices with `.toNat` visible (acceptable
for v0, prefer a `Nat` presentation once stable); move
`CombViewExample.lean` into `Examples/` because it imports an Examples module
(yes, before any umbrella integration); site ids as module position plus
block label and position in the block (matches principle 13, with slang's
`genblk` name for unlabeled blocks).

## 8. Acceptance for the whole effort

All of these must hold:

1. The equations come from the actual `add_n.sem N` and `mul_n.sem N`.
2. No hand-supplied equation theorem bypasses the producer.
3. The structural proof does not expand symbolic `N`; its cost is
   independent of the size of `N`.
4. The remaining goals are exactly the intended rank, footprint, knownness
   or arithmetic obligations.
5. The final player proof contains the carry induction or the row induction.
6. Only `propext`, `Classical.choice`, `Quot.sound`. A test harness rejects
   `bv_decide` and `native_decide` or reports them separately.
7. The proof scales: proof lines, elaboration time, `.olean` size, kernel
   time are measured and do not grow with `N`.

Negative tests, each with an asserted outcome (accepted, accepted with a
user goal, rejected as unsupported, rejected with a structural
counterexample): overlapping writers, missing output coverage, a rank cycle,
the wrong carry direction, the wrong slice width, a dynamic indexed write, an
unknown (x) input, a zero-width range, a one-width range, row-major aliasing.
The x-input test in particular: `sv_structure` and `sv_equations` succeed
over `LVec`, and `sv_bitvec` fails unless an input-knownness premise is
supplied. That prevents accidental two-state coercions.

Update to section 5, external reviews: the second review (10/29) was kept
almost entirely. Pushed back on, and now stated above: named views are the
library interface and not something contestants must write (principle 12),
and the four stages are internal steps behind `sv_comb`.
