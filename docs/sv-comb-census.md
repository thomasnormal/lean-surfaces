# `sv_comb`: obligation census of the two for-all-N reference proofs (2026-10-29)

> **Where the cited `svgolf/` paths live.** The svGolf proof-golf framework
> (`svgolf/`: the tasks, the checker, the reference proofs and the plain-Lean
> drafts this note cites) is not part of this branch; it lives on the
> `svgolf-prep` golf branch. Only the ls-sv infrastructure (`LeanModels/Sv/`,
> this note and the census) is merged here, so the `svgolf/...` paths below
> name files on that branch.

Step 3 of the plan in `docs/sv-comb-design.md`. Source: the structural half
of `svgolf/tasks/add/reference/add_n.lean` (lines 66 to 582, read in full)
and a scan of `svgolf/tasks/mul/reference/mul_n.lean` (structural half,
lines 158 to 1528). The question: of the lines that are not the circuit's
mathematics, which are mechanical derivation, which are genuine arithmetic
obligations, and which exist only because of today's representation?

## 1. The adder, line by line

| lines | what | kind | tactic's fate |
|---|---|---|---|
| 66 to 100 | the envelope's shape (`sumT`, `carryT`, `ripple_generates`, `ripple_static_source`), pinned by `rfl` | restates what the extractor produced | read from `design.pdesign` directly; never restated |
| 102 to 135 | instantiated vocabulary (`cinProc`, `sumProc i`, `carryProc i`, `rippleProcs N`, `rippleDecls N`) | instantiation of the templates at a symbolic genvar | computed (`sv2_inst_simp`); this is the family schema |
| 137 to 225 | the stages of `instantiate2` at symbolic `N` (environment, raw widths `\|N-1\|+1`, element widths, generate expansion, assembly) | mechanical, no choices | computed; internal |
| 227 to 262 | process list, membership characterization, length, declarations | derived facts about the above | computed |
| 264 to 351 | one-driver rule: driver windows of the list, pairwise disjointness | bookkeeping plus **arithmetic** | windows computed; disjointness is the first group of real goals (below) |
| 353 to 437 | the process table by index (`getElem?_flatMap_pair`, `ripple_proc`, ...) | exists only because later facts are indexed by **position in the flattened list** | disappears with site identities (design principle 13); membership characterization suffices |
| 439 to 503 | declarations, windows, driven signals | derived by cases over the four process forms | computed |
| 505 to 561 | the `CombDesign` fields (`nodup`, `assign`, `inWidth`, `notInput`, `disjoint`, `selfDisjoint`, `rhsFree`, `rhsDeclared`, `initWidth`) | case analysis over the four forms, `simp`, plus **arithmetic** | structural parts computed; arithmetic parts are goals |
| 563 to 581 | rank by position and the acyclicity proof | the player's certificate plus **arithmetic** | rank supplied by the player over sites; decrease is a goal |

About 520 lines in total. The mathematics is not in there at all.

### The genuine arithmetic obligations (adder)

After removing the derivation, what is left is about a dozen one-line goals,
all linear and all closed by `omega` today:

1. **Driver windows are pairwise disjoint.** For `i, i' < N`: `s[i]` against
   `s[i']`, `c[i+1]` against `c[i'+1]` (both `i ≠ i' → …`), `c[0]` against
   `c[i+1]` (`0 ≠ i + 1`). Other pairs differ by signal name.
2. **Windows lie in range.** `c[i+1]` in a width-`N+1` vector (`i + 1 + 1 ≤
   N + 1`), `s[i]` in width `N` (`i + 1 ≤ N`), `c[N]` read in width `N+1`.
3. **The rank decreases along every read.** Bit `i` reads `c[i]`, written
   by the carry-in (`i = 0`) or by bit `i-1`'s carry cell; the carry-out
   reads `c[N]`, written by bit `N-1`'s carry cell. With the rank
   `carry-in ↦ 0`, `bit i ↦ i + 1`, `carry-out ↦ N + 1`, each is `i < i + 1`
   or `N < N + 1`.
4. **Positivity of `N`** where a width `N` must be non-empty (`1 ≤ N`).

Everything else is "which of the four process forms is this", which the
tactic knows.

## 2. The multiplier: what is different

The structural half is about 1370 lines (76% of the file). The same
categories apply; the differences are exactly the 2-D arrays:

* **Geometry facts in the environment** (`MulEnvOk`, `ppGeom N`,
  `rectGeom N`): `pp` and `t` are `[N-1:0][N-1:0]` (row stride `N`), `s`
  and `c` are `[N-1:0][N:0]` (row stride `N+1`). The tactic derives these
  from the declarations once.
* **Row-major windows** (`win_sq`, `win_rect`): `x[i][j]` is flat bit
  `i * N + j` (or `i * (N+1) + j`). The lemma is proved once; each template
  then needs only `i < N`, `j < N` (or `j ≤ N`). These two lemmas belong in
  the shared library, not in each proof.
* **Row-major disjointness** (the one-driver rule, about 200 lines):
  `i * N + j ≠ i' * N + j'` for `(i, j) ≠ (i', j')` with `j, j' < N`. This
  is the nonlinear obligation, and it is the same fact for `pp`, `t`,
  `s` and `c`. One library lemma
  (`rowMajor_inj : j < W → j' < W → i * W + j = i' * W + j' → i = i' ∧ j = j'`)
  serves all of them.
* **The rank is defined on the flat index** (`mulRank N k`) with division
  and remainder by `N` (`Nat.add_mul_div_right`, `Nat.div_le_div_right`
  appear in the acyclicity proof). With site identities the rank is a
  lexicographic pair `(i, j)` and no division appears. This is the main
  simplification the design predicts.
* **Template instantiation at in-range genvars** (about 100 lines): each of
  the nine templates (`pp`, the row-0 assigns, the row-`i` assigns, the
  outputs) is instantiated once. Mechanical.
* **Nonlinear arithmetic that is not structural** (the `grind` calls near
  line 1760) belongs to the settled-state proof, i.e. the player's part.

## 3. What this fixes for the design

1. **The footprint rules v0 needs** are few: single bits `x[i]`, `x[i+1]`,
   `x[N]` (adder); 1-D slices with offset (`p[N+j]` from `s[N-1][j+1]`,
   multiplier output); 2-D bits `x[i][j]` and `x[i-1][j+1]` over the two row
   strides; whole-row fills (`c[0] = '0`). Prefix adders will additionally
   need `i - (1 << k)`; that is outside v0 and becomes an explicit goal.
2. **The rank constructors v0 needs**: `rippleRank` (one index) and
   `lexRank` (two). Both are over site identities, not positions.
3. **The library lemmas v0 needs**: `win_sq`/`win_rect` generalized to a
   row stride `W`, and `rowMajor_inj`. Neither mentions an SV design.
4. **A measurable target.** Of the adder's roughly 520 structural lines, the
   player keeps about a dozen one-line arithmetic goals plus the rank
   definition; of the multiplier's roughly 1370, the row-major disjointness
   goal (once) plus the rank definition. Everything else is derivation.
5. **The position-indexed process table is the largest piece that exists
   only for historical reasons** (about 85 lines for the adder). Site
   identities remove it; this is a bonus of principle 13, not an extra cost.

## 4. Not covered by this census

The settled-state half (`ripple_settled`, the `eval_*` gate lemmas,
knownness) is the producer side of the netlist view; it is censused with
step 7 (`sv_known`, `sv_bitvec`). Module instances (`ripple_fa`),
`always_comb` bodies and the sequential tier were not read.
