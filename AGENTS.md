# AGENTS.md — operating manual for the proof AI

You are proving real Python programs correct in Lean 4 (`leanprover/lean4:v4.33.0-rc1`, core only, no packages).

## Orientation

1. A Python file's real AST is dumped to a JSON envelope (`extractors/python/extract.py`, CPython `ast` frontend).
2. `load_program f from "….json"` ingests it at elaboration time: `f : Module` is a **literal AST term** proofs can unfold.
3. A fuel-based definitional interpreter (`LeanModels/Python/Semantics.lean`) gives it meaning: `callFunction m f args fuel : Res Val` with `ok / exn / timeout / unsupported`.
4. Theorems live in `# lean[ … # ]` comment blocks inside the `.py` file, spliced verbatim into a generated companion `Examples/<Name>.lean`.
5. Statements use the typed surface (`LeanModels/Python/Surface.lean`): they never mention `Val`, fuel, or the AST — [docs/spec-surface.md](docs/spec-surface.md) is normative for shapes.
6. Goal states print back in surface notation (`LeanModels/Python/Delab.lean`) — the goal state is your interface; below `unfold CallsTo`/`obtain`, fuel and `callFunction` are visible by design.
7. [docs/DESIGN.md](docs/DESIGN.md) is the authoritative semantics/format contract; the semantics is differentially tested against CPython (`harness/diff_test.py`).
8. A SystemVerilog lane (`LeanModels/Sv/**`, `harness/sv/**`, `Examples/sv/**`) is mid-integration: NOT imported by `lake build`; it has its own contract ([docs/sv-design-m0.md](docs/sv-design-m0.md)) and is checked with `lake env lean LeanModels/Sv/<File>.lean`. Leave it alone unless it is your task.
9. Your deliverable: proofs in `.py` lean-blocks that keep `lake build` green from the repo root.
10. Read the docstrings of [Surface.lean](LeanModels/Python/Surface.lean) and [LoopTactic.lean](LeanModels/Python/LoopTactic.lean) before proving anything nontrivial — they are the tactic reference; this file only indexes them.

## The workflow

```
1. edit Examples/python/<f>.py            # code on top, theorems in "# lean[ … # ]" blocks
2. python3 extractors/python/extract.py Examples/python/<f>.py
                                          # regenerates <f>.json + Examples/<PascalStem>.lean
3. lake build                             # from repo root; must end "Build completed successfully"
```

Before proving a new function's spec: add its concrete cases to `harness/cases.json` and run `python3 harness/diff_test.py` (must exit 0). The model is validated against CPython, not against your reading of the docs — this step has caught real spec bugs (see `Examples/python/gcd.py`).

Every example's first lean-block is `#py_check` non-vacuity runs. Write them before the theorems.

## Judgment vocabulary

| Surface | Elaborates to | Meaning |
|---|---|---|
| `f(a, b) ==> v` | `CallsTo m "f" #[toVal a, toVal b] (toVal v)`, i.e. `∃ fuel, callFunction … fuel = .ok (toVal v)` | total: terminates and returns `v` |
| `f(a) ⇓ r` | the same `CallsTo`, hypothesis position, binding `r` | relational specs; prints back as `==>` |
| `f(a) ~~> v` | `PartialTo`: `∀ fuel r, callFunction … fuel = r → r = .timeout ∨ r = .ok (toVal v)` | strengthened partial: every run times out or returns exactly `v` — no exception, no `unsupported`, no other value |
| `f(a) ==>! e` | `Raises`: `∃ fuel, callFunction … fuel = .exn e` | terminates raising `e` |
| `#py_check f(a) = v` / `#py_check f(a) raises e` | `#guard` of one concrete run at fixed fuel **4096** | non-vacuity check |
| raw ∀-fuel form: `(h : callFunction f "f" #[.int a] fuel = .ok r) : r = .int …` | itself | the canonical `@[spec]` shape (conditional simp lemma) |

Elaboration notes: the identifier is both the loaded module constant and the function name; dotted `arith.mod(7, 0)` splits into module `arith`, function `"mod"`. Preconditions are ordinary named hypotheses (`(hn : 0 ≤ n)`). Binders use `Py*` brands (`PyInt` ≡ `Int`). Marshalling is `ToVal` (`toVal_int`, `toVal_nat`, … are simp lemmas). The spec RHS is mathematical Lean: Python `//` is `Int.fdiv`, `%` is `Int.fmod` — never "prettify" to `/` without a sign hypothesis ([docs/spec-surface.md](docs/spec-surface.md) §2).

## GOAL-SHAPE → TACTIC

| Goal shape | Tactic |
|---|---|
| `CallsTo _ _ _ _` (`==>`/`⇓`) or `==>! _`, loop-free body — straight-line **or** branching | `py_prove [f]` |
| `CallsTo` goal, body has one `while` | `py_begin [f]`, then `py_loop` clauses (next row) |
| goal after `py_begin`: context has `hentry : ∀ F, callFunction … (F + 32) = …` containing a frozen `execWhile` | `py_loop (inv := fun (x y : Int) => …) (dec := fun (x y : Int) => …)`; binder names = the Python variable names; add `(state := […])` *before* `inv` when theorem binders shadow them |
| residual named-atom arithmetic (`hinv1…`, `hcont`, primed exit vars `i'`) | `omega` to pin values (`obtain rfl : i' = n + 1 := by omega`), then `grind`; pass library lemmas as needed (`grind [Int.gcd_zero_right, Int.natAbs_of_nonneg]`) |
| corollary of a total theorem: raw ∀-fuel `@[spec]` form, typed `⇓` form, `~~>` form, or value-rewritten `==>` | `py_corollary [tot]`; instantiate if needed (`py_corollary [fib_total n.toNat]`); extra value bridges after a comma (`py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]`) |
| recursive function | induction on the **math argument** (`Nat.strongRecOn`), base cases `py_prove`; step: `py_lift ⟨f₁, h₁⟩ := ih … with [f]` per IH, then `refine ⟨f₁ + f₂ + 32, ?_⟩`, `rw [callFunction.eq_2]`, `py_simp [f, facts…]`, `simp (disch := omega) only [h₁, h₂]` — see `Examples/python/fib.py` |
| loop provably never runs (guard false at entry) | constant-fuel witness: `exact CallsTo.intro 8 (by py_simp [callFunction, execWhile, f, h0])` — see `tri_neg_total` in `Examples/python/tri.py` |
| threshold obligation `∃ f₀, ∀ F, f₀ ≤ F → <straight-line run> = .ok v` (hand-rolled loop lemmas) | `py_threshold 32 [facts…]` |

The proof to imitate for loops (real file, checked by `lake build`):

```lean
-- Examples/python/tri.py (lean block; built as Examples/Tri.lean)
theorem tri_total (n : PyInt) (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2 := by
  py_begin [tri]
  py_loop (inv := fun (total i : Int) => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1))
          (dec := fun (total i : Int) => (n + 1 - i).toNat)
  · obtain rfl : i' = n + 1 := by omega
    grind
  all_goals grind
```

With shadowed binders (`gcd` mutates `a`, `b`; the invariant needs the *initial* values):

```lean
-- Examples/python/gcd.py (lean block; built as Examples/Gcd.lean)
theorem gcd_total (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : gcd(a, b) ==> Int.gcd a b := by
  py_begin [gcd]
  py_loop (state := [a, b])
          (inv := fun (x y : Int) => 0 ≤ x ∧ 0 ≤ y ∧ Int.gcd x y = Int.gcd a b)
          (dec := fun (x y : Int) => y.toNat)
  · grind [Int.gcd_zero_right, Int.natAbs_of_nonneg]
  · exact ⟨hinv2, Int.fmod_nonneg hinv1 hinv2, by rw [gcd_fmod_step hinv1 hinv2, hinv3]⟩
  · have := Int.fmod_lt_of_pos x (show (0:Int) < y by omega)
    have := Int.fmod_nonneg hinv1 hinv2
    omega
  · exact ⟨ha, hb, trivial⟩
```

Residual-goal order after `py_loop`: exit algebra, invariant preservation, measure decrease, initial invariant; any unclosed interpreter obligation is appended last, never dropped.

## Failure modes

All error strings below were reproduced on the current tree.

| Symptom | Cause | Fix |
|---|---|---|
| `omega could not prove the goal` although the needed hypothesis is right there, and a binder is `PyInt`-typed | `omega`'s atom matching is syntactic; a hypothesis stated over the `PyInt` brand and a goal atom over `Int` don't unify for it | work through `py_begin` — it restates every `Py*`-branded hypothesis at the unbranded type; in hand proofs, restate the hypothesis at `Int` yourself |
| `grind` fails on a goal whose invariant facts it should use | `grind`'s e-matching instantiates from **atomic** facts, not conjunctions | state the invariant as a top-level `∧`-chain — `py_loop` splits it into `hinv1`, `hinv2`, … for you; never re-conjoin them (no `⟨hinv1, hinv2⟩` repackaging before `grind`) |
| ``py_loop: no `hentry` hypothesis in context — run `py_begin [<prog>]` first`` | `py_loop` consumes the entry lemma `py_begin` produces | run `py_begin [f]` first |
| ``py_loop: loop variable `k` is not in the loop environment [n, s] — when the Python variable names are shadowed by ambient binders, name them with `(state := [...])` `` | `inv` binder names must *be* the Python variable names unless mapped | `py_loop (state := [s, n]) (inv := fun (s k : Int) => …) …` — `state` entries are matched **by name** (any order) against the loop environment; the i-th entry pairs with the i-th lambda binder, freeing binder names |
| `py_loop: could not derive the loop-test value / continuation condition / body's logical step` | test/body outside the v1 recipe (non-`Int` loop variables, `break`/`continue`/`return` in the body, two loops) — or a Miller pattern got destroyed: unification reads `tv`/`Cont`/`step` off goals containing metavariables, which surviving `ite`s, destructured states, and full-simp-set rewrites (e.g. moving `!` across `(b == 0) = !?Cont s`) all break | keep loops in the v1 shape ([LoopTactic.lean](LeanModels/Python/LoopTactic.lean) docstring); in hand-rolled obligations: keep the state variable whole (`intro s`, never destructure), collapse test branches with `ite_ok_bool`, and use `simp only [truthy]`, not `py_simp`, on the truthiness goal |
| ``py_begin: goal is not a `==>`/`⇓` (CallsTo) statement`` | `py_begin` only opens total-correctness goals | state the theorem with `==>`/`⇓`; get `~~>` and `@[spec]` forms afterwards via `py_corollary` |
| `py_prove` leaves a huge goal full of `execWhile` and AST literals | the body has a loop; `py_prove` is for loop-free bodies only | switch to `py_begin [f]` + `py_loop` |
| `#py_check` fails: ``Expression callFunction … 4096 == Res.ok … did not evaluate to `true` `` | wrong expected value — or recursion deeper than the fixed fuel 4096 (fuel is a *depth* bound) | fix the expectation; for deeper runs use a raw `#guard` with bigger fuel (concrete runs cost time proportional to steps, not fuel — generosity is free) |
| `warning: Left-hand side of simp theorem has a variable as head symbol …` on an `@[spec]` theorem | the raw ∀-fuel shape is a conditional simp lemma with variable head | prefix with `set_option warning.simp.varHead false in` (house style, every example file) |
| `simp` won't apply a threshold hypothesis `h : ∀ F, f₀ ≤ F → execWhile … = .ok p` | the loop lemma was applied at metavariable spans, so `simp` cannot index `h` | conditional `rw [h]` and discharge `f₀ ≤ F` by `omega` (`execWhile_at_least` docstring) |
| `simp only [prog] at h; py_simp at h` fails with "no progress" | two-step unfold/normalize breaks on hypotheses needing no cast normalization | fuse them: `py_simp [prog] at h` (what `py_lift` does) |
| a `first \| exact … (by …)` alternative "succeeds" then the proof is broken | `exact … (by …)` **commits** inside `first` even when the nested block fails (recovered with `sorry`, merely logged) | when writing tactics: put all-tactic attempts first, guarded by `done` (`py_prove` docstring) |
| `Env.lookup`/`Env.set` dot notation fails to resolve | `Env` is an abbrev of `List (String × Val)`; dot notation lands in the `List` namespace | use the full names |
| a fuel-arithmetic mess (`max f₁ f₂ + 3` offsets) | you are hand-counting interpreter steps | never do this: use threshold forms (`py_lift`, `CallsTo.at_least`, `execWhile_at_least`) + `simp (disch := omega) only [h]`, and generous slack constants (`⟨f₁ + f₂ + 32, ?_⟩` — any slack works) |

Statement discipline when re-proving: the statements in the example files and [docs/spec-surface.md](docs/spec-surface.md) are **normative — reproduce them exactly**. Do not add hypotheses to make a proof pass; a genuinely needed hypothesis is a *semantics finding* — take it through the differential harness first (that is how `gcd`'s sign hypotheses were justified). Do not delete a hypothesis that turns out unneeded on this toolchain; keep it and record the fact (see `midpoint_nonneg` in `Examples/python/midpoint.py`).

Why `~~>` is the only admissible partial-correctness form: the naive "if it returns `.ok` then `v`" is **vacuously provable for every `v`** whenever the callee raises or diverges — a reward-hackable objective for an AI prover. `PartialTo` is falsifiable: it is inconsistent with `==>!` and with `unsupported` (`PartialTo.not_raises`, `PartialTo.iff_obs`). Totality subsumes it (`CallsTo.partialTo`, via fuel monotonicity), so prove `==>` and get `~~>` free via `py_corollary`.

## House rules

- **Induction on math variables, never on fuel.** `fib_total` inducts on `k : Nat` with `Nat.strongRecOn`; fuel induction lives only inside the framework (`fuelMono`, Obs.lean).
- **Threshold form for every spliced run**: `py_lift` / `CallsTo.at_least` / `execWhile_at_least`, side conditions by `omega`. Generous slack constants everywhere: `py_prove` and `py_threshold` use 32, `#py_check` uses 4096, witnesses use `… + 32`.
- **Typed surface in statements**: `Py*` binders, mathematical RHS, no `Val`/fuel/AST. The raw ∀-fuel form appears only in `@[spec]` corollaries, proved by `py_corollary`.
- **`@[spec]` only on Hoare-triple/simp shapes** (the raw ∀-fuel form, the `⇓`-relational form). The ∃-fuel arrows (`==>`, `~~>`) are *not* `@[spec]` (recorded in `Examples/python/add.py`). `@[spec]` is core Lean's mvcgen attribute: there is no `simp [spec]` set — cite lemmas by name.
- **Non-vacuity first**: `#py_check` block before any theorem; `unsupported`-outcome checks stay raw `#guard … matches` (no surface form — deliberate).
- **`#print axioms` of every `@[spec]` theorem** must show only `[propext, Classical.choice, Quot.sound]`.
- **`py_simp` freezes recursion points**: `callFunction`/`execWhile` are not in its simp set; unfold one step with `rw [callFunction.eq_2]` / `rw [execWhile.eq_2]`, pass them explicitly only when full unfolding is safe. Program literals must be passed explicitly (`py_simp [tri]`).

## Never

- Never `sorry`, `admit`, or `native_decide` — anywhere, ever.
- Never edit generated files: `Examples/*.lean` companions (header says `AUTOGENERATED … DO NOT EDIT`) and `Examples/python/*.json` envelopes. Edit the `.py`, re-extract.
- Never weaken, strengthen, or "simplify" a recorded theorem statement to make a proof pass.
- Never add `"expect": "unsupported"` whitelist entries to `harness/cases.json` to silence a mismatch — whitelists document known tier gaps, nothing else. A non-whitelisted mismatch is an interpreter bug: report it, don't paper over it.
- Never state partial correctness as bare "if `.ok` then `v`" — use `~~>` (see above).
- Never leave `lake build` red, and never `git commit`.
- Never touch the SV lane's files (or `lakefile.toml` / `LeanModels.lean` / `lean-toolchain`) as a side effect of Python-lane work.
