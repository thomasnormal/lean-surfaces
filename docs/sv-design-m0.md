# SV lane — M0 design contract (scheduler-core vertical slice)

Authoritative interface contract for the first SystemVerilog implementation slice.
Components built against it must match it exactly; genuine contradictions are
resolved minimally and reported. Companion reading: `docs/sv-spec-surface.md` (+
part 2) for where this is going; `docs/DESIGN.md` for the Python-lane precedent.

## CONCURRENCY RULES (another workflow is fixing the Python lane in this repo)

SV M0 agents may create/edit ONLY: `extractors/sv/**`, `LeanModels/Sv/**`,
`Examples/sv/**`, `harness/sv/**`, `docs/sv-*.md`. FORBIDDEN (read-only):
`lakefile.toml`, `lean-toolchain`, `LeanModels.lean`, `LeanModels/Core/**`,
`LeanModels/Python/**`, `Main.lean`, `Examples/python/**`, `Examples/*.lean`
(the glob `Examples.+` is part of `lake build`!), `harness/*.py`, `harness/cases.json`,
`extractors/python/**`, `README.md`, `docs/DESIGN.md`, `docs/envelope-schema.md`,
`docs/spec-surface.md`. Do NOT run plain `lake build` as a check of YOUR work and
never make it red: SV modules are NOT imported from `LeanModels.lean` in M0.
Typecheck SV Lean files with `lake env lean LeanModels/Sv/<File>.lean` from the
repo root. Integration (imports, lakefile exe, Res unification) happens after the
Python workflow finishes — emit an integration checklist instead of doing it.

## Frontend

`python3.12` + `pyslang` 11.0.0 (installed, user site). The Python-lane extractor
uses `python3` (3.9); the SV extractor is `python3.12 extractors/sv/extract.py
<file.sv> [more...]`, emitting `foo.sv.json` next to each source. Use pyslang's
parse+elaboration (compilation) API; emit from the SYNTAX/AST level with
elaborated type info (widths) resolved. Envelope mirrors the Python one:
`schema_version "sv-0.1"`, `language "systemverilog"`, `frontend {name:
"pyslang", version}`, `source_file`, `source_sha256`, `design`, `lean_blocks: []`
(reserved, not scanned in M0). The extractor NEVER fails on valid SV: anything
outside the node vocabulary becomes `{"kind":"Unsupported","sv_kind":<slang node
class>,"text":<≤200 chars>}`. Deterministic output (double-run byte-identical).
The extractor agent owns `docs/sv-envelope-schema.md` documenting the exact node
vocabulary (analogous to the Python schema doc); the Lean ingester is written
against that doc.

## M0 language tier

Single module, no hierarchy/generate/interfaces/classes/functions. Declarations:
`logic`/`wire` (4-state), vector `[W-1:0]` or scalar, with optional initializers.
Ports in/out. Processes: `always_ff @(posedge <clk>)`, `always @(posedge <clk>)`,
`always_comb`, continuous `assign`. Statements: blocking `=`, nonblocking `<=`,
`if`/`else`, `begin/end`. Expressions: identifiers; sized/unsized literals incl.
`'0`, `'1`, x/z digits; unary `~ ! -`; binary `+ - & | ^ == != < <= > >=`;
ternary `?:`; concatenation `{a, b}`. Everything else: representable as
`Unsupported`, interpreter returns `.unsupported` (loud) when reached.
M0 target examples (all already Xcelium-verified in the galleries):
`adder`, `counter`, `race_blk`, `swap_nba`, `xsel` → `Examples/sv/*.sv`.

## 4-state value core (normative — these facts were verified on Xcelium)

`namespace LeanModels.Sv`. `inductive Logic | l0 | l1 | lx | lz` (z behaves as x
in every operator below except `===`). `structure LVec where bits : Array Logic`
— **LSB-first** (bits[0] is bit 0). `LVec.known? : LVec → Option (BitVec w)`.

Operator semantics (IEEE 1800-2017, Xcelium-confirmed):
- **Arithmetic (`+ - * < <= > >=`)**: if ANY bit of either operand is x/z, the
  entire result is x (whole-vector collapse, §11.4.3) — never bit-precise carry
  through x. Comparisons yield 1-bit x.
- **Bitwise**: per-bit tables. `&`: 0&any=0, 1&1=1, else x. `|`: 1|any=1, 0|0=0,
  else x. `^`: any x/z bit → x, else xor. `~`: ~0=1, ~1=0, ~x=~z=x.
- **Logical equality `==`/`!=`**: 0 (definite) if some bit position has both bits
  known and unequal; else x if any x/z anywhere; else 1. (NOT "any x → x".)
- **Case equality `===`/`!==`**: exact 4-state match, always 0/1.
- **`if (c)`**: true iff `c` has at least one `l1` bit; all-zero OR unknown-only
  → else branch (verified: `if (1'bx)`/`if (1'bz)` take else; absent else = no-op,
  so a latch-style `if` with x condition HOLDS the target, never x-poisons it).
- **Ternary `c ? a : b` with unknown c**: evaluate both; bitwise merge (equal
  known bits kept, differing/unknown positions → x), §11.4.11. Different from
  `if`!
- **`!c`**: 1 iff c is all-known zero; 0 iff some l1 bit; else x.
- Width contexts: M0 restricts to same-width operands (extractor emits resolved
  widths; width mismatch in source → Unsupported rather than implicit
  extension rules).
- `-` unary: two's complement with the arithmetic collapse rule.

## Scheduler core M0: cycle semantics with a schedule oracle

`abbrev SvState := List (String × LVec)` (assoc, first match wins — same
discipline as the Python lane's Env). M0 defines a **cycle-level** semantics
(full event/delay scheduler is the next tier; `initial`/`#` are Unsupported):

One `cycleStep d σ fuel inputs s`:
1. Overwrite input-port values from `inputs` (the stimulus for this cycle).
2. **Comb settle**: run `always_comb` + `assign` processes to fixpoint, fuel-
   bounded, order chosen by σ; fuel exhaustion → `.timeout` (combinational loop).
3. **Edge phase**: run every `@(posedge clk)` process once, in the order σ
   dictates; blocking assigns hit the state immediately (this is what makes
   `race_blk` schedule-dependent); nonblocking assigns append to an NBA queue
   (reads see pre-update state via the sequential state, matching the LRM's
   Active/NBA region split at cycle granularity).
4. **NBA commit** in queue order (last write to a name wins).
5. Comb settle again. The resulting state is the cycle's trace snapshot.

`def run (d : Design) (σ : ScheduleOracle) (fuel : Nat) (stim : List SvState) :
Res (List SvState)` — initial state from declaration initializers, all other
variables all-x (LRM startup, verified: pre-reset counter is x); one snapshot per
stimulus entry. `ScheduleOracle`'s exact shape is the semantics agent's choice
(must: determine a permutation of ready processes per invocation; provide
`σ_src : ScheduleOracle` = source/declaration order, the executable default —
Xcelium empirically follows declaration order for the M0 examples). `Res` for M0:
define a local `Sv.Res` mirroring the Python lane's (`ok/timeout/unsupported`;
no exceptions in M0); unification into `Core/` is an integration-checklist item.

Normative theorems (M0 definition of done, in `LeanModels/Sv/Proofs.lean`):
1. `run_deterministic : ∀ d σ fuel stim, run … = run …` — same σ twice gives the
   same trace (should be `rfl`-adjacent; run is a function — state it to pin it).
2. `swap_nba_spec : ∀ σ` — for the loaded `swap_nba` design: every post-edge
   snapshot swaps a/b (for ALL schedules).
3. `race_blk_racy : ∃ σ₁ σ₂` with different traces on the same 1-cycle stimulus
   (the (2,2) vs (1,1) witnesses).
4. `counter_from_reset : ∀ σ` — after a cycle with rst=1, count follows
   `if rst then 0 else count+1` for the rest of the stimulus (induction over
   cycles; this is `⊑@clk[from rst]` in the gallery's terms).
No `sorry`. `#guard`/`#eval` smoke tests in `LeanModels/Sv/Tests.lean` (loaded
envelopes at elab time is NOT required in M0 — a small hand-written or
JSON-ingested Design literal is fine; if JSON ingestion at elab time is easy,
prefer it).

## Differential harness vs Xcelium

`harness/sv/diff_test.py` (python3 is fine here) + `harness/sv/cases.json`.
Per case: named example, input stimulus per cycle, signals to sample, cycles N.
Xcelium side: generate a testbench that instantiates the module, drives a clock
and the per-cycle inputs, and `$display`s a canonical line per cycle
(`CYCLE <k> <name>=<binary with x/z> ...`, sampled after NBA settle — use
`@(negedge clk)` sampling); run `xrun -sv`. Lean side: a runner script executed
via `lake env lean --run harness/sv/runner.lean <envelope> <cases args...>`
printing identical lines using `σ_src`, same fuel conventions as run. Compare
line-by-line. `race_blk` is a special case: assert the Xcelium trace equals the
Lean trace for SOME σ ∈ {σ_src, σ_rev} and note which. All five examples must
pass; any mismatch is an interpreter bug to fix (Xcelium is ground truth).

## Definition of done (M0)

1. Extractor: deterministic, all 5 examples extract; schema doc written;
   `Unsupported` path exercised (e.g. a `#10` and a `for` loop in a scratch file).
2. `lake env lean` green on every `LeanModels/Sv/*.lean`; plain `lake build`
   untouched and still green (verify by running it ONCE at the very end — it must
   not know the SV lane exists).
3. The four theorems proved; axiom check clean.
4. Harness green on all 5 examples vs Xcelium 24.03.
5. `docs/sv-integration-checklist.md` written: imports to add to
   `LeanModels.lean`, lakefile exe entry for a real `leanmodels-sv-run`, `Res`/
   `Span` unification into `Core/`, companion/`// lean[` scanning, and gallery
   theorems still unproven at M0 (xsel, adder as `Sv.comb` forms, etc.).
