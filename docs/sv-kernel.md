# The SystemVerilog kernel: the declared profile, the layers, and the rules for new constructs

Status: decided by Thomas on 2026-11-02. The design and its reasoning are in `svgolf/design/architecture/ARCH-NOTE.md`
(decisions 1–10), and the schedule is in `svgolf/design/architecture/EXECUTION-PLAN.md`. This page is the short form every SV
change is held to.

## The ruling

Thomas, 2026-11-02, verbatim: "SystemVerilog's exact operational and elaboration semantics are the semantic authority. Cycle
semantics and module contracts are first-class derived abstractions for the synthesizable hardware fragment. Every cycle model
or contract used by automation carries a refinement theorem back to the exact semantics."

## The layers

| layer | what it is | rule |
|---|---|---|
| **E** | the authoritative semantics of the declared profile: a total `step`, an inductive closure, legal schedules by permutation (`choose_perm`) | the only trusted definition; no fuel |
| **D** | derived views: body, loop recurrence, settle, register transfer, cycle machine, array, contracts | each carries a refinement theorem to E, labelled Exact, OverApprox or UnderApprox |
| **L** | the proof library and tactics | may rely only on views that carry their refinement theorem |
| **S** | statements, over the observation interface (pre sample = `cycleStep2`'s `st2`, post sample = the snapshot); trusted observations are ports only | backend-independent: `Obs_run2` and `Obs_E` are two instances |
| **X** | executors | test instruments only; fuel is allowed here, with one soundness lemma, and no proof rides on an executor |

## The declared profile, v0

- **Scope by milestone.**
  - E-core-0: continuous assigns and `always_comb`. It is built and gate G-B passed. It is on master under
    `LeanModels/Sv/Kernel/` (build root `LeanModels.Sv.Kernel`, imported by `LeanModels.lean`) since 2026-11-04.
  - E-core-1: `always_ff`, NBA, reset, and the clocking discipline as a rely.
  - E-core-2: hierarchy.
  - The memory rung begins with `Kernel/CoreMem.lean` and
    `Kernel/MemElab.lean`: source-shaped, fuel-free array state, cell laws,
    and one-rank retained-declaration elaboration. `Kernel/MemCycle.lean`
    provides the provisional sequential view for direct one-rank cell NBAs;
    nested and compound memory forms remain named boundaries.
- **Process-atomic execution** is a declared profile ruling on IEEE 1800-2023 §4.7: a process runs to its next suspension point
  without interleaving. Xcelium behaves this way (`docs/sv-oracle-disagreements.md`). The departure is a register row, see
  below. `LeanModels/Sv/PreemptGuard2.lean` provides the conservative
  `Schedule:preemptive` boundary for the cycle routes: it refuses an
  instantiated design when an unsafe process can read a bit another writes,
  or two unsafe processes can write the same bit. NBA-only edge bodies and
  simple continuous assignments are safe atomic activations, including their
  cross-process overlap, because RHS evaluation precedes the NBA commit. The
  route runners apply this guard by default; the low-level `run`/`run2`
  executors remain process-atomic and source-shaped.
- **Qualified-case reports are not deferred.** E-core-0 refuses a violated `unique`/`unique0`/`priority` claim inside the
  activation that violates it. IEEE 1800-2023 §12.4.2.1 (by §12.5.3.1) defers the report to the Observed region and clears
  it when the `always_comb` is re-triggered in the same slot. So E refuses glitch-only violations that the LRM discards, and
  whether it refuses depends on the schedule. The departure is loud: E refuses, it never produces a wrong value. Register
  row `sv-div-5`.
- **Design only.** Stimulus, clocks and resets come from an event-level environment. Testbench SystemVerilog (delays, `initial`
  stimulus, `$display`) does not define design meaning.
- **4-state is the authority**, with a 2-state view and the default start policy.
- **Statement scope is narrower than E** (Thomas, 2026-11-03). This is not a semantic divergence and has no register row.
  - A task statement observes each clock cycle through two port samples (pre, just before the active edge, and post). It
    assumes one clock with one active edge (posedge or negedge, a parameter of the clocking discipline). The clock port is
    clocking, not an observed data port.
  - E still gives every such design its LRM meaning slot by slot, and the clock is an ordinary signal driven by the
    environment. Only the statements cannot speak about these designs:
    - designs that use the clock as data (`assign y = clk & en`, clock-to-output paths), whose outputs change within a
      cycle;
    - dual-edge logic;
    - several unrelated clocks. These are also outside the profile.
  - Retirement path: samples at both clock levels (an observation-model extension of Task v2, no change to E), then a
    two-edge clocking discipline, then multi-clock as a later E milestone.
- **M0 clock boundary.** The legacy `sv-0.1` JSON loader now applies the
  same loud source discipline before its implicit cycle runner: one input
  clock only, using the canonical `clk` port. Two clocks and data/derived
  clocks are refused as `Clock:multiple` or `Clock:implicit`; the richer
  `sv-0.2` event route remains the place for named clocks and instant lists.
- **Elaboration happens in Lean.** slang is a multi-point witness, never the definition.
- **Three kinds of refusal**, each loud:
  - elaboration refusal: the construct is outside the profile;
  - dynamic refusal: a reachable `unsupported` node;
  - view refusal: a derived view's hypothesis fails.

## Rules for every change

1. **No fuel in any definition.** Loops have the trip list given by their header (`TripSchema`). Fuel exists only in a test
   executor, with one soundness lemma.
2. **New constructs land in E first.** A construct enters E, with Xcelium-pinned rows, before any derived view or tactic relies
   on it. A view that adopts it carries its refinement theorem.
3. **`Stmt2` is frozen**: six constructors, no seventh. It is the legacy view behind R-DESIGN2 until its estate is transported.
   The build guard is `Examples/system-verilog/stmt2_frozen/guard.lean`: an exhaustive match that fails to compile when a
   constructor is added. Do not add an arm to make it compile; take the change to the svGolf lead and Thomas.
4. **One AST.** `Sv.Ast` will hold syntax and elaboration structure, with phase-separated types. Until it exists, new constructs
   stay retained in `PStmt`/envelope form: no new lowering, no new fuel cap.
5. **Structure is preserved.** Loops, generate families and parameters stay as written; nothing is unrolled in meaning.
6. **Every deliverable has a status label**: *provisional over `run2`*, *derived from E*, *transport theorem*, or *trusted
   statement*.

## Debts

These are the SystemVerilog tier's rows under family-architecture §3.4(b) ("a second semantics owes an adequacy theorem") and
§3.4 (the shared `Core.SemM`). Each has a retirement condition. The declared departures (§5.0a) are separate: they live in
`docs/sv-declared-divergences.json`.

| debt | what is owed | retirement condition | progress (2026-11-02) |
|---|---|---|---|
| **svGolf statements over `run2`** | svGolf `Statement` v1 is stated over the `Design2` cycle model (`run2`). It is pinned against Xcelium by testing, not refined to the authority by theorem | R-COMB, R-EDGE and R-DESIGN2 proved, and the records re-certified | Comb-profile records move to the trusted pre-sample convention over `run2` with no re-proof (`statement_obs_of_statement`, `arch-obs` `d141c956`). Three accepted records are transported to E-core-0 (`statement_E0`, `arch-x1` `d00b2919`). `run2` → E holds only for typed stimuli (`not_included_run2_E0`), so R-DESIGN2 is stated with `IncludedOn` |
| **`Design2` adequacy** | `CycleAdequacy` (`LeanModels/Sv/Adequacy.lean`) is stated, not proved, and only for the M0 `Design`, while every svGolf statement is over `Design2`. It cannot be the bridge | R-DESIGN2 proved for the profile, or the statement deleted | the R-DESIGN2 comb slice (both inclusions, assigns and `always_comb`) on `arch-x1` |
| **Statement-level fuel** | the procedural `for`/`while` meaning uses fuel. Master `c64ebdac` computes it exactly from the header, so it never runs out, but it is still fuel | loop meaning from the `TripSchema`, with no fuel | `TripSchema` as an indexed domain, the 32-bit header agreement and a fuel-free canonical decoder (`arch-loop` `a6672a4e`) |
| **`Sv.Res`, not `Core.SemM`** | the tier uses its own result type, not the family's shared `SemM` | E's outcome is `Core.SemM`-shaped | E-core-0 uses neither yet; it is decided when E-core-1 fixes the outcome type |

## Where things are

- `svgolf/design/architecture/ARCH-NOTE.md`: the design, the decisions, and the measured and proved results.
- `svgolf/design/architecture/EXECUTION-PLAN.md`: the schedule and the gate status.
- The workstream notes, on their branches until merged:
  - X1-NOTE on `arch-x1`: E-core-0 and the refinements;
  - the observation interface on `arch-obs`;
  - LOOP-NOTE on `arch-loop`;
  - the measurements on `arch-measure`.
