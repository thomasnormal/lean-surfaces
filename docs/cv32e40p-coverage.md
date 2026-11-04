# CV32E40P coverage scoreboard — phase 1 (symbolic extraction)

Program goal: prove every RTL file of the OpenHW CV32E40P core. This
scoreboard measures what the phase-1 **symbolic extraction mode** of
`extractors/sv/extract.py` (schema `sv-0.2`, see the "Symbolic mode"
section of `docs/sv-envelope-schema.md`) represents of the 27 `rtl/*.sv`
files, and what remains — the true phase-2+ semantic workload.

Method: every `rtl/*.sv` module is extracted with

```
python3.12 extractors/sv/extract.py --top <module> \
    rtl/include/cv32e40p_pkg.sv rtl/include/cv32e40p_apu_core_pkg.sv \
    rtl/include/cv32e40p_fpu_pkg.sv rtl/<file>.sv
```

i.e. compiled together with the three RTL packages so that package
parameters, typedefs and enum types resolve by name (multi-file
compilation is used for **name resolution only**). The two design laws
hold throughout: **parameters stay symbolic** (`ParameterDecl`/`ParamRef`,
symbolic range bounds with `resolved` cross-checks — a parameterized
module is data for a phase-2 Design-valued *function* of its parameters)
and **generate stays structural** (`GenerateFor`/`GenerateIf` are one
node each with symbolic bounds/condition and a body template — never
unrolled). Enum types become named `EnumType` declarations with ordered
members as metadata (never folded to raw literals); `$clog2`/`$bits`/
`$high`/`$size` are `SysCall` expression nodes over symbolic widths.

Everything below regenerates deterministically (double run
byte-identical) via

```
python3.12 extractors/sv/cv32e40p_census.py <cv32e40p-checkout> \
    --out-json docs/cv32e40p-census.json \
    --out-md docs/cv32e40p-coverage.md
```

Machine-readable sidecar for delta measurement: `docs/cv32e40p-census.json`
(per-file node/kind/blocker counters, tier map, ladder, M0 baseline,
source sha256 per file, checkout commit). Checkout censused here:
OpenHW `cv32e40p` @ `6033d2b1be3295ec774d17ac4cf226faacfdeb08`.

Reading the table:

* **nodes** = total envelope nodes; **concrete** = the shared M0
  vocabulary (processes, assigns, if/else, arithmetic, `Int`,
  `PackedType`, ...); **symbolic** = the NEW phase-1 class
  (`ParameterDecl`, `LocalParam`, `ParamRef`, `GenvarRef`,
  `GenerateFor`, `GenerateIf`, `EnumType`, `EnumRef`, `TypeRef`,
  `SysCall`, `Import`). `PackedType`/`Int` nodes whose *bounds* contain
  `ParamRef` children count as concrete; the symbolic children are
  counted in the symbolic column.
* **Unsupported** counts are node counts in the emitted envelope — the
  phase-2 work queue exactly as the ingester will see it (full per-class
  detail in the sidecar).
* **tier needed**: `T-select` bit/part selects & indexed/sliced
  assignment targets & replication · `T-reset` async-reset event lists &
  `always_latch` · `T-case` case statements · `T-ops` signed/2-state
  arithmetic, `$signed` casts, width conversions, reductions · `T-hier`
  module instances · `T-struct` packed-struct fields/type aliases ·
  `T-array` (cross-cutting, no blocker nodes of its own) word-array
  state semantics for the memory-shaped files.
* **spec sketch**: honest one-liners. **jewel** marks specs that become
  forall-parameter theorems — the capability that beats model checking.
  "contract-only" = no file-local functional spec; the file's truth is
  its interface contract inside the core-level composition (phase 3+).
* `cv32e40p_fp_wrapper.sv` is **skipped-with-reason**: it needs the
  vendored `fpnew` tree (`rtl/vendor/pulp_platform_fpnew`); its envelope
  is still emitted and censused, but its `Invalid*` nodes are
  name-resolution artifacts, not vocabulary gaps.
* `cv32e40p_register_file_ff.sv` and `cv32e40p_register_file_latch.sv`
  both declare module `cv32e40p_register_file`; the census resolves the
  top by declared name. No `rtl/*.sv` file uses `` `include `` (the `-I`
  flag exists for later phases).

## The scoreboard

<!-- census:begin -->
| file | nodes | concrete | symbolic | Unsupported (top classes) | tier needed | spec sketch |
|---|---|---|---|---|---|---|
| `cv32e40p_aligner.sv` | 126 | 118 | 5 | **3** — case×1, bit-index×1, event-list×1 | T-case+reset+select | aligner FSM: reconstructs the 32-bit instruction stream from 16-bit-granular fetches — concrete functional spec |
| `cv32e40p_alu.sv` | 988 | 813 | 75 | **100** — lhs-select×50, case×13, bit-index×10 | T-case+hier+ops+select | per-op functional spec at W=32 (shifts, compare, min/max, shuffle, bit-manip); div/rem delegated to alu_div — concrete |
| `cv32e40p_alu_div.sv` | 334 | 292 | 27 | **15** — bit-index×6, $signed-call×2, part-select×2 | T-case+ops+reset+select | **forall C_WIDTH** serial div/rem transaction: after the handshake, quotient/remainder of the operands — **jewel** |
| `cv32e40p_apu_disp.sv` | 453 | 430 | 6 | **17** — reduce-or×9, lhs-select×6, event-list×2 | T-ops+reset+select | dispatcher: no lost/duplicated APU transactions, hazard flags sound — invariant spec |
| `cv32e40p_compressed_decoder.sv` | 33 | 28 | 3 | **2** — case×1, part-select×1 | T-case+select | RVC expansion function: each 16-bit instruction maps to its 32-bit equivalent, illegal iff outside the table — concrete |
| `cv32e40p_controller.sv` | 926 | 862 | 39 | **25** — bit-index×19, event-list×4, case×2 | T-case+reset+select | pipeline control FSM — contract-only, no file-local spec |
| `cv32e40p_core.sv` | 833 | 771 | 52 | **10** — instance×7, bit-index×2, explicit-cast×1 | T-hier+ops+select | hierarchical composition — contract-only (wiring, needs T-hier) |
| `cv32e40p_cs_registers.sv` | 1401 | 1131 | 182 | **88** — lhs-select×45, struct-field×9, case×8 | T-case+ops+reset+select+struct+array | per-CSR read/write semantics; hwloop CSR family **forall N_HWLP** — partial jewel |
| `cv32e40p_decoder.sv` | 666 | 595 | 70 | **1** — case×1 | T-case | decode table: each instruction class maps to its documented control bundle; illegal-instruction soundness — concrete |
| `cv32e40p_ex_stage.sv` | 715 | 677 | 29 | **9** — lhs-select×4, instance×3, event-list×2 | T-hier+reset+select | EX-stage mux + writeback arbitration — contract-only |
| `cv32e40p_ff_one.sv` | 137 | 82 | 43 | **12** — lhs-select×10, bit-index×2 | T-select | **forall LEN**: first_one_o = index of lowest set bit; no_ones_o iff input = 0 — **jewel** |
| `cv32e40p_fifo.sv` | 270 | 236 | 28 | **6** — lhs-select×2, event-list×2, bit-index×1 | T-reset+select+array | **forall DEPTH/WIDTH/FALL_THROUGH**: order-preserving bounded queue (push/pop trace equality) — **jewel** |
| `cv32e40p_fp_wrapper.sv` | 70 | 49 | 12 | **9** — 2state-var×4, vendor-invalid-assign×2, vendor-invalid×2 | T-hier+ops+vendor | SKIPPED: needs vendored fpnew tree (rtl/vendor/pulp_platform_fpnew): fpnew_pkg types/instances do not resolve; envelope still emitted, its Invalid* nodes are name-resolution artifacts, not vocabulary gaps |
| `cv32e40p_hwloop_regs.sv` | 112 | 87 | 17 | **8** — lhs-select×4, event-list×3, 2state-var×1 | T-ops+reset+select+array | **forall N_REGS**: loop {start,end,cnt} write/read; counter decrement exact — **jewel** |
| `cv32e40p_id_stage.sv` | 1604 | 1435 | 77 | **92** — part-select×23, case×21, lhs-select×17 | T-case+hier+ops+reset+select | decode/issue stage — contract-only, no file-local spec |
| `cv32e40p_if_stage.sv` | 260 | 244 | 7 | **9** — case×4, instance×3, part-select×1 | T-case+hier+reset+select | fetch stage — contract-only, no file-local spec |
| `cv32e40p_int_controller.sv` | 268 | 220 | 13 | **35** — bit-index×32, reduce-or×2, event-list×1 | T-ops+reset+select | highest-priority pending&enabled irq selection over the 32 lines — concrete |
| `cv32e40p_load_store_unit.sv` | 396 | 374 | 7 | **15** — case×8, part-select×3, event-list×3 | T-case+hier+reset+select | misaligned-access split + sign/zero-extension of rdata — concrete data-path spec; OBI handshake contract |
| `cv32e40p_mult.sv` | 427 | 357 | 11 | **59** — lhs-select×22, width-conv×12, $signed-call×6 | T-case+ops+reset+select | signed/unsigned 32x32 multiply + dot-product/MAC — concrete |
| `cv32e40p_obi_interface.sv` | 186 | 174 | 10 | **2** — case×1, event-list×1 | T-case+reset | **forall TRANS_STABLE**: OBI address-phase stability + request/response pairing — **jewel** (protocol) |
| `cv32e40p_popcnt.sv` | 75 | 57 | 12 | **6** — lhs-select×4, bit-index×2 | T-select | popcount = sum of bits via adder tree at W=32 — concrete (generate-tree induction) |
| `cv32e40p_prefetch_buffer.sv` | 101 | 91 | 7 | **3** — instance×3 | T-hier | controller+FIFO composition — contract-only (needs T-hier) |
| `cv32e40p_prefetch_controller.sv` | 358 | 327 | 25 | **6** — case×2, part-select×2, event-list×2 | T-case+reset+select | **forall DEPTH**: outstanding-transaction counter invariant; fetch FIFO never overflows — **jewel** |
| `cv32e40p_register_file_ff.sv` | 205 | 142 | 48 | **15** — bit-index×9, lhs-select×3, event-list×3 | T-reset+select+array | **forall ADDR_WIDTH/DATA_WIDTH**: read-after-write register file, x0 hardwired to 0 — **jewel** |
| `cv32e40p_register_file_latch.sv` | 211 | 145 | 44 | **22** — bit-index×9, 2state-var×4, lhs-select×2 | T-hier+ops+reset+select+struct+array | same regfile contract as _ff (equivalence corollary) — **jewel** |
| `cv32e40p_sleep_unit.sv` | 122 | 116 | 4 | **2** — event-list×1, instance×1 | T-hier+reset | clock-gate handshake: core clock off only when quiescent — contract |
| `cv32e40p_top.sv` | 169 | 152 | 14 | **3** — instance×3 | T-hier | top-level composition — contract-only (needs T-hier) |
<!-- census:end -->

Crown jewels (the forall-parameter theorems this program exists for):
`ff_one` (forall LEN: lowest-set-bit index), `alu_div` (forall C_WIDTH:
serial div/rem transaction), `fifo` (forall DEPTH/WIDTH/FALL_THROUGH:
order-preserving queue), `register_file_ff` + `register_file_latch`
(forall ADDR/DATA widths: read-after-write, x0 = 0),
`hwloop_regs` (forall N_REGS), `prefetch_controller` (forall DEPTH:
outstanding-count invariant), `obi_interface` (forall TRANS_STABLE:
protocol stability), and the hwloop-CSR family of `cs_registers`
(forall N_HWLP, partial).

## Global blockers: before → after

Baseline = the byte-preserved single-file M0 mode over the same 27 files
(re-measured with both the pre-phase HEAD extractor and the current one:
identical, **818** Unsupported nodes; the "838" in the program brief was
a mistranscription — its per-class figures Parameter 149 / Generate* 93 /
WildcardImport 22 match the 818 run exactly).

<!-- blockers:begin -->
| blocker class | before (M0) | after (symbolic) | disposition |
|---|---|---|---|
| `AssignmentExpression:target` | 71 | 170 | T-select (grows: generate bodies/package-typed regions now visible) |
| `ElementSelectExpression` | 55 | 112 | T-select (grows: generate bodies/package-typed regions now visible) |
| `CaseStatement` | 12 | 65 | T-case (grows: generate bodies/package-typed regions now visible) |
| `RangeSelectExpression` | 36 | 48 | T-select (grows: generate bodies/package-typed regions now visible) |
| `TimedStatement:EventListControl` | 18 | 39 | T-reset (grows: generate bodies/package-typed regions now visible) |
| `UninstantiatedDefSymbol:UninstantiatedDef` | 26 | 32 | T-hier (grows: generate bodies/package-typed regions now visible) |
| `ReplicationExpression` | 18 | 25 | T-select (grows: generate bodies/package-typed regions now visible) |
| `ConversionExpression:width` | 14 | 14 | T-ops |
| `UnaryExpression:BitwiseOr` | 13 | 13 | T-ops |
| `CallExpression` | 9 | 10 | T-ops (grows: generate bodies/package-typed regions now visible) |
| `VariableSymbol:2state` | 56 | 9 | T-ops |
| `MemberAccessExpression` | 0 | 9 | T-struct (grows: generate bodies/package-typed regions now visible) |
| `VariableSymbol:type` | 11 | 8 | T-struct |
| `ConversionExpression:Explicit` | 0 | 6 | T-ops (grows: generate bodies/package-typed regions now visible) |
| `BinaryExpression:LogicalShiftLeft` | 4 | 4 | T-ops |
| `ContinuousAssignSymbol:InvalidExpression` | 40 | 2 | fp_wrapper only (vendor fpnew — skipped) |
| `BinaryExpression:Multiply` | 2 | 2 | T-ops |
| `ProceduralBlockSymbol:AlwaysLatch` | 1 | 2 | T-reset (grows: generate bodies/package-typed regions now visible) |
| `InvalidExpression` | 0 | 2 | fp_wrapper only (vendor fpnew — skipped) |
| `BinaryExpression:ArithmeticShiftRight` | 1 | 1 | T-ops |
| `TypeAliasType:TypeAlias` | 1 | 1 | T-struct |
| `ParameterSymbol:Parameter` | 149 | 0 | absorbed: ParameterDecl/LocalParam (symbolic) |
| `InvalidStatement` | 45 | 0 | absorbed: package-typed statements now bind |
| `GenerateBlockSymbol:GenerateBlock` | 39 | 0 | absorbed: GenerateIf / generate-for body |
| `VariableSymbol:range` | 37 | 0 | absorbed: symbolic PackedType bounds (ParamRef) |
| `PortSymbol:2state` | 31 | 0 | absorbed: package/enum-typed ports now resolve |
| `GenerateBlockArraySymbol:GenerateBlockArray` | 27 | 0 | absorbed: GenerateFor (one structural node, never unrolled) |
| `GenvarSymbol:Genvar` | 27 | 0 | absorbed: GenvarRef (symbolic) |
| `PortSymbol:range` | 23 | 0 | absorbed: symbolic PackedType bounds (ParamRef) |
| `WildcardImportSymbol:WildcardImport` | 22 | 0 | absorbed: Import (packages resolve) |
| `TransparentMemberSymbol:TransparentMember` | 14 | 0 | absorbed: EnumType members (metadata, never folded) |
| `NamedValueExpression:Parameter` | 8 | 0 | absorbed: ParamRef (symbolic) |
| `ProceduralBlockSymbol:NoEventControl` | 8 | 0 | absorbed: processes bind once package types resolve |
| **total** | **818** | **574** | |
<!-- blockers:end -->

What happened, honestly:

* The **name-resolution noise is gone**: parameters (149+8), generates
  (93), wildcard imports (22), enum members (14), symbolic range bounds
  on variables/ports (60), package-typed ports/processes/statements
  (31+8+45), and 38 of the 40 invalid continuous assigns — absorbed into
  the symbolic vocabulary, not folded away.
* Several semantic classes **grow** (case 12→65, lhs-select 71→170,
  bit-index 55→112, event-list 18→39, ...): M0 could not see inside
  generate bodies or bind package-typed regions, so their contents were
  invisible or lumped under `InvalidStatement`. Symbolic mode opens
  those regions; the residual is measured over *more visible design*.
  This is the honest accounting: **818 → 574** total, and the 574 is now
  100% semantics, 0% name resolution.
* **Headline residual: 574 Unsupported nodes**, of which **570** are
  real semantic-tier workload (4 are `Invalid*` vendor artifacts in the
  skipped `fp_wrapper`); **565** lie in the 26 provable files.

## The ladder

Tiers ordered for maximal early unlock, leaves first (cumulative "files
fully cleared" counts the 26 provable files; `fp_wrapper` additionally
needs the vendor tree):

<!-- ladder:begin -->
| tier (cumulative) | residual nodes | files touched | newly fully cleared | cumulative cleared (of 26 provable) |
|---|---|---|---|---|
| T-select | 355 | 21 | ff_one, popcnt | 2 |
| + T-reset | 41 | 18 | fifo, register_file_ff | 4 |
| + T-case | 65 | 13 | aligner, compressed_decoder, controller, decoder, obi_interface, prefetch_controller | 10 |
| + T-ops | 59 | 11 | alu_div, apu_disp, hwloop_regs, int_controller, mult | 15 |
| + T-hier | 32 | 11 | alu, core, ex_stage, id_stage, if_stage, load_store_unit, prefetch_buffer, sleep_unit, top | 24 |
| + T-struct | 18 | 2 | cs_registers, register_file_latch | 26 |
<!-- ladder:end -->

Proof-order recommendation (leaves first, jewels earliest):

1. **T-select** alone finishes `ff_one` and `popcnt` — the first
   forall-LEN jewel lands immediately, by induction on the structural
   `GenerateFor` nodes.
2. **+T-reset** (async-reset event lists — small tier) finishes `fifo`
   and `register_file_ff`: two more jewels, and the `T-array` word-state
   semantics should be designed here alongside them.
3. **+T-case** finishes the pure decode leaves `decoder` and
   `compressed_decoder` (table specs), plus `aligner`, `obi_interface`
   (protocol jewel), `prefetch_controller` (DEPTH jewel) and the
   `controller` FSM (contract-only).
4. **+T-ops** finishes `alu_div` (forall-C_WIDTH jewel), `mult`,
   `int_controller`, `apu_disp`, `hwloop_regs` (jewel).
5. **+T-hier** finishes `alu` (closing the whole leaf datapath) and
   opens the contract-only pipeline files (`ex/if/id_stage`,
   `load_store_unit`, `prefetch_buffer`, `sleep_unit`, `core`, `top`).
6. **+T-struct** finishes `cs_registers` and `register_file_latch` —
   all 26 provable files represented.

### Phase-2 design note: the Lean ingestion contract

The envelope vocabulary fixed in this phase is the stable contract for
phase-2 Lean semantics. Each symbolic envelope ingests as a **Design-
valued function of its parameters**: `ParameterDecl`s become a `Params`
record (defaults as `resolved` metadata), and every width/bound/index
term containing `ParamRef`/`SysCall` nodes elaborates to a Lean
expression over that record. `instantiate : Design → Params →
FlatDesign` is an ordinary Lean function that proofs reason about
*symbolically* — a forall-width theorem is `∀ p : Params, spec
(instantiate d p)`, proved without ever evaluating `instantiate` at a
concrete parameter, which is exactly the capability model checking lacks.
`GenerateFor` nodes (genvar, symbolic bounds, body template) expand by
recursion over the genvar range, so proofs about them go by induction on
the range — the direct precedent is the analog lane's `chain : Nat →
Netlist` construction (`LeanModels/Spice/RippleNetlist.lean`, proved
forall-n in `Examples/spice/ripple_adder`), which this generalizes from
a hand-written family to source-extracted ones. `GenerateIf` stays a
symbolic conditional over `Params`; enum types ingest as named finite
types with the ordered member list, values as lemmas rather than
substitutions. No semantics change lands until this contract does.

## Probe deltas (phase-1 acceptance)

`Unsupported` node counts, single-file M0 mode (before) vs symbolic mode
(after):

| probe | before | after | residual after (all deliberate phase-2+ tiers) |
|---|---|---|---|
| `cv32e40p_ff_one.sv` (generate-heavy) | 13 | 12 | selects inside the generate body templates (`AssignmentExpression:target` ×10, `ElementSelectExpression` ×2) — the two generate trees themselves are now two structural `GenerateFor` nodes (with nested `GenerateIf`/`GenerateFor`) |
| `cv32e40p_alu_div.sv` (params+enum+generate+`$high`) | 24 | 15 | selects (×9), `$signed` casts (×2), `\|` reduction (×2), `case` (×1), async-reset event list (×1) |
| `cv32e40p_decoder.sv` (pkg-heavy) | 32 | 1 | the single giant `case` statement |
