# CV32E40P spec surface — normative gallery (design target)

**Status: design document, drafted 2026-07-30; nothing here elaborates yet.**
This is the CV32E40P counterpart of `docs/spec-surface.md` (Python) and
`docs/sv-spec-surface.md` (SystemVerilog): a gallery of statement-level Lean
spec drafts for real modules of the [OpenHW CV32E40P] RV32IMC core, written to
drive the SV surface's next feature slices. Every port list and behavior claim
below was read out of the actual RTL at
`scratchpad/svtest/cv32e40p/rtl/` (plus the user manual under
`docs/source/` of that clone) — not from folklore; the "what the RTL
corrected" section at the end records where the RTL contradicted the folklore.
The corpus-level census lives in `docs/sv-corpus-coverage.md`; a per-module
CV32E40P census (`docs/cv32e40p-coverage.md`) has not been produced yet — when
it exists, its feature tallies should be checked against the NOTE lines here.

Relation to the existing surface: everything from `docs/sv-spec-surface.md`
is assumed (⊨, `Sv.comb`, `Sv.onPosedge`, `⊑@clk`, ⊨sva, schedule oracle σ,
`LVec`/`BitVec` coercions, parametric design families as Lean functions of
their parameters). This gallery is about what CV32E40P **adds**: contracts,
oracles, ghost accounting, spec-side tables, and the transaction judgment.

## Design laws (established; the gallery obeys and showcases them)

- **L1 — parameters stay symbolic.** Elaboration is a Lean function of the
  parameters (`ff_one : Nat → Sv.Design`); specs quantify over them. Theorems
  that hold for *every* width/depth are marked **CROWN JEWEL**.
- **L2 — specs mention ports only.** Internal registers, FSM states, pointers,
  counters (`ctrl_fsm_cs`, `read_pointer_q`, `mepc_q`, …) never appear in a
  spec statement. They live in proof-side invariants. Where a spec seems to
  need internal state, the surface provides *spec-side* state instead: a golden
  model's state (entry 3, 4), or ghost/auxiliary accounting (entry 10).
- **L3 — physical/ISA facts enter as spec-side definitions, never axioms.**
  RISC-V division conventions, the decode table, WARL legalization masks, the
  abstract memory semantics — all are ordinary Lean `def`s the theorems refer
  to. Nothing about the ISA is postulated.
- **L4 — every safety/behavior spec sketch notes its realizability twin.**
  A port-trace safety spec is vacuously satisfiable by a wedged design (this
  is the hardware analogue of the reward-hackable bare "if it returns" form
  the Python lane's `~~>` was strengthened against). Each sequential entry
  therefore carries a *realizability twin*: a liveness/latency statement that
  the described interaction actually completes under a live environment. For
  combinational entries the twin is the `Sv.comb` settling obligation itself
  (the always/assign network is acyclic and total).

## New judgment family (introduced by this gallery)

All of these are design-target notation; each is inventoried with a design
sketch in section A.

| Surface | Reading |
|---|---|
| `m ⊨ᶜ ⟨R, G⟩` | rely-guarantee contract: on every trace whose *input* ports satisfy rely `R`, the trace satisfies guarantee `G` |
| `m ⊨tx T` | transaction conformance on a handshake: accepted request ⇒ correct response within `T.latency`, held until consumed (revives `Sv.transaction` from SV gallery ex. 10, now with latency bound and hold discipline) |
| `m ⊨[β] P` | run against environment oracle β (bus/memory side) in addition to σ |
| `m ≈mem[β_M] sem` | the module's port behavior against a memory-like oracle equals an abstract memory semantics `sem` |
| `m ⊑@clk[areset rn] model via Rel` | Mealy refinement of a Lean step function, from deassertion of the **asynchronous** active-low reset `rn`, outputs related to model state by `Rel` |
| `∃ ghost, …` | auxiliary spec state quantified inside a guarantee — spec-side bookkeeping over the port trace, not RTL state |

Conventions: each module gets a generated typed port record (`ins`/`outs`
fields named exactly as in the RTL, widths symbolic in the parameters, e.g.
`first_one_o : BitVec (Nat.clog2 LEN)`); preconditions are ordinary
hypotheses; spec RHSs are mathematical Lean (`Nat.popCount`, `List` queues,
`Fin 32 → BitVec 32` register maps, `Rv.*` ISA definitions).

---

## The gallery

### 1. `cv32e40p_ff_one` — ∀-width lowest-set-index (the simplest crown jewel)

```systemverilog
module cv32e40p_ff_one #(parameter LEN = 32) (
    input  logic [LEN-1:0]         in_i,
    output logic [$clog2(LEN)-1:0] first_one_o,
    output logic                   no_ones_o);
```

A `$clog2(LEN)`-level selection tree over generate loops; each internal node
prefers its left (lower-index) subtree, so the module computes the *lowest*
set bit index. Purely combinational.

```lean
def lowestSet (x : BitVec n) (hx : x ≠ 0) : Fin n := ⟨Nat.find (exists_getElem_of_ne_zero hx), …⟩

-- CROWN JEWEL (∀-width)
@[spec] theorem ff_one_spec (LEN : Nat) (hLEN : 2 ≤ LEN) (x : BitVec LEN) :
    (ff_one LEN) ⊨ Sv.comb fun ins outs =>
      ins.in_i = x →
        outs.no_ones_o = decide (x = 0) ∧
        ∀ hx : x ≠ 0, outs.first_one_o.toNat = (lowestSet x hx).val
```

`first_one_o` is unconstrained when `x = 0` (the RTL leaves junk on it), and
the theorem says so by saying nothing. The hypothesis `2 ≤ LEN` is honest, not
defensive: at `LEN = 1` the generate tree is empty, `sel_nodes[0]` is tied to
`1'b0`, and `no_ones_o` is stuck at 1 regardless of `in_i` — the RTL is
genuinely broken there, and the spec must not paper over it. Non-power-of-two
`LEN` works (the tree pads with out-of-range leaves tied to 0) and is covered
by the quantifier.

**NOTE (new vocabulary):** `Nat.clog2` in port-record *types*
(`first_one_o : BitVec (Nat.clog2 LEN)`); an induction principle over the
generate-tree structure (the SV gallery's ex. 11 promised this for linear
carry chains; here the recursion is a binary tree with padding).
**Difficulty/deps:** the easiest crown jewel — self-contained, no ISA model;
proof is one tree induction with a padding lemma. The right first target for
the parametric-design machinery.

### 2. `cv32e40p_popcnt` — fixed-width adder tree

```systemverilog
module cv32e40p_popcnt (
    input  logic [31:0] in_i,
    output logic [ 5:0] result_o);
```

Five levels of paired 2-input adders (`cnt_l1` … `cnt_l4`, then the root add).
**Not parameterized** — unlike `ff_one`, the RTL hardcodes 32 bits, so there is
no ∀-width theorem to have here (see "what the RTL corrected").

```lean
@[spec] theorem popcnt_spec (x : BitVec 32) :
    popcnt ⊨ Sv.comb fun ins outs =>
      ins.in_i = x → outs.result_o.toNat = x.toNat.popCount
```

**NOTE (new vocabulary):** none beyond a spec-prelude `popCount` helper —
this entry is the calibration point: at fixed width the whole theorem should
close by `sv_prove` ⟶ `bv_decide` with no structural induction at all.
**Difficulty/deps:** trivial; self-contained. Pairs with entry 1 as the
"same shape, with vs. without L1" contrast.

### 3. `cv32e40p_fifo` — ∀-depth queue semantics

```systemverilog
module cv32e40p_fifo #(
    parameter bit FALL_THROUGH = 1'b0,
    parameter int unsigned DATA_WIDTH = 32,
    parameter int unsigned DEPTH = 8,
    parameter int unsigned ADDR_DEPTH = (DEPTH > 1) ? $clog2(DEPTH) : 1) (
    input  logic clk_i, rst_ni,            // rst_ni: ASYNCHRONOUS, active low
    input  logic flush_i, flush_but_first_i, testmode_i,
    output logic full_o, empty_o,
    output logic [ADDR_DEPTH:0]   cnt_o,
    input  logic [DATA_WIDTH-1:0] data_i,
    input  logic push_i,
    output logic [DATA_WIDTH-1:0] data_o,
    input  logic pop_i);
```

Ring buffer with read/write pointers and a count register; push is ignored
when full, pop when empty; simultaneous push+pop keeps the count;
`flush_but_first_i` drops everything except the head. The spec-side model is
the thing the pointers are hiding — a `List`:

```lean
def fifoStep (DEPTH : Nat) (q : List (BitVec W)) (i : FifoIn W) : List (BitVec W) :=
  if i.flush then []
  else if i.flushButFirst then q.take 1
  else
    let q₁ := if i.push ∧ q.length < DEPTH then q ++ [i.data] else q
    if i.pop ∧ q ≠ [] then q₁.tail else q₁    -- pop reads the OLD head

-- CROWN JEWEL (∀-width, ∀-depth)
@[spec] theorem fifo_refines (W DEPTH : Nat) (hD : 0 < DEPTH) :
    (fifo W DEPTH (FALL_THROUGH := false)) ⊑@clk_i[areset rst_ni] (fifoStep DEPTH) via
      fun q outs =>
        outs.cnt_o.toNat = q.length ∧
        outs.full_o  = decide (q.length = DEPTH) ∧
        outs.empty_o = decide (q = []) ∧
        ∀ d, q.head? = some d → outs.data_o = d

-- corollary in the SV gallery's stream vocabulary: conservation
theorem fifo_conservation (hnoflush : …) :
    (fifo W DEPTH false) ⊨ᶜ ⟨NoFlush, fun tr => Sv.pops tr <+: Sv.pushes tr⟩
```

`data_o` when empty is RTL garbage (`mem_q[read_pointer_q]`), so the output
relation constrains it only through `head?` — this is why `via` must be a
*relation*, not the M0 single-output function. `FALL_THROUGH := true` changes
`empty_o` and bypasses `data_o` combinationally from `data_i`; it gets its own
model variant, deliberately out of the first scope. **Realizability twin:**
after a push into a non-full FIFO, `empty_o` is low and `data_o` carries the
pushed value within 1 cycle — the refinement is not satisfied by a FIFO that
never surfaces data.
**NOTE (new vocabulary):** `⊑@clk[areset rn] model via Rel` — three upgrades
to M0's `⊑@clk[from rst]` at once: input *records* per cycle (not one port),
an output *relation* (not one observed port), and the **asynchronous
active-low reset** qualifier (M0's qualifier meant "from the first edge that
*samples* rst = 1"; here reset is level-sensitive and unclocked — every
clocked module in CV32E40P uses this discipline).
**Difficulty/deps:** medium; self-contained. Proof-side invariant is the
ring-buffer↔List abstraction (pointer arithmetic mod `FIFO_DEPTH` — internal,
so L2-invisible). The RTL's `DEPTH == 0` pass-through branch is asserted away
by the RTL itself (`assert (DEPTH > 0)`), hence `hD`.

### 4. `cv32e40p_register_file` (ff variant) — last-write memory + x0 + real read-during-write

```systemverilog
module cv32e40p_register_file #(
    parameter ADDR_WIDTH = 5, DATA_WIDTH = 32, FPU = 0, ZFINX = 0) (
    input  logic clk, rst_n,                    // async active-low reset
    input  logic scan_cg_en_i,
    input  logic [ADDR_WIDTH-1:0] raddr_a_i, raddr_b_i, raddr_c_i,   // 3 read ports
    output logic [DATA_WIDTH-1:0] rdata_a_o, rdata_b_o, rdata_c_o,
    input  logic [ADDR_WIDTH-1:0] waddr_a_i, waddr_b_i,              // 2 write ports
    input  logic [DATA_WIDTH-1:0] wdata_a_i, wdata_b_i,
    input  logic                  we_a_i, we_b_i);
```

What the RTL actually does (all read out of the file, several against
folklore): reads are pure combinational `assign`s from the flop array — so a
read in the same cycle as a write to the same address returns the **old**
value, the new one is visible from the next edge. On a same-address
same-cycle write collision, **port B wins** (`if (we_b_dec[i]) … else if
(we_a_dec[i])`). `mem[0]` is rewritten to 0 every cycle — x0 is hardwired.
Bit 5 of a read address selects the FP bank, which with `FPU = 0` is tied to
`'0`, so "FP reads" return 0; writes with `waddr[5] = 1` are silently dropped
(the write decoder only compares against 0…31). The `ADDR_WIDTH` parameter is
**not honestly symbolic**: the code indexes `raddr[5]` and `raddr[4:0]`
unconditionally and the core instantiates `ADDR_WIDTH = 6` — so this entry
quantifies over *addresses*, not widths (see "what the RTL corrected"; no
crown-jewel marking, by honesty).

```lean
def rfStep (s : Fin 32 → BitVec 32) (i : RfIn) : Fin 32 → BitVec 32 := fun r =>
  if r = 0 then 0
  else if i.we_b ∧ intAddr i.waddr_b = some r then i.wdata_b   -- port B beats port A
  else if i.we_a ∧ intAddr i.waddr_a = some r then i.wdata_a
  else s r                                    -- intAddr : BitVec 6 → Option (Fin 32), none iff bit 5 set

def rfRead (s : Fin 32 → BitVec 32) (a : BitVec 6) : BitVec 32 :=
  match intAddr a with | some r => s r | none => 0             -- FPU = 0: FP bank reads as 0

@[spec] theorem register_file_refines :
    (register_file (FPU := 0)) ⊑@clk[areset rst_n] rfStep via
      fun s ins outs =>
        outs.rdata_a_o = rfRead s ins.raddr_a_i ∧
        outs.rdata_b_o = rfRead s ins.raddr_b_i ∧
        outs.rdata_c_o = rfRead s ins.raddr_c_i   -- reads see the PRE-edge state:
                                                  -- read-during-write ⇒ OLD value

-- the ∀-addr last-write corollaries, stated purely on ports:
theorem rf_last_write (a : BitVec 6) (h0 : a ≠ 0) (hint : a[5] = false) :
    register_file ⊨ Sv.onPosedge fun s s' =>
      s.we_a_i → s.waddr_a_i = a → ¬(s.we_b_i ∧ s.waddr_b_i = a) →
      s'.raddr_c_i = a → s'.rdata_c_o = s.wdata_a_i

theorem rf_x0_hardwired :
    register_file ⊨ Sv.afterReset fun tr => ∀ n, tr.raddr_a_i n = 0 → tr.rdata_a_o n = 0
```

Note the `via` relation now takes `ins` too (Mealy outputs): the read data is
a function of *current* address and *pre-edge* state — that asymmetry **is**
the read-during-write behavior, stated rather than narrated.
**Realizability twin:** `rf_last_write` is itself the twin of the refinement's
safety direction — a written value is actually observable one cycle later.
**NOTE (new vocabulary):** Mealy-style `via s ins outs`; `Fin 32 → BitVec 32`
as spec-side model state; nothing else. **Difficulty/deps:** easy-medium;
self-contained. The subtlety is all discovery (priority, old-value reads,
dropped high writes), now recorded; per-address proof is mechanical.

### 5. `cv32e40p_alu` — per-opcode combinational conformance

```systemverilog
module cv32e40p_alu import cv32e40p_pkg::*; (
    input  logic clk, rst_n, enable_i,
    input  alu_opcode_e operator_i,                    // 7-bit enum, ~60 ops
    input  logic [31:0] operand_a_i, operand_b_i, operand_c_i,
    input  logic [1:0]  vector_mode_i,                 // PULP SIMD: 32/16/8-bit lanes
    input  logic [4:0]  bmask_a_i, bmask_b_i,
    input  logic [1:0]  imm_vec_ext_i,
    input  logic        is_clpx_i, is_subrot_i,
    input  logic [1:0]  clpx_shift_i,
    output logic [31:0] result_o,
    output logic        comparison_result_o,
    output logic        ready_o,                       // low only while dividing
    input  logic        ex_ready_i);
```

Combinational for everything except DIV/REM (which own entry 6). The trap
discovered by reading: the adder result is routed **through the shifter** —
for `ALU_ADD`, `result_o = (a + b) >>> bmask_b_i` (the plain add is the
shift-amount-zero case of the PULP add-with-round-and-normalize family). So
the base-ISA conformance theorem needs a benign-inputs hypothesis:

```lean
def Rv32Base (ins : AluIns) : Prop :=          -- "no PULP-SIMD context"
  ins.vector_mode_i = VEC_MODE32 ∧ ins.bmask_a_i = 0 ∧ ins.bmask_b_i = 0 ∧
  ins.imm_vec_ext_i = 0 ∧ ins.is_clpx_i = false ∧ ins.is_subrot_i = false

def aluBaseSem : AluOp → BitVec 32 → BitVec 32 → BitVec 32   -- spec-side table (L3)
  | .ADD => (· + ·)  | .SUB => (· - ·)  | .AND => (· &&& ·)  | .XOR => (· ^^^ ·)
  | .SLL => fun a b => a <<< (b.extractLsb' 0 5)  | .SRA => …  | .SLTS => …  | …

@[spec] theorem alu_conf_base (op : AluOp) (hop : op ∈ rv32imAluOps) (a b : BitVec 32) :
    alu ⊨ Sv.comb fun ins outs =>
      Rv32Base ins → ins.operator_i = op → ins.operand_a_i = a → ins.operand_b_i = b →
      outs.result_o = aluBaseSem op a b

@[spec] theorem alu_conf_cmp (op) (hop : op ∈ cmpOps) (a b : BitVec 32) :
    alu ⊨ Sv.comb fun ins outs => Rv32Base ins → … →
      outs.comparison_result_o = cmpSem op a b     -- branches consume this port
```

**Scope note (PULP SIMD):** `vector_mode_i ∈ {16, 8}` splits every datapath
into lanes (partitioned carry chains, per-lane shift amounts, per-lane
comparisons feeding byte-replicated results); shuffle/pack/clip/bit-manip ops
add ~40 more table rows. All of it is *stateable* in exactly the
`aluBaseSem`-table style (a `laneMap` combinator over 2×16-bit / 4×8-bit
views), and none of it is in the first scope. The `Rv32Base` hypothesis is
what makes the base table sound without it.
**NOTE (new vocabulary):** spec-side op-semantics table as data; enum-typed
port fields (`operator_i : AluOp` in the port record, from the SV package
enum). **Difficulty/deps:** per-row easy (fixed width — `bv_decide` closes
each row); breadth is the cost. RHS definitions overlap the ISA model's
execute stage (see section B) — write them once, in the model.

### 6. `cv32e40p_alu_div` — the ⊨tx transaction, ∀-width — CROWN JEWEL

```systemverilog
module cv32e40p_alu_div #(parameter C_WIDTH = 32, C_LOG_WIDTH = 6) (
    input  logic Clk_CI, Rst_RBI,                  // async active-low reset
    input  logic [C_WIDTH-1:0]     OpA_DI, OpB_DI,
    input  logic [C_LOG_WIDTH-1:0] OpBShift_DI,
    input  logic OpBIsZero_SI, OpBSign_SI,
    input  logic [1:0] OpCode_SI,                  // 0 udiv, 1 div, 2 urem, 3 rem
    input  logic InVld_SI,                         // req handshake
    input  logic OutRdy_SI,                        // resp handshake
    output logic OutVld_SO,
    output logic [C_WIDTH-1:0] Res_DO);
```

Serial restoring divider, 3-state FSM (IDLE/DIVIDE/FINISH — proof-side only,
per L2). The module boundary is **not** "divide a by b": the ALU pre-swaps the
operands (`OpA_DI` gets the *divisor*), pre-shifts the dividend left
(`OpB_DI = dividend <<< OpBShift_DI`, shift derived from its leading zeros),
and precomputes `OpBIsZero_SI`. Worse, `OpBIsZero_SI` is consumed *live*
during DIVIDE, not latched — so input stability during the transaction is a
load-bearing rely, not hygiene. The honest module-level spec carries the
preprocessing as a hypothesis; the clean statement is its ALU-level twin.

```lean
-- L3: RISC-V M-extension conventions as definitions, width-generic
def Rv.divRem (W : Nat) (op : DivOp) (dividend divisor : BitVec W) : BitVec W := …
  -- div-by-zero: quot = allOnes, rem = dividend; overflow (intMin / −1): quot = intMin, rem = 0

structure DivPre (W) (dividend divisor : BitVec W) (op : DivOp) : AluDivIns W → Prop := …
  -- OpA_DI = divisor, OpB_DI = dividend <<< OpBShift_DI, OpBShift_DI = normalization amount,
  -- OpBIsZero_SI = decide (divisor = 0), OpBSign_SI/OpCode_SI encode op — AND all held
  -- stable from acceptance until the response is consumed

-- CROWN JEWEL (∀-width; C_LOG_WIDTH = clog2(C_WIDTH+1) is the RTL's own validity assertion,
-- so it is the design family's domain, not a theorem hypothesis)
@[spec] theorem alu_div_tx (W : Nat) (hW : 0 < W) (dividend divisor : BitVec W) (op : DivOp) :
    (alu_div W) ⊨tx {
      rely     := DivPre W dividend divisor op
      request  := fun ins  => ins.InVld_SI
      response := fun outs => outs.OutVld_SO ∧ outs.Res_DO = Rv.divRem W op dividend divisor
      latency  := fun ins  => ins.OpBShift_DI.toNat + 2      -- ≤ W + 2
      holdUntil := fun ins => ins.OutRdy_SI }

-- realizability twin at the clean boundary (fixed W = 32, via entry 5's ports):
theorem alu_div_op (a b : BitVec 32) (op) (hop : op ∈ divOps) :
    alu ⊨tx { request  := fun ins => ins.enable_i ∧ ins.operator_i = op ∧
                          ins.operand_a_i = a ∧ ins.operand_b_i = b
              response := fun outs => outs.ready_o ∧ outs.result_o = Rv.divRem 32 op a b
              latency  := 34, holdUntil := fun ins => ins.ex_ready_i }
```

A wrinkle the RTL insists on: `OutVld_SO` is also high while IDLE (before any
request) — so "OutVld ∧ result correct" is only meaningful *inside* a
transaction window, which is exactly the scoping `⊨tx` provides and a bare
trace-`always` would get wrong.
**NOTE (new vocabulary):** the revived `⊨tx` — now a structure with `rely`
(input stability + preprocessing), a per-request `latency` bound (L4's twin is
built in: the response must *arrive*), and `holdUntil` (response held until
the consumer takes it, per the FINISH state's wait-on-`OutRdy_SI`).
**Difficulty/deps:** medium-hard; the ∀-width induction is over the serial
iteration (a descending invariant on the remainder/quotient pair). Needs
`Rv.divRem` from the ISA model's M slice — the first concrete "build the ISA
model early" pull.

### 7. `cv32e40p_decoder` — conformance to a spec-side decode table

```systemverilog
module cv32e40p_decoder import cv32e40p_pkg::*; #(
    parameter COREV_PULP = 1, COREV_CLUSTER = 0, A_EXTENSION = 0, FPU = 0, /* … */) (
    input  logic        deassert_we_i,
    input  logic [31:0] instr_rdata_i,
    input  logic        illegal_c_insn_i,
    output logic        illegal_insn_o, ebrk_insn_o, mret_insn_o, /* … */ ecall_insn_o, wfi_o,
    output logic        alu_en_o,   output alu_opcode_e alu_operator_o,
    output logic [2:0]  alu_op_a_mux_sel_o, /* … ~60 control outputs total:
                        ALU/MUL selection, immediates, regfile we, CSR op,
                        LSU type/sign/we, hwloop, jump/branch mux … */
    input  PrivLvl_t    current_priv_lvl_i,  input logic [31:0] mcounteren_i,
    input  logic        debug_mode_i, fs_off_i, /* … */);
```

Fully combinational — a single giant `always_comb` dispatching on
`instr_rdata_i[6:0]` and inner fields. **Correction to the brief:** there is
no `casez` anywhere in this RTL; the wildcard dispatch is done with
`unique case … inside` (set-membership patterns with open ranges) and plain
`unique case`. The spec-side need is the same — don't-care pattern matching —
but the semantics to model is `case inside` (LRM §12.5.4) plus `unique`
priority claims, not `casez`.

```lean
structure InstrPat where mask val : BitVec 32          -- wildcard pattern
def InstrPat.matches (p : InstrPat) (w : BitVec 32) : Bool := (w &&& p.mask) = p.val

structure DecodeRow where
  pat  : InstrPat
  ctrl : CtrlImage        -- PARTIAL record: only the ports this row constrains

def decodeTable (cfg : DecoderCfg) : List DecodeRow   -- L3: the ISA encoding as data;
                                                      -- cfg (COREV_PULP, FPU, …) selects rows

@[spec] theorem decoder_conforms (cfg) (row) (hrow : row ∈ decodeTable cfg)
    (w : BitVec 32) (hm : row.pat.matches w) :
    (decoder cfg) ⊨ Sv.comb fun ins outs =>
      ins.instr_rdata_i = w → ins.illegal_c_insn_i = false → ins.deassert_we_i = false →
      DecoderBenign ins →                    -- debug_mode/fs_off/priv at the row's assumed values
      outs ▷ row.ctrl ∧ outs.illegal_insn_o = false     -- ▷ : agrees on constrained fields

@[spec] theorem decoder_illegal (cfg) (w) (hno : ∀ row ∈ decodeTable cfg, ¬row.pat.matches w) :
    (decoder cfg) ⊨ Sv.comb fun ins outs =>
      ins.instr_rdata_i = w → outs.illegal_insn_o = true
```

The completeness theorem `decoder_illegal` is the one simulators never give
you: *everything* outside the table is flagged. `deassert_we_i` (controller
kill signal) is hypothesized false in the conformance rows; its effect (we
outputs forced off, `csr_op` forced to READ) is two more rows, not a footnote.
**Realizability twin:** trivial (combinational totality — every 32-bit word
hits exactly one verdict; the `unique` claims become disjointness obligations
on the table).
**NOTE (new vocabulary):** `InstrPat` wildcard patterns + `case inside`
semantics in the SV core; partial-record agreement `▷` for "this row
constrains these 14 of the 60 outputs"; config-parametric tables.
**Difficulty/deps:** statement easy, breadth brutal (RV32I ≈ 50 rows; +M, +A,
+C-expanded, +PULP ≈ 300). Blocks on the ISA model's *encoding* tables —
`decodeTable` should be generated from the same source of truth the ISA
model's decoder uses, or the two will drift.

### 8. `cv32e40p_cs_registers` — the CsrBehavior table: WARL as data, trap-entry atomicity

```systemverilog
module cv32e40p_cs_registers import cv32e40p_pkg::*; #(
    parameter N_HWLP = 2, APU = 0, FPU = 0, PULP_SECURE = 0, USE_PMP = 0, /* … */) (
    input  logic clk, rst_n,
    input  logic [31:0] hart_id_i, mtvec_addr_i,   input logic csr_mtvec_init_i,
    // SRAM-like SW interface
    input  csr_num_e csr_addr_i,  input logic [31:0] csr_wdata_i,
    input  csr_opcode_e csr_op_i, output logic [31:0] csr_rdata_o,
    // dedicated HW view ports
    output logic [23:0] mtvec_o,  output logic [1:0] mtvec_mode_o,
    output logic [31:0] mepc_o, mie_bypass_o, mcounteren_o, depc_o,
    input  logic [31:0] mip_i,    output logic m_irq_enable_o, u_irq_enable_o,
    output PrivLvl_t priv_lvl_o,  output logic debug_single_step_o, /* … */
    // trap-entry command interface (from controller)
    input  logic [31:0] pc_if_i, pc_id_i, pc_ex_i,
    input  logic csr_save_if_i, csr_save_id_i, csr_save_ex_i,
    input  logic [5:0] csr_cause_i,  input logic csr_save_cause_i,
    input  logic csr_restore_mret_i, csr_restore_dret_i, /* … */
    // perf-counter event inputs (16 of them) …
);
```

The RTL is *already* table-shaped: one `case (csr_addr_i)` whose every arm is
a legalization expression. Those expressions, read out of the file, become the
data of a spec-side `CsrBehavior` table:

```lean
structure CsrBehavior where
  addr     : BitVec 12
  resetVal : BitVec 32
  legalize : (old wdata : BitVec 32) → BitVec 32     -- WARL mask/legalization AS DATA (L3)
  hwView   : Option (PortName × (BitVec 32 → …))     -- dedicated output port, if any

def csrTable (cfg) : List CsrBehavior := [
  { addr := MEPC,   legalize := fun _ w => w &&& ~1#32, hwView := some (mepc_o, id), … },
  { addr := MCAUSE, legalize := fun _ w => w.bit31 ++ 0 ++ w.extractLsb' 0 5, … },
  { addr := MIE,    legalize := fun _ w => w &&& IRQ_MASK, hwView := some (mie_bypass_o, …), … },
  { addr := MTVEC,  legalize := fun _ w => w.hi24 ++ 0#6 ++ (0 ++ w.bit0), … },  -- 256-B aligned base
  { addr := MSTATUS, legalize := mstatusLegalize, … },  -- picks {uie,mie,upie,mpie,mpp,mprv}
  { addr := MSCRATCH, legalize := fun _ w => w, … }, … ]

-- rmw folds CSR_OP_SET/CLEAR against csr_rdata_o — a port, so this stays L2-pure
def rmw (s : Ports) : BitVec 32 :=
  match s.csr_op_i with
  | .WRITE => s.csr_wdata_i | .SET => s.csr_rdata_o ||| s.csr_wdata_i
  | .CLEAR => s.csr_rdata_o &&& ~~~s.csr_wdata_i | .READ => s.csr_rdata_o

-- one theorem per table row, generated: SW write, observed on the HW-view port
@[spec] theorem csr_write_conforms (c) (hc : c ∈ csrTable cfg) (hport : c.hwView = some (p, f)) :
    cs_registers ⊨ Sv.onPosedge fun s s' =>
      s.csr_addr_i = c.addr → s.csr_op_i ≠ .READ → ¬s.csr_save_cause_i →
      s'.(p) = f (c.legalize (s.csr_rdata_o) (rmw s))

-- trap entry: one edge, the whole tuple, and it BEATS a same-cycle SW write
@[spec] theorem csr_trap_entry_atomic :
    cs_registers ⊨ Sv.onPosedge fun s s' =>
      s.csr_save_cause_i → ¬s.debug_csr_save_i →
      s'.mepc_o = savePc s ∧               -- pc_if/pc_id/pc_ex per csr_save_{if,id,ex}_i
      s'.m_irq_enable_o = false ∧          -- mstatus.MIE cleared
      McauseReads s' s.csr_cause_i ∧       -- via the read port, next cycle
      MpieReads s' (s.m_irq_enable_o)      -- MPIE := old MIE, via the read port
```

Scoped honestly to the representative subset with dedicated HW-view ports:
{mstatus.{mie,mpie,mpp}, mtvec, mepc, mcause, mie, mscratch} with
`PULP_SECURE = 0`, `FPU = 0`. CSRs whose only observation point is
`csr_rdata_o` (mscratch, mcause) get the two-phase read-back form
(`McauseReads`: a later read with no intervening write returns the value) —
heavier, stated once as a combinator. Out of first scope: PMP, performance
counters, debug/trigger, hwloop CSRs — each is *rows*, not new machinery.
**Realizability twin:** a legalized write is observable (the read-back
combinator is non-vacuous: reads do occur and return); trap entry commands are
never lost (`csr_save_cause_i` at a live edge always lands the tuple).
**NOTE (new vocabulary):** the `CsrBehavior` spec-side DSL; per-row theorem
generation from a table; the read-back observation combinator;
port-name-indexed `hwView`. **Difficulty/deps:** medium per row, large
surface. Legalization semantics comes from the privileged spec — second
concrete ISA-model pull (the table *is* a privileged-spec artifact).

### 9. `cv32e40p_load_store_unit` — BusOracle β, OBI rely, misaligned split, ≈mem

```systemverilog
module cv32e40p_load_store_unit #(parameter PULP_OBI = 0) (
    input  logic clk, rst_n,
    // OBI data master
    output logic data_req_o,   input logic data_gnt_i, data_rvalid_i,
    input  logic data_err_i, data_err_pmp_i,
    output logic [31:0] data_addr_o,  output logic data_we_o,
    output logic [3:0]  data_be_o,    output logic [31:0] data_wdata_o,
    input  logic [31:0] data_rdata_i,
    // EX-stage command interface
    input  logic data_we_ex_i,        input logic [1:0] data_type_ex_i,
    input  logic [31:0] data_wdata_ex_i,  input logic [1:0] data_reg_offset_ex_i,
    input  logic data_load_event_ex_i,    input logic [1:0] data_sign_ext_ex_i,
    output logic [31:0] data_rdata_ex_o,  input logic data_req_ex_i,
    input  logic [31:0] operand_a_ex_i, operand_b_ex_i,  input logic addr_useincr_ex_i,
    input  logic data_misaligned_ex_i,    output logic data_misaligned_o,
    input  logic [5:0] data_atop_ex_i,    output logic [5:0] data_atop_o,
    output logic p_elw_start_o, p_elw_finish_o,
    output logic lsu_ready_ex_o, lsu_ready_wb_o, busy_o);
```

Up to 2 outstanding OBI transactions (`DEPTH = 2`, a counter — internal,
L2-invisible). The RTL's own `ifdef`'d assertions are, read correctly, its
**rely**: `data_err_i = 0 ∧ data_err_pmp_i = 0` always (bus/PMP errors
unsupported — asserted, not handled), and `data_rvalid_i` only while
transactions are outstanding.

```lean
-- β: the memory side of OBI as an environment oracle beside σ.
-- β consumes the request history and decides gnt timing, rvalid timing, rdata.
structure ObiRely (β : BusOracle) : Prop where
  no_err       : …                    -- err lines held low (the RTL's own assumption)
  resp_matched : …                    -- rvalid only answers an accepted request, in order
  live         : …                    -- every request eventually granted; every grant
                                      -- eventually answered   (the L4 half)

structure ExRely : Prop := …
  -- EX command held stable until lsu_ready_ex_o; on data_misaligned_o the command is
  -- replayed next with data_misaligned_ex_i = 1 and operands advanced by 4
  -- (the replay is the CONTROLLER/ID-stage's obligation — see the honest note below)

-- (a) the split guarantee, purely on the bus ports
@[spec] theorem lsu_misaligned_split (β) (hβ : ObiRely β) :
    load_store_unit ⊨ᶜ ⟨ExRely, fun tr =>
      ∀ n, WordCmdAt tr n → (addrAt tr n).extractLsb' 0 2 ≠ 0 →
        FlagsAt tr n data_misaligned_o ∧
        ∃ m₁ m₂, n ≤ m₁ ∧ m₁ < m₂ ∧
          ObiTxAt tr m₁ (addrAt tr n)            (hiBE (addrAt tr n)) ∧
          ObiTxAt tr m₂ (align4 (addrAt tr n) + 4) (loBE (addrAt tr n))⟩
    -- halfword twin: split iff addr[1:0] = 3; bytes never split

-- (b) ≈mem: against a memory-like environment, the port behavior IS abstract memory
def AbstractMem := BitVec 32 → BitVec 8                       -- L3: spec-side, byte-addressed
def memSem : AbstractMem → MemCmd → AbstractMem × BitVec 32   -- RISC-V load/store semantics:
  -- byte/half/word at ANY alignment, sign-/zero-extension per data_sign_ext (incl. the
  -- 2'b10 "ones-extend/NaN-box" mode the RTL implements), no misaligned trap ever

@[spec] theorem lsu_mem_equiv (M₀ : AbstractMem) :
    load_store_unit ≈mem[obiMemOracle M₀] memSem
    -- reading: for every gnt/rvalid timing ObiRely allows the oracle, the stream of
    -- EX commands ↦ data_rdata_ex_o results equals running memSem from M₀
```

The ≈mem theorem is the crown of this entry: the byte-enable table, the
rotate-by-`wdata_offset` store alignment, the three sign-extension muxes and
the two-beat reassembly through `rdata_q` all disappear into "it is a
memory". **Honest scoping note:** the misaligned protocol is *split across
modules* — the LSU only raises `data_misaligned_o`; the second beat happens
because ID/EX replays the command with adjusted operands. So `ExRely` carries
that replay obligation, and the end-to-end "a misaligned load returns the
right bytes" theorem lives at core level, with this entry as its LSU lemma.
**Realizability twin:** under `ObiRely.live`, `lsu_ready_ex_o` is eventually
high after any command (no wedge), and both beats of a split complete —
bounded by 2 outstanding + grant latencies.
**NOTE (new vocabulary):** `BusOracle` β beside σ with a rely *structure*
(`⊨[β]`); `⊨ᶜ` with relies naming another module's behavior (`ExRely`);
`≈mem` equivalence to a spec-side semantics; trace-position helpers
(`ObiTxAt`, `WordCmdAt`) over the typed port record.
**Difficulty/deps:** hard — first real oracle user. `memSem` is the ISA
model's memory slice; sign-extension conventions come with it.

### 10. `cv32e40p_controller` — the contract style: exactly-once, interrupt boundary, stall-liveness

```systemverilog
module cv32e40p_controller import cv32e40p_pkg::*; #(
    parameter COREV_CLUSTER = 0, COREV_PULP = 0, FPU = 0) (
    input  logic clk, clk_ungated_i, rst_n,
    input  logic fetch_enable_i,   output logic ctrl_busy_o, is_decoding_o,
    // decoder verdicts in:  illegal/ecall/mret/dret/wfi/ebrk/fencei/csr_status _i …
    // decoder control out:  deassert_we_o
    input  logic instr_valid_i,    output logic instr_req_o,
    output logic pc_set_o,  output logic [3:0] pc_mux_o,  output logic [2:0] exc_pc_mux_o,
    // LSU: data_req_ex_i, data_we_ex_i, data_misaligned_i, data_load_event_i, data_err_i …
    // EX:  branch_taken_ex_i, mult_multicycle_i, apu_* dependency flags
    // IRQ: irq_req_ctrl_i, irq_sec_ctrl_i, irq_id_ctrl_i [4:0], irq_wu_ctrl_i
    output logic irq_ack_o,  output logic [4:0] irq_id_o, exc_cause_o,
    // debug req/mode/single-step …, wake_from_sleep_o
    // CSR commands out: csr_save_{if,id,ex}_o, csr_cause_o, csr_save_cause_o, csr_restore_*_o
    // forwarding selects + hazard inputs (reg_d_* match flags)
    output logic halt_if_o, halt_id_o, misaligned_stall_o, jr_stall_o, load_stall_o,
    input  logic id_ready_i, id_valid_i, ex_valid_i, wb_ready_i,
    output logic perf_pipeline_stall_o);
```

A 16-state FSM (`RESET … DECODE … FLUSH_EX/WB … XRET_JUMP … DBG_* …
DECODE_HWLOOP`) — every one of them proof-side, per L2; the specs below never
name a state. This is the entry the `⊨ᶜ` judgment exists for: nothing the
controller guarantees is unconditional — every guarantee leans on handshake
discipline from four neighbors (IF/prefetcher, decoder, EX/LSU, interrupt
controller).

```lean
def PipeRely : CtrlIns →ᵗ Prop := …
  -- neighbors keep the pipeline protocol: instr_valid_i stable until id_ready_i;
  -- decoder verdict lines are a function of the ID instruction; ex_valid/wb_ready
  -- rise per their own contracts; irq_req_ctrl_i held until irq_ack_o (int-controller
  -- discipline); data_misaligned_i only in response to an LSU word/half command

-- (a) exactly-once instruction accounting — WITH the ghost-state note
@[spec] theorem controller_exactly_once :
    controller ⊨ᶜ ⟨PipeRely, fun tr =>
      ∃ ledger : InstrLedger tr,          -- GHOST: auxiliary spec state over the port trace
        (∀ i ∈ ledger.tokens, ledger.retired i + ledger.squashed i = 1) ∧
        (∀ i ∈ ledger.tokens, ledger.squashed i = 1 →
           ledger.cause i ∈ ({.takenBranch, .irq, .exception, .debugEntry, .flush} : Set _))⟩

-- (b) interrupt boundary: the taking edge is a clean cut (from the DECODE-state
--     IRQ block of the RTL: ack, cause, save-ID, PC redirect, halts — one edge)
@[spec] theorem controller_irq_boundary :
    controller ⊨ᶜ ⟨PipeRely, Sv.onPosedge fun s s' =>
      s.irq_ack_o →
        s.csr_save_cause_o ∧ s.csr_cause_o = 1#1 ++ s.irq_id_o ∧ s.csr_save_id_o ∧
        s.pc_set_o ∧ s.pc_mux_o = PC_EXCEPTION ∧
        s.halt_if_o ∧ s.halt_id_o ∧ ¬s.is_decoding_o⟩   -- interrupted instr not half-retired
-- plus the handshake bijection: one irq_ack_o pulse per taken request, id echoed exactly

-- (c) stall-liveness: no permanent stall without cause (the L4 twin of every
--     halt/stall output this module owns)
theorem controller_no_wedge :
    controller ⊨ᶜ ⟨PipeRely ∧ EnvLive, fun tr =>
      ∀ n, ∃ m, n ≤ m ∧ (ProgressAt tr m ∨ BlockedForCause tr m)⟩
  -- EnvLive: neighbors are live (fetch eventually valid, ex_valid/wb_ready recur,
  --          LSU responses arrive — ultimately entry 9's ObiRely.live)
  -- ProgressAt: an ID-stage handshake fires (instruction advances)
  -- BlockedForCause: sleep awaiting wake event / WFI / debug halted / fetch_enable low
  --   — every stalled cycle is attributable to a named, port-visible cause
```

**The ghost-state note (load-bearing):** ports carry no instruction identity,
so "each instruction retires exactly once" is not directly a port predicate.
`InstrLedger` is *auxiliary spec state*: tokens minted at ID-acceptance
handshakes (`instr_valid_i ∧ id_ready_i`), discharged by retirement
(`id_valid_i` reaching EX/WB per the handshake chain) or by a squash event
(`pc_set_o`-with-cause, `deassert_we_o`, halts). It is constructed *from the
port trace* — never from RTL internals — so L2 survives; but it is genuinely
new surface vocabulary, and the alternative (a quantifier-only port formula)
is technically expressible and humanly unreadable. The ledger is also exactly
what the core-level `minstret`/RVFI cross-check will consume.
**Difficulty/deps:** the hardest entry; needs `⊨ᶜ`, ghost state, and
recurrence liveness at once, and its rely is only fully groundable once
entries 5–9's guarantees exist to instantiate it (contract composition). The
squash-cause set and the save-PC selection are privileged-ISA facts (which
instruction is "the interrupted one") — ISA model again.

---

## A. New surface vocabulary inventory (consolidated)

What this gallery demands beyond `docs/sv-spec-surface.md`, each with a
one-line design sketch and its consumers:

1. **`⊨ᶜ` — rely-guarantee contract judgment over port traces.**
   `m ⊨ᶜ ⟨R, G⟩` elaborates to `∀ σ stim tr, Runs m σ stim tr → R tr.inputs →
   G tr` — R constrains only input-port history, G the whole trace; a
   composition rule discharges one module's R from a neighbor's G.
   Needed by: 3 (flush discipline corollary), 6 (stability rely), 9 (ExRely/
   ObiRely), 10 (PipeRely — the flagship).
2. **Ghost/auxiliary spec state.** `∃ ledger : Ghost tr, …` — spec-side
   accounting *derived from the port trace* (tokens, transaction ledgers,
   shadow queues); introduction/stepping combinators plus the L2 guard: a
   ghost may read ports only. Needed by: 10 (instruction ledger), 9
   (outstanding-transaction ledger inside `≈mem`'s proof-facing form), 3
   (pushes/pops sequences are a degenerate ghost).
3. **Environment oracles beside σ.** `BusOracle β` (and later an IRQ oracle):
   deterministic input-resolvers `history → cycle inputs`, with rely
   *structures* (`ObiRely β`: safety + liveness fields); `m ⊨[β] P` and
   quantification `∀ β, ObiRely β → …`. Needed by: 9 (data OBI), 10 (EnvLive
   grounds in the instruction-side bus), later the prefetcher.
4. **Spec-side DSLs as data (L3 made concrete).** `CsrBehavior` table (8),
   `DecodeRow`/`decodeTable` (7), `AbstractMem`/`memSem` (9), `Rv.divRem` and
   the `aluBaseSem` op table (5, 6). One design rule: these live in (or are
   generated from) the ISA model, not per-gallery-entry, so RTL conformance
   and ISA semantics cannot drift apart.
5. **Typed per-module port records with parametric widths.** Generated
   `Ins`/`Outs` structures, field names verbatim from the RTL, widths as
   functions of parameters (`BitVec (Nat.clog2 LEN)`, `BitVec (ADDR_DEPTH+1)`),
   SV package enums as Lean inductives (`AluOp`, `csr_num_e`, `PrivLvl_t`).
   Needed by: every entry; prerequisite for legible trace predicates
   (`tr.irq_ack_o n`, `s.csr_addr_i`).
6. **The revived `⊨tx`.** Upgraded from SV gallery ex. 10's `Sv.transaction`:
   a structure `{rely, request, response, latency, holdUntil}` — latency
   bounds bake the realizability twin into the judgment; `holdUntil` captures
   valid-until-ready output discipline. Needed by: 6 (flagship), 5 (div ops at
   the ALU boundary), 9 (per-access view of the LSU).
7. **`⊑@clk[areset rn] model via Rel` — refinement, generalized thrice.**
   Input records per cycle; output *relation* `Rel : ModelState → Ins → Outs →
   Prop` (Mealy, partial — garbage ports unconstrained); asynchronous
   active-low reset qualifier (level-sensitive, unclocked — M0's sampled
   `[from rst]` does not describe any CV32E40P module). Needed by: 3, 4; later
   every golden-model refinement in this core.
8. **`≈mem` — equivalence to an abstract memory semantics.** Command-stream
   observational equality between a module's port behavior under a
   memory-like oracle and a spec-side `memSem`; the statement form for "this
   bus widget is transparent". Needed by: 9 (flagship); later the prefetcher/
   OBI interface pair.
9. **Wildcard-pattern decode vocabulary.** `InstrPat` (mask/value) with
   `matches`; partial-record agreement `▷` ("the row constrains these
   outputs"); table-completeness and `unique`-disjointness obligations.
   Core-semantics prerequisite: `case … inside` (LRM §12.5.4) — **not**
   `casez`, which this RTL never uses. Needed by: 7; the `unique case`
   priority semantics also appears in 3 (`unique case (1'b1)`) and 8.
10. **Recurrence liveness + attribution.** `∀ n, ∃ m ≥ n, Progress ∨
    BlockedForCause` — infinite-trace recurrence (SV gallery ex. 19's
    machinery) plus *cause attribution* (every non-progress suffix names a
    port-visible reason). Needed by: 10; the bounded variants by 6, 9.
11. **Per-state invariants are PROOF-side only (reaffirmed).** FSM states
    (controller's 16, alu_div's 3), pointers, and counters appear exclusively
    in `Sv.invariant`-style proof lemmas; the surface never grows a judgment
    that mentions them. Consumed silently by: 3, 4, 6, 8, 9, 10.

## B. ISA-model dependency map

Which entries need the RV32IMC+privileged Lean model, and which stand alone:

| Entry | ISA model needed? | What exactly |
|---|---|---|
| 1 ff_one | **No** | pure combinatorics |
| 2 popcnt | **No** | pure combinatorics |
| 3 fifo | **No** | generic queue semantics |
| 4 register_file | **No** | generic memory semantics (x0 is a local fact) |
| 5 alu | **Borderline** | RHS op table = the model's execute-stage arithmetic; stateable standalone but should be *the same defs* |
| 6 alu_div | **Yes (M slice)** | `Rv.divRem` conventions (div-by-zero, overflow) |
| 7 decoder | **Yes (encodings)** | `decodeTable` = the ISA encoding tables; must share a source of truth with the model's decoder |
| 8 cs_registers | **Yes (privileged)** | WARL legalization, trap-entry tuple, mret/dret = privileged spec v1.11 content |
| 9 load_store_unit | **Yes (memory slice)** | `memSem`: load/store + sign-extension semantics |
| 10 controller | **Yes (privileged + stream)** | retirement/squash causes, interrupted-instruction identity, interrupt priority |

The argument for building the ISA model early, in one paragraph: entries 1–4
are self-contained and can drive the *mechanism* work (parametric designs,
refinement-via, async reset) immediately — but every entry from 5 up leans on
some slice of the ISA model, and the three hardest (8, 9, 10) lean on the
privileged part. Worse, four different spec-side artifacts (op table, div
conventions, decode table, CSR table) are all *projections of the same model*;
writing them per-entry and reconciling later is how conformance suites drift.
Build the RV32IMC+privileged model first as ordinary Lean definitions (L3),
generate `decodeTable`/`csrTable`/`aluBaseSem` from it, and the gallery's
RHSs come for free — plus the model is the golden model the eventual
core-level `⊑` theorem (the cross-language payoff, SV gallery ex. 10 writ
large) refines against.

## What the RTL corrected (honest notes)

Assumptions the actual files contradicted, recorded so the next reader specs
from the RTL too:

- **No `casez` exists in CV32E40P.** The decoder's wildcard dispatch is
  `unique case … inside` (+ plain `unique case`); the fifo and controller use
  `unique case (1'b1)` priority style. The planned "casez vocabulary" is
  really *`case inside` + `unique`* vocabulary.
- **popcnt is not parametric** (hardcoded 32-bit), while ff_one is — the
  ∀-width crown jewel budget goes to ff_one, fifo, and alu_div only.
- **register_file's `ADDR_WIDTH` parameter is decorative.** The code indexes
  `raddr[5]`/`raddr[4:0]` unconditionally, `NUM_WORDS = 2^(ADDR_WIDTH−1)`,
  and the core instantiates `ADDR_WIDTH = 6`. Quantify over addresses, not the
  parameter. Also found only by reading: write port **B beats A** on
  collisions; reads are combinational over pre-edge state (read-during-write
  returns the old value); with `FPU = 0`, reads of addresses ≥ 32 return 0 and
  writes there are dropped; the "Mask top bit of write address" comment is
  stale — no masking happens.
- **Plain `ALU_ADD` routes through the shifter** (`result = (a+b) >>>
  bmask_b_i`): base-ISA ALU conformance is false without the
  `bmask_b_i = 0` (and VEC_MODE32, non-clpx) hypothesis — the `Rv32Base`
  benign-context predicate is mandatory, not defensive.
- **alu_div's boundary is not "divide a by b".** Operands arrive pre-swapped
  and pre-shifted from the ALU; `OpBIsZero_SI` is consumed live mid-division
  (stability is a rely); `OutVld_SO` is also high in IDLE; and the divider is
  where `ready_o` of the whole ALU comes from.
- **Every clocked module uses asynchronous active-low reset** (`negedge
  rst_n` in sensitivity lists). M0's `[from rst]` sampled-reset qualifier
  fits none of them; the `[areset rn]` qualifier is new, required vocabulary.
- **ff_one is broken at `LEN = 1`** (`no_ones_o` stuck at 1): the crown jewel
  honestly starts at `LEN ≥ 2`.
- **The LSU's error inputs are asserted, not handled** (`data_err_i`,
  `data_err_pmp_i` assumed 0 by the RTL's own SVA; PMP dead) — bus-error
  behavior belongs in the rely, and a spec claiming error handling would be
  specifying fiction. The misaligned second beat is the ID/EX stage's replay,
  not the LSU's — the LSU-local guarantee is conditional on `ExRely`.
- **The fifo's `DEPTH = 0` pass-through mode exists in generate but is
  asserted away** (`assert (DEPTH > 0)`), and `flush_but_first_i` (keep only
  the head) is a queue operation folklore FIFOs don't have.
- **cs_registers hides nothing:** trap entry beats a same-cycle SW CSR write
  (write-logic ordering); `mtvec` stores only the top 24 bits + a 1-bit mode
  (256-byte alignment is structural); `mcause` keeps just `{bit 31, bits
  4:0}`; `mepc` clears bit 0. All of it is table data, none of it axioms.
