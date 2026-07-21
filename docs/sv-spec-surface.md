# SystemVerilog spec surface — target ergonomics (normative examples)

**Status: design target** (see "Implementation status" below for what is being
built right now). This document is the complete SV gallery and plays the same role
as `docs/spec-surface.md` does for Python: when the SV lane is built, these
statements must elaborate, and new examples should be written in this style.
Examples 1–10 exercise the core judgment family; examples 11–19 cover
elaboration-time structure, net resolution, level-sensitive logic, data layout,
interfaces/protocols, data-carrying SVA, class polymorphism, process control, and
liveness.

Scope reminder: **full IEEE 1800 semantics, not just the synthesizable subset** —
the event-driven stratified scheduler, delays, `initial`/`fork`/`join`, mailboxes,
classes, constrained randomization, SVA, DPI. We model *simulation semantics* (what
the LRM prescribes for a simulator), not hardware netlists; where the two diverge
(X-optimism, below) the divergence is a documented feature of the model, not a bug.

## Pipeline (mirrors the Python lane)

slang (`--ast-json`) → standardized envelope → `load_design counter from
"Examples/sv/counter.sv.json"` → typed wrappers generated from elaboration info
(a `State` structure with one field per signal, port types as `LVec n`), plus
`// lean[ ... // ]` comment blocks spliced into companions, `@[spec]`, and an
`sv_prove` tactic front door.

## Semantic objects

- **4-state values from day one**: `Logic ::= l0 | l1 | lx | lz`; vectors
  `LVec n` (arrays of `Logic`). `LVec.known : LVec n → Option (BitVec n)`
  embeds the X/Z-free case, where `bv_decide` automation lives. `BitVec` literals
  coerce into `LVec` positions in specs.
- **Design** = elaborated module hierarchy: processes, variables/nets, sensitivity.
- **Oracles**: a run is a *deterministic* function of
  `(design, stimulus, σ : ScheduleOracle, ρ : RandOracle)` — σ resolves the LRM's
  deliberate same-region ordering freedom, ρ resolves `randomize()`/`$urandom`.
  Quantify over σ ⇒ "for all legal schedules"; plug in a concrete σ ⇒ executable
  simulator (differentially tested against Xcelium).
- **Trace** `tr` = the observable history: signal values over (time, delta) points,
  `$display` output, termination status.

## The judgment family

| Surface | Reading |
|---|---|
| `f(a, b) ==> v` | SV `function`: same total-correctness arrow as the Python lane |
| `m / stim ⇓[σ] tr` | design `m` under stimulus `stim` and schedule `σ` yields trace `tr` |
| `m ⊨ P` | `∀ stim σ tr, m / stim ⇓[σ] tr → P stim tr` — for **all** inputs and **all** legal schedules |
| `m ⊨sva p` | the design satisfies its extracted SVA property `p` (same ∀ stim σ) |
| `Sv.Deterministic m` | all schedules give the same observable trace (race-freedom) |
| `m ⊑@clk model` | cycle-accurate refinement of a Lean transition function (golden model); `⊑@clk[from rst]` starts at the first edge sampling `rst` = 1 |
| `Sv.FinishesBy m t` | terminates (`$finish`) by time `t` for every schedule |

**Implementation status.** The M0 slice is in progress per `docs/sv-design-m0.md`:
a cycle-level scheduler core, five gallery examples (`adder`, `counter`,
`race_blk`, `swap_nba`, `xsel`) extracted into Lean, and a differential harness
against Xcelium. The M0 cycle-level slice of the judgment family is now real
(`LeanModels/Sv/Surface.lean` + `Delab.lean`): `d ⊨ P` elaborates to the
fuel-free all-schedule judgment (∀ σ stim tr, `Runs d σ stim tr → P d stim tr`,
with `Sv.spec` for plain stimulus/trace predicates and `Sv.onPosedge` for
adjacent-snapshot relations, startup state included); `d / stim ⇓[σ] tr` is the
run judgment (`Runs`, fuel existentially packaged with fuel-monotonicity making
the witness irrelevant); `Sv.Deterministic` is exactly as promised above; and
`d ⊑@clk[from rst] model` is cycle refinement from the first sampled reset
(M0 form: single observed output port, `Bool` reset input per cycle, ∀ over the
pre-reset abstract state — which is what makes `[from rst]` load-bearing). The
M0 theorems are restated in these forms as corollaries of the raw `Proofs.lean`
theorems — `swap_nba_swaps` (⊨/onPosedge, example 3's `swap_nba_spec` shape),
`swap_nba_det`/`counter_det` (`Sv.Deterministic`), `race_blk_race` (two-schedule
⇓-witnesses), and `counter_refines : counterDesign ⊑@clk[from rst] counterModel`
(example 2, verbatim) — with goal-state delaborators printing every judgment
back in its surface notation (`#guard_msgs`-pinned in `Delab.lean`).
`#sv_check <design> [[clk := 1, rst := 1], …] (under σ)? shows count = [x, 0, 1]`
guards concrete interpreter runs in surface syntax (`Tests.lean` demos), and a
first-cut `sv_prove [raw, bridges…]` closes the four surface corollary shapes
(exact restatements, Deterministic-from-totality, ⊨ from hypothesis-form raw
theorems, ⊑@ via the reset-column rule). Everything else in this document —
in particular `Sv.comb`, `⊨sva`, `Sv.FinishesBy`, event-driven time, and the
function arrow — remains design-target.

Preconditions stay ordinary hypotheses. Temporal spec helpers (`Sv.at`,
`Sv.always`, `Sv.eventually`, `Sv.onPosedge`) live in the spec prelude.

## The gallery

### 1. Combinational module — and why 4-state shows up immediately

```systemverilog
module adder (input  logic [7:0] a, b,
              output logic [7:0] s);
  assign s = a + b;
endmodule
```
```lean
@[spec] theorem adder_spec (a b : BitVec 8) :
    adder ⊨ Sv.comb fun ins outs => ins.a = a → ins.b = b → outs.s = a + b
```

The binders are `BitVec 8` — i.e. the theorem speaks about **known** (X/Z-free)
inputs, and the coercion into 4-state ports makes that hypothesis explicit. Feed an
X and the LRM says `s` is X-contaminated — totally: a single x (or z) bit in either
operand makes *all eight* result bits x (LRM §11.4.3), so `LVec.addX` in the general
4-state statement (`outs.s = LVec.addX ins.a ins.b`) is the whole-vector collapse,
not a bit-precise carrying add; it is available but rarely what you want. `Sv.comb`
packages "after combinational settling" (Active-region convergence, which is itself
a theorem obligation: the always/assign network is acyclic).

### 2. Sequential module — golden-model refinement

```systemverilog
module counter (input  logic clk, rst,
                output logic [7:0] count);
  always_ff @(posedge clk)
    if (rst) count <= '0;
    else     count <= count + 8'd1;
endmodule
```
```lean
def counterModel (s : BitVec 8) (rst : Bool) : BitVec 8 :=
  if rst then 0 else s + 1

@[spec] theorem counter_refines : counter ⊑@clk[from rst] counterModel
```

`⊑@clk[from rst]` says: sample the design at each `posedge clk` from the first edge
at which `rst` is sampled 1; from there on the sampled outputs follow the Lean
transition function. The qualifier is not decoration: in 4-state simulation `count`
is X from time 0 through every pre-reset edge (X + 1 = X), so no `BitVec 8` state
corresponds to the startup trace — reset is what establishes the abstraction (a
2-state, zero-initializing simulator coincidentally matches `counterModel` with
`s0 = 0`, but the LRM does not). The spec *is* an ordinary Lean program — this is the
refinement shape that later scales to "SV module ⊑ Python golden model". Wrap-around
at 256 is inherited from `BitVec 8` arithmetic — the model can't accidentally
promise unbounded counting.

### 3. The crown jewel of full semantics — races and the schedule oracle

```systemverilog
module race_blk (input logic clk);          // blocking assigns: a race
  logic [7:0] a = 8'd1, b = 8'd2;
  always @(posedge clk) a = b;
  always @(posedge clk) b = a;
endmodule

module swap_nba (input logic clk);          // nonblocking: correct swap
  logic [7:0] a = 8'd1, b = 8'd2;
  always @(posedge clk) a <= b;
  always @(posedge clk) b <= a;
endmodule
```
```lean
theorem race_blk_racy : ¬ Sv.Deterministic race_blk := by
  sv_witness                       -- exhibits two schedules: (a,b) ↦ (2,2) vs (1,1)

@[spec] theorem swap_nba_spec :
    swap_nba ⊨ Sv.onPosedge fun s s' => s'.a = s.b ∧ s'.b = s.a

theorem swap_nba_det : Sv.Deterministic swap_nba
```

*This* is what the full (non-synthesizable-subset) semantics buys: the LRM
deliberately leaves same-region process order unspecified, so `race_blk`'s outcome
depends on σ — both `always` blocks read and write in the Active region, and the
two orders give `(2,2)` and `(1,1)`. A simulator shows you *one* schedule;
`¬ Sv.Deterministic` proves the bug exists in *some* legal schedule, and
`Sv.Deterministic` proves its absence in **all** of them — a theorem no simulator
can check. The NBA version is deterministic because reads happen in the Active
region and updates in the NBA region, by construction of the scheduler.

### 4. Event-driven time — delays, `initial`, `$finish`

```systemverilog
module tb;
  logic [7:0] x = 8'd0;
  initial begin
    #10 x = 8'd42;
    #10 x = x + 8'd1;
    #5  $finish;
  end
endmodule
```
```lean
theorem tb_timeline : tb ⊨ Sv.always fun t s =>
    (t < 10 → s.x = 0) ∧ (10 ≤ t ∧ t < 20 → s.x = 42) ∧ (20 ≤ t → s.x = 43)

theorem tb_finishes : Sv.FinishesBy tb 25
```

Purely a testbench construct — no hardware meaning at all — and exactly the kind of
program the "full semantics" decision exists for. Time is part of the trace;
`Sv.always` quantifies over trace points, sampling the Postponed-region
(end-of-timestep) value at each time. That definition is what makes the `10 ≤ t` /
`20 ≤ t` boundaries above true: *within* the timestep at exactly `t = 10`, a
same-time process scheduled before the assignment still reads 0 (the same
Preponed/Postponed sampling distinction SVA makes in example 6).

### 5. X-optimism — we model the LRM, and prove it honestly

```systemverilog
module xsel (input  logic sel,
             input  logic [7:0] a, b,
             output logic [7:0] y);
  always_comb
    if (sel) y = a;
    else     y = b;
endmodule
```
```lean
@[spec] theorem xsel_known (s : Bool) (a b : BitVec 8) :
    xsel ⊨ Sv.comb fun ins outs =>
      ins.sel = s → ins.a = a → ins.b = b → outs.y = if s then a else b

theorem xsel_xoptimism (a b : BitVec 8) :          -- sel = X takes the ELSE branch
    xsel ⊨ Sv.comb fun ins outs =>
      ins.sel = Logic.lx → ins.a = a → ins.b = b → outs.y = b
```

Per the LRM (§12.4: zero, x, or z is not-true), an `if` condition evaluating to X
or Z is treated as false — simulation takes the `else` branch even though real
hardware might do anything ("X-optimism"). The second theorem states this
*faithfully*, and it has an identical `Logic.lz` twin. That our semantics can prove it is a
feature: it's the truth about simulation, and the gap between simulation and
hardware becomes a stateable, analyzable property instead of folklore.

### 6. SVA — in-language properties become all-schedule theorems

```systemverilog
module handshake (input  logic clk, rst, req,
                  output logic ack);
  always_ff @(posedge clk) ack <= req & ~rst;

  p_req_ack: assert property (@(posedge clk) disable iff (rst) req |-> ##1 ack);
endmodule
```
```lean
@[spec] theorem handshake_sva : handshake ⊨sva handshake.props.p_req_ack

-- which unfolds to the honest temporal statement (note the reset hypothesis):
example : handshake ⊨ Sv.onPosedgeIdx fun tr n =>
    Sv.neverDuring tr.rst n (n + 1) →   -- rst never true at ANY point in the
    tr.req n → tr.ack (n + 1)           -- attempt window, on CURRENT values
```

The property text stays in the source where the simulator also checks it; the
theorem upgrades it from "held on the schedules and stimuli we simulated" to "holds
for every stimulus and every legal schedule". SVA sampling semantics (Preponed-
region values) is part of the scheduler model, so `|->` and `##1` mean exactly what
they mean in simulation — with one exemption the LRM itself makes: `disable iff`
reads `rst` asynchronously, on *current* (not Preponed-sampled) values, at any point
during the attempt (§16.12). Hence the `Sv.neverDuring` hypothesis rather than the
sampled `¬tr.rst n`: a `rst` pulse inside the window discards the attempt even when
the edge-`n` sample of `rst` was 0.

### 7. Testbench concurrency — `fork/join` and mailboxes

```systemverilog
module pc;
  mailbox #(int) mb = new();
  int out[$];
  initial fork
    begin : producer
      for (int i = 0; i < 4; i++) mb.put(i);
    end
    begin : consumer
      repeat (4) begin int v; mb.get(v); out.push_back(v); end
    end
  join
endmodule
```
```lean
theorem pc_fifo : pc ⊨ Sv.atEnd fun s => s.out = [0, 1, 2, 3]
```

For **every** interleaving of producer and consumer (σ ranges over all of them,
including blocking `get` wakeups), the queue comes out in order — single-producer
single-consumer FIFO order preservation, proved over the scheduler, not sampled by
one run.

### 8. Constrained randomization — the random oracle

```systemverilog
class Packet;
  rand bit [7:0] len;
  constraint legal { len inside {[1:15]}; }
endclass

module rnd;
  Packet p;
  initial begin
    p = new();
    if (!p.randomize()) $fatal(1, "randomize failed");
  end
endmodule
```
```lean
theorem rnd_len_legal : rnd ⊨∀ρ Sv.atEnd fun s =>
    1 ≤ s.p.len.toNat ∧ s.p.len.toNat ≤ 15
```

`randomize()` is relational: it picks *some* solution of the constraint set via the
random oracle ρ. `⊨∀ρ` quantifies over every draw — so downstream correctness
theorems hold for every value randomization can produce, which is the theorem a
constrained-random testbench actually needs.

### 9. DPI — the honest axiomatic boundary

```systemverilog
import "DPI-C" function int c_hash(int x);

module dpi_use (input logic [31:0] x, output logic [31:0] h);
  assign h = c_hash(x);
endmodule
```
```lean
theorem dpi_use_spec (hc : ∀ x, (c_hash.contract x).nonneg) :
    dpi_use ⊨ Sv.comb fun ins outs => (outs.h.toBitVec).sle 0x7FFFFFFF ...
```

Foreign C code gets a *contract*, not a definition — theorems about designs using
DPI are explicitly conditional on it. The correct semantics of an FFI boundary, not
a compromise.

### 10. The payoff — cross-language refinement

```systemverilog
module tri_acc (input  logic clk, rst, start,
                input  logic [31:0] n,
                output logic [31:0] result,
                output logic        done);
  logic [31:0] i, acc, n_q;
  typedef enum logic [0:0] { IDLE, RUN } state_e;
  state_e state;
  always_ff @(posedge clk) begin
    if (rst) begin state <= IDLE; done <= 1'b0; end
    else case (state)
      IDLE: if (start) begin i <= 32'd0; acc <= 32'd0; n_q <= n; done <= 1'b0; state <= RUN; end
      RUN:  if (i > n_q) begin result <= acc; done <= 1'b1; state <= IDLE; end
            else begin acc <= acc + i; i <= i + 32'd1; end
    endcase
  end
endmodule
```
```lean
-- tri(n) ==> r is the PYTHON judgment for Examples/python/tri.py
theorem tri_acc_refines_python (n : PyInt) (h0 : 0 ≤ n) (hbound : n < 2 ^ 15)
    (hpy : tri(n) ==> r) :
    tri_acc ⊨ Sv.transaction
      (request  := fun ins => ins.start ∧ ins.n = BitVec.ofInt 32 n)
      (response := fun outs => outs.done ∧ outs.result = BitVec.ofInt 32 r)
```

Both lanes meet in one theorem: the Python program is the golden model, the SV
design is the implementation, and the statement is "whenever `start` is pulsed with
`n`, the module eventually raises `done` with exactly the value the Python program
returns". Latching `n` into `n_q` at acceptance is what makes that a ∀-stimulus
theorem — compare against the live port instead and a stimulus that changes `n`
mid-transaction falsifies it. The bound is hardware honesty twice over: it keeps
32-bit accumulation exact, and it keeps the exit guard `i > n_q` satisfiable in
32 bits (at `n = 2³² − 1`, `done` would never rise). This is
the theorem shape the whole project converges on, and everything above — shared
spec prelude, `Py*`/`BitVec` bridges, oracle quantification — exists so that it is
*this short*.

### 11. Generate loops — one theorem for every parameter value

```systemverilog
module full_add (input logic a, b, cin, output logic s, cout);
  assign {cout, s} = a + b + cin;
endmodule

module rca #(parameter int W = 8)
            (input  logic [W-1:0] a, b,
             output logic [W-1:0] s,
             output logic         cout);
  logic [W:0] c;
  assign c[0] = 1'b0;
  for (genvar i = 0; i < W; i++) begin : g
    full_add fa (.a(a[i]), .b(b[i]), .cin(c[i]), .s(s[i]), .cout(c[i+1]));
  end
  assign cout = c[W];
endmodule
```
```lean
@[spec] theorem rca_spec (W : Nat) (hW : 0 < W) (a b : BitVec W) :
    (rca W) ⊨ Sv.comb fun ins outs =>
      ins.a = a → ins.b = b →
      outs.s = a + b ∧
      outs.cout = (a.zeroExtend (W + 1) + b.zeroExtend (W + 1)).msb
```

Elaboration is a *Lean function of the parameters*: `rca : Nat → Sv.Design`, and the
generate loop unrolls by computation. So one theorem quantifies over **every**
instantiation width — proved by induction over the generate structure (the carry
chain), which is something neither simulation (fixed `W`) nor typical model checkers
(fixed instance) can express at all.

### 12. Nets are not variables — multiple drivers, Z, and resolution

```systemverilog
module tribuf (input logic en, input logic [7:0] d, inout wire [7:0] bus);
  assign bus = en ? d : 8'bz;
endmodule

module bus2 (input  logic en0, en1,
             input  logic [7:0] d0, d1,
             output logic [7:0] y);
  wire [7:0] bus;
  tribuf b0 (.en(en0), .d(d0), .bus(bus));
  tribuf b1 (.en(en1), .d(d1), .bus(bus));
  assign y = bus;
endmodule
```
```lean
@[spec] theorem bus2_exclusive (d0 : BitVec 8) :
    bus2 ⊨ Sv.comb fun ins outs =>
      ins.en0 = 1 → ins.en1 = 0 → ins.d0 = d0 → outs.y = d0

theorem bus2_conflict (d0 d1 : BitVec 8) (i : Fin 8) (hne : d0[i] ≠ d1[i]) :
    bus2 ⊨ Sv.comb fun ins outs =>
      ins.en0 = 1 → ins.en1 = 1 → ins.d0 = d0 → ins.d1 = d1 →
      outs.y[i] = Logic.lx

theorem bus2_float :
    bus2 ⊨ Sv.comb fun ins outs => ins.en0 = 0 → ins.en1 = 0 → outs.y.allZ
```

A `wire` with several drivers resolves per bit (agree → the value; one drives Z →
the other wins; conflict → X; nobody drives → Z). Variables (`logic` in a process)
forbid multiple drivers outright. This net/variable split — and the resolution
function — is core LRM semantics the synthesizable-subset view tends to gloss over;
here each resolution case is its own small theorem.

### 13. Level-sensitive logic — the transparent latch

```systemverilog
module dlatch (input logic en, input logic [7:0] d, output logic [7:0] q);
  always_latch
    if (en) q = d;
endmodule
```
```lean
@[spec] theorem dlatch_transparent (d : BitVec 8) :
    dlatch ⊨ Sv.comb fun ins outs => ins.en = 1 → ins.d = d → outs.q = d

@[spec] theorem dlatch_hold :
    dlatch ⊨ Sv.stableWhile (fun s => s.en = Logic.l0) (·.q)
```

Two theorems, two temporal regimes: transparent (combinational follow) while `en`
is high, held constant while `en` is low — `Sv.stableWhile` is the prelude helper
for "this signal does not change on any trace segment where that predicate holds".
Neither edge-triggered nor purely combinational: a semantics tier of its own.

### 14. Packed structs — data layout as a theorem

```systemverilog
typedef struct packed {
  logic [3:0]  tag;     // bits [15:12]
  logic [11:0] addr;    // bits [11:0]
} req_t;

module pack_demo (input  req_t r,
                  output logic [15:0] bits,
                  output logic [3:0]  t);
  assign bits = r;
  assign t    = r.tag;
endmodule
```
```lean
@[spec] theorem pack_layout (tag : BitVec 4) (addr : BitVec 12) :
    pack_demo ⊨ Sv.comb fun ins outs =>
      ins.r.tag = tag → ins.r.addr = addr →
      outs.bits = tag ++ addr ∧ outs.t = tag
```

A packed struct *is* its concatenation (first field = most significant bits), and
the wrapper generator turns `req_t` into a Lean structure whose bit-image is
`tag ++ addr`. Layout bugs — the classic silent killer at design boundaries —
become type-checked equalities.

### 15. Interfaces and protocols — stream conservation

```systemverilog
interface stream_if #(parameter int W = 8);
  logic         valid, ready;
  logic [W-1:0] data;
  modport src (output valid, data, input  ready);
  modport dst (input  valid, data, output ready);
endinterface

module skid_buf (input logic clk, rst, stream_if.dst in, stream_if.src out);
  logic full;
  logic [$bits(in.data)-1:0] held;
  always_ff @(posedge clk) begin
    if (rst) full <= 1'b0;
    else if (!full && in.valid) begin held <= in.data; full <= 1'b1; end
    else if (full && out.ready) full <= 1'b0;
  end
  assign in.ready  = ~full;
  assign out.valid = full;
  assign out.data  = held;
endmodule
```
```lean
-- Sv.beats tr ifc = the list of data values sampled on cycles where valid ∧ ready
@[spec] theorem skid_no_loss_no_reorder :
    skid_buf ⊨ Sv.afterReset fun tr => Sv.beats tr.out <+: Sv.beats tr.in

@[spec] theorem skid_capacity :
    skid_buf ⊨ Sv.afterReset fun tr =>
      (Sv.beats tr.in).length ≤ (Sv.beats tr.out).length + 1
```

The protocol-level spec: the sequence of beats leaving is a **prefix** (`<+:`) of
the sequence of beats entering — no loss, no reorder, no invention — and the buffer
holds at most one in-flight beat. List-prefix over extracted beat sequences is the
clean Lean shape for stream-processing hardware, and it composes: chaining two
proved-conservative stages is `List.IsPrefix.trans`. (`held` is sized with
`$bits(in.data)` rather than a hardcoded `[7:0]`: a fixed width compiles silently
but truncates data whenever the interface is instantiated with `W != 8`.)

### 16. SVA with local variables — data integrity through a pipeline

```systemverilog
module pipe2 (input  logic clk,
              input  logic valid_in,  input  logic [7:0] d_in,
              output logic valid_out, output logic [7:0] d_out);
  logic v1; logic [7:0] s1;
  always_ff @(posedge clk) begin
    v1 <= valid_in;  s1 <= d_in + 8'd1;
    valid_out <= v1; d_out <= s1 + 8'd1;
  end

  property p_integrity;
    logic [7:0] v;
    @(posedge clk) (valid_in, v = d_in) |-> ##2 (valid_out && d_out == v + 8'd2);
  endproperty
  a_integrity: assert property (p_integrity);
endmodule
```
```lean
@[spec] theorem pipe2_sva : pipe2 ⊨sva pipe2.props.a_integrity

-- which unfolds to the quantified temporal statement:
example : pipe2 ⊨ Sv.onPosedgeIdx fun tr n =>
    ∀ v, tr.valid_in n → tr.d_in n = v →
      tr.valid_out (n + 2) ∧ tr.d_out (n + 2) = v + 2
```

SVA local variables (`v = d_in` captured at match time) are how real assertions
track data, not just control. In the Lean unfolding the local variable becomes an
ordinary `∀` — the two `+1` stages compose to `+2` end-to-end, per in-flight datum.

### 17. Classes and virtual dispatch — the OOP tier

```systemverilog
class Shape;
  virtual function int area(); return 0; endfunction
endclass

class Square extends Shape;
  int side;
  function new(int s); side = s; endfunction
  virtual function int area(); return side * side; endfunction
endclass

module poly;
  int a;
  initial begin
    automatic Square q = new(5);
    automatic Shape  s = q;   // upcast
    a = s.area();             // dynamic dispatch
  end
endmodule
```
```lean
theorem poly_dispatch : poly ⊨ Sv.atEnd fun s => s.a = 25
```

The theorem pins *dynamic* dispatch: a static reading of `s.area()` gives 0. Class
objects live on a garbage-collected handle heap in the semantics (the same heap
machinery the Python lane's mutation tier needs — shared `Core/` infrastructure),
and `25` certifies the vtable lookup went through the derived override. (The
`automatic` keyword is required by IEEE 1800-2017 §6.21 for initialized variables
in a static block scope; without it, simulators warn even though behavior here is
unchanged.)

### 18. Process control — `join_none`, `join_any`, `disable fork`

```systemverilog
module timeout;
  logic done = 1'b0;
  int   status = 0;              // 1 = completed, 2 = timed out
  initial begin
    fork
      #30 done = 1'b1;           // the "work"
    join_none
    fork
      begin wait (done); status = 1; end
      begin #50 status = 2; end
    join_any
    disable fork;
    $finish;
  end
endmodule
```
```lean
theorem timeout_ok : timeout ⊨ Sv.atEnd fun s => s.status = 1

-- and the variant with the work at #70 instead of #30:
theorem timeout_fires : timeout70 ⊨ Sv.atEnd fun s => s.status = 2
```

The verification-methodology workhorse pattern (watchdog racing the payload,
loser killed by `disable fork`). Because the two outcomes are separated in *time*
(30 vs 50), the result is schedule-independent — the theorems hold for all σ — and
proving the `timeout70` variant flips to `status = 2` shows the semantics tracks
exactly which process wins and what `disable fork` terminates.

### 19. Liveness — no starvation, on infinite traces

```systemverilog
module arb2 (input  logic clk, rst,
             input  logic req0, req1,
             output logic gnt0, gnt1);
  logic last;                              // 1 ⇒ gnt1 was granted last
  always_ff @(posedge clk) begin
    if (rst) begin gnt0 <= 0; gnt1 <= 0; last <= 0; end
    else begin
      gnt0 <= req0 & (~req1 |  last);
      gnt1 <= req1 & (~req0 | ~last);
      if      (req0 & (~req1 | last)) last <= 1'b0;
      else if (req1)                  last <= 1'b1;
    end
  end

  a_live0: assert property (@(posedge clk) disable iff (rst)
             req0 |-> s_eventually (gnt0 || !req0));
endmodule
```
```lean
theorem arb2_no_starvation : arb2 ⊨ Sv.onPosedgeIdx fun tr n =>
    (∀ m, n ≤ m → tr.req0 m) → ∃ m, n ≤ m ∧ tr.gnt0 m
```

Liveness ("a held request is eventually granted") ranges over **infinite** traces:
the trace here is the function `cycle ↦ state` obtained by iterating the per-cycle
step, so `∃ m` is a genuine unbounded eventually — the property simulation can
only ever *fail to falsify* (an `s_eventually` assertion reports at end-of-sim),
but Lean can prove outright: with both requesters persistent, `last` alternates,
so the wait is in fact bounded by 2 cycles — and the bounded strengthening
`∃ m ≤ n + 2, …` is available to state too.

## Spec-prelude shopping list (SV additions)

- `Logic`/`LVec n` with `known`, `BitVec` coercions, X-propagation lemmas
- `Sv.comb`, `Sv.onPosedge`, `Sv.always`, `Sv.at`, `Sv.atEnd`, `Sv.eventually`,
  `Sv.transaction`, `Sv.FinishesBy`
- `Sv.Deterministic`, `sv_witness` (schedule counterexample exhibitor)
- `⊑@clk` cycle refinement against Lean transition functions, with the
  `[from rst]` initialization qualifier (4-state startup is X until first reset)
- SVA property extraction (`m.props.<label>`) + `⊨sva`
- Scheduler-region lemmas (NBA read/write separation, Preponed sampling,
  `disable iff` current-value asynchrony, Postponed-region trace sampling)
- Parametric design families: `Design` as a Lean function of parameters; induction
  principles over generate structure
- Net resolution lemmas (`LVec.resolve`: agree/Z-yield/conflict-X/float-Z cases)
- `Sv.stableWhile`, `Sv.afterReset`
- `Sv.beats` (valid∧ready sampling) + `List.IsPrefix` (`<+:`) composition lemmas
- SVA local variables ↦ `∀`-quantified unfoldings
- Infinite traces (`cycle ↦ state`) for liveness; bounded-eventually strengthenings
