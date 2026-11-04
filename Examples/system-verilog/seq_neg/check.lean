import LeanModels.Sv.Ingest2
import LeanModels.Sv.Param2
import LeanModels.Sv.SeqProfile

/-!
# Negative fixtures for the FF-only clock-step profile (PLAN4 Gate 1, step 4)

Each design below is outside `Design2.ffOnlyProfileB` (`LeanModels/Sv/SeqProfile.lean`) for the
reason its source comment states, and a `#guard` pins that reason:

1. `blocking_self.sv`: a blocking self-read and write in `always_ff` (the body is not NBA-only);
2. `overlap.sv`: two `always_ff` processes write overlapping windows: the loader refuses it (the
   one-driver rule, IEEE 1800-2023 §9.2.2.4; the refusal is pinned by `#guard_msgs`);
3. `blocking_ff.sv`: a blocking assignment in `always_ff` (not NBA-only);
4. `async_reset.sv`: an asynchronous reset (`alwaysFFR`, not an `always_ff` of the profile);
5. `temp_cycle.sv`: two processes in a dependency cycle through blocking temporaries; not NBA-only,
   and its `run2` result depends on the schedule (`σ_src` and `σ_rev` disagree).

The sixth item, a schedule that omits a process, is a theorem: `omitted_process` (`SeqProfile.lean`).
-/

namespace Examples.systemVerilog.seq_neg.check

open LeanModels.Sv

load_design_sv2 blockingSelf from "Examples/system-verilog/seq_neg/blocking_self.sv.json"
-- 2. overlapping windows: the loader refuses the design (the one-driver rule).
/--
error: load_design_sv2: 'Examples/system-verilog/seq_neg/overlap.sv.json' REFUSED — at the defaults, signal 'q' of module 'overlap' is written on one bit by an `always_comb`/`always_ff` procedure and by another process at this parameter point (IEEE 1800-2023 §9.2.2.2/§9.2.2.4: no other process may write such a procedure's variables, per longest static prefix §11.5.3; a run-time index covers the whole signal): the semantics would order the writes by process order, which no simulator is bound to (`PortConn:driver`, `driversOk`)
-/
#guard_msgs in
load_design_sv2 overlap from "Examples/system-verilog/seq_neg/overlap.sv.json"

load_design_sv2 blockingFF from "Examples/system-verilog/seq_neg/blocking_ff.sv.json"
load_design_sv2 asyncReset from "Examples/system-verilog/seq_neg/async_reset.sv.json"
load_design_sv2 tempCycle from "Examples/system-verilog/seq_neg/temp_cycle.sv.json"

/-- Some `always_ff` body is not NBA-only. -/
def someBlocking (d : Design2) : Bool :=
  d.processes.toList.any fun p => match p with
    | .alwaysFF _ b => !b.nbaOnly
    | _ => false

-- 1. a blocking self-read and write
#guard blockingSelf.sem.ffOnlyProfileB == false
#guard someBlocking blockingSelf.sem
-- 3. a blocking assignment in always_ff
#guard blockingFF.sem.ffOnlyProfileB == false
#guard someBlocking blockingFF.sem
-- 4. an asynchronous reset
#guard asyncReset.sem.ffOnlyProfileB == false
#guard asyncReset.sem.processes.toList.any fun p => match p with
  | .alwaysFFR _ _ _ => true
  | _ => false
-- 5. a dependency cycle through blocking temporaries: out of the profile, and schedule-dependent
#guard tempCycle.sem.ffOnlyProfileB == false
#guard someBlocking tempCycle.sem
#guard (cycleStep2 tempCycle.sem σ_src 64 [("clk", .ofNat 1 1), ("d", .ofNat 4 1)]
      (initState2 tempCycle.sem) 0).toOption.map (·.1) !=
    (cycleStep2 tempCycle.sem σ_rev 64 [("clk", .ofNat 1 1), ("d", .ofNat 4 1)]
      (initState2 tempCycle.sem) 0).toOption.map (·.1)

end Examples.systemVerilog.seq_neg.check
