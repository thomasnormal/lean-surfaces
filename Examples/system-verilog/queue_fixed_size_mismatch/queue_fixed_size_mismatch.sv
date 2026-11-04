/*
:name: queue_fixed_size_mismatch
:description: IEEE 1800-2023 §7.6 — a differently sized literal queue copied into a fixed array halts at the run-time mismatch
:tags: 7.6 queue assignment mismatch
:type: runtime_diagnostic
*/
module top;
  int fixed_values[3];
  int queue_values[$] = '{1, 2, 3, 4, 5};

  initial begin
    $display("BEFORE");
    fixed_values = queue_values;
    $display("UNREACHED");
    $finish;
  end
endmodule
