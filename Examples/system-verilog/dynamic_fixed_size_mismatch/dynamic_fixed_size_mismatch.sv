/*
:name: dynamic_fixed_size_mismatch
:description: IEEE 1800-2023 §7.6 — copying a differently sized dynamic array into a fixed array is a run-time error and performs no copy.
:tags: 7.6 dynamic array assignment mismatch
:type: runtime_diagnostic
*/
module top;
  int fixed_values[2];
  int dynamic_values[] = new[3];

  initial begin
    $display("BEFORE");
    fixed_values = dynamic_values;
    $display("UNREACHED");
    $finish;
  end
endmodule
