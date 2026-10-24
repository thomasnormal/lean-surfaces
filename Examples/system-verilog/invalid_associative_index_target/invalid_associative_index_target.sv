/*
:name: invalid_associative_index_target
:description: IEEE 1800-2023 §§7.8.4-7.8.5 — floating associative-array keys and implicit real-to-integral index conversions are illegal.
:tags: 7.8.4 7.8.5 associative array index
:type: compile_error
:diagnostic_match: associative array index cannot be selected with a real expression
*/
module top;
  int integral_keys[int];
  int floating_keys[real];
  real r = 3.7;
  initial begin
    integral_keys[r] = 10;
    floating_keys[1.5] = 10;
    $display("PASS");
    $finish;
  end
endmodule
