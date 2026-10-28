/*
:name: invalid_packed_dimension_decl
:description: IEEE 1800-2023 §7.4 — malformed packed dimensions are compile-time errors and allocate no runtime variables.
:tags: 7.4 6.9.1
:type: compile_error
:diagnostic_match: packed dimensions require a full range
*/
module top;
  bit [3:x] bad_range;
  bit [3] bad_single;
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
