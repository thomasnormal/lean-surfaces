/*
:name: invalid_packed_dimension_literal
:description: IEEE 1800-2023 §7.4 — an elaboration-rejected packed dimension with a literal initializer has no runtime object.
:tags: 7.4 6.9.1
:type: compile_error
:diagnostic_match: packed dimensions require a full range
*/
module top;
  bit [3:x] bad_range = 1'b0;
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
