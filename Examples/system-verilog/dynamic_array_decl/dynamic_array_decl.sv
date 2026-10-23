/*
:name: dynamic_array_decl
:description: IEEE 1800-2023 Section 7.5 -- an uninitialized 2-state
  dynamic-array declaration is inert until allocation or access.
:tags: 7.5
:type: simulation
*/
module top;
  bit values[];
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
