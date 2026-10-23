/*
:name: associative_array_decl
:description: IEEE 1800-2023 Section 7.8 -- an uninitialized 2-state
  associative-array declaration is inert until an operation observes it.
:tags: 7.8
:type: simulation
*/
module top;
  bit values[int];
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
