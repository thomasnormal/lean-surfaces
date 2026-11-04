/*
:name: dynamic_array_empty_decl
:description: IEEE 1800-2023 Section 7.5 -- zero-size dynamic-array
  declarations have no cells to represent, for either 2-state or 4-state
  element types.
:tags: 7.5
:type: simulation
*/
module top;
  bit bits_from_new[] = new[0];
  logic logic_from_new[] = new[0];
  bit bits_from_pattern[] = '{};
  logic logic_from_pattern[] = '{};
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
