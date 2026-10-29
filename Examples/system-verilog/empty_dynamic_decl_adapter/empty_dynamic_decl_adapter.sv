/*
:name: empty_dynamic_decl_adapter
:description: Empty dynamic-array declarations have no flat self-check cells.
:tags: 7.5
:type: simulation
*/
module top;
  initial begin
    bit bits_from_new[] = new[0];
    logic logic_from_new[] = new[0];
    bit bits_from_pattern[] = '{};
    logic logic_from_pattern[] = '{};
    $display("PASS");
    $finish;
  end
endmodule
