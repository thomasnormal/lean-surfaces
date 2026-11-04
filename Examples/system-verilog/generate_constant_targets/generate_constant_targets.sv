/*
:name: generate_constant_targets
:description: elaboration-constant packed element targets in generated continuous assignments
:tags: 27.4
:type: simulation
*/
module top;
  logic [3:0] chain;
  initial chain[0] = 1'b1;
  for (genvar i = 0; i < 3; i++) begin : g
    initial chain[i+1] = chain[i];
  end
  initial begin
    if (chain[3] === 1'b1) $display("PASS");
    else $display("FAIL");
  end
endmodule
