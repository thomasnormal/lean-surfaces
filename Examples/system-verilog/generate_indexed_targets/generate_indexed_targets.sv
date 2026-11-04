/*
:name: generate_indexed_targets
:description: elaboration-constant indexed packed part-select targets in generated procedural assignments
:tags: 27.4
:type: simulation
*/
module top;
  logic [7:0] up;
  logic [7:0] down;
  for (genvar i = 0; i < 4; i++) begin : g
    initial up[i*2 +: 2] = i[1:0];
    initial down[7-i*2 -: 2] = i[1:0];
  end
  initial begin
    if (up === 8'b11100100 && down === 8'b00011011) $display("PASS");
    else $display("FAIL");
  end
endmodule
