/*
:name: fixed_array_dynamic_packed_slice
:description: §7.4.6/11.5 — dynamic indexed slices in packed fixed-array cells
:tags: 7.4.6, 11.5
:type: simulation
*/
module top;
  bit [3:0][7:0] source [0:0];
  bit [3:0][7:0] target [0:0];
  int i;

  initial begin
    source[0] = 32'h11223344;
    target[0] = 0;
    i = 1;
    target[0][i +: 2] = source[0][1:0];
    i = 3;
    target[0][i -: 2] = source[0][1:0];
    if (target[0] === 32'h33444400 && target[0][i -: 2] === 16'h3344)
      $display("PASS");
    else
      $display("FAIL");
  end
endmodule
