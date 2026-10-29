/*
:name: two_state_net
:description: §6.3.1 — wire bit startup floats and x drivers squash to zero
:tags: 6.3.1
:type: simulation
*/
module top;
  wire bit floating;
  wire bit [3:0] bus;
  wire bit driven;
  assign driven = 1'bx;

  initial begin
    // PASS
    if (floating === 1'bz && bus === 4'bzzzz && driven === 1'b0)
      $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
