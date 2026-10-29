/*
:name: trireg_net
:description: §6.6.4 — an un-driven plain trireg starts high impedance
:tags: 6.6.4
:type: simulation
*/
module top;
  trireg scalar;
  trireg [3:0] bus;

  initial begin
    // PASS
    if (scalar === 1'bz && bus === 4'bzzzz) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
