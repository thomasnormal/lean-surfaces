/*
:name: supply_net
:description: §6.6.6 — an un-driven supply0/supply1 net has a permanent value
:tags: 6.6.6
:type: simulation
*/
module top;
  supply0 gnd;
  supply1 vcc;

  initial begin
    // PASS
    if (gnd === 1'b0 && vcc === 1'b1) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
