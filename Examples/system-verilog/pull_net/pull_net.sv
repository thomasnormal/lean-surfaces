/*
:name: pull_net
:description: §6.6.5 — un-driven tri0/tri1 nets use their implicit pull
:tags: 6.6.5
:type: simulation
*/
module top;
  tri0 gnd;
  tri1 vcc;

  initial begin
    // PASS
    if (gnd === 1'b0 && vcc === 1'b1) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
