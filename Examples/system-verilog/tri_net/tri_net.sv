/*
:name: tri_net
:description: §6.6.1 — an un-driven tri net reads as high impedance
:tags: 6.6.1
:type: simulation
*/
module top;
  tri [3:0] bus;

  initial begin
    // PASS
    if (bus === 4'bzzzz) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
