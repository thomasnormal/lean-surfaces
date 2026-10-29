/*
:name: wired_net
:description: §6.6.2 — un-driven wired-resolution nets read as high impedance
:tags: 6.6.2
:type: simulation
*/
module top;
  wand and_bus;
  wor or_bus;
  triand tri_and_bus;
  trior tri_or_bus;

  initial begin
    // PASS
    if (and_bus === 1'bz && or_bus === 1'bz
        && tri_and_bus === 1'bz && tri_or_bus === 1'bz)
      $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
