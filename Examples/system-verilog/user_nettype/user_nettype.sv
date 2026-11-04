/*
:name: user_nettype
:description: §6.7 — plain user-defined integral nettypes retain high impedance
:tags: 6.7
:type: simulation
*/
module top;
  nettype logic scalar_net;
  nettype logic [3:0] vector_net;
  scalar_net scalar;
  vector_net bus;

  initial begin
    // PASS
    if (scalar === 1'bz && bus === 4'bzzzz) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
