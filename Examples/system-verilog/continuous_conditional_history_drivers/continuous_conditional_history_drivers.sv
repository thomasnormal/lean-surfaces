/*
:name: continuous_conditional_history_drivers
:description: §10.3/§28.12 — pure conditional drivers fold from literal source state
:tags: 10.3 28.12
:type: simulation
*/
module top;
  logic enable_a = 1'b0;
  logic enable_b = 1'b0;
  wire bus;

  assign bus = enable_a ? 1'b1 : 1'bz;
  assign bus = enable_b ? 1'b0 : 1'bz;

  initial begin
    if (bus === 1'bz)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
