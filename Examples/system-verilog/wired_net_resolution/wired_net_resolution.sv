/*
:name: wired_net_resolution
:description: §6.6.3 and §28.12.4 — literal wand and wor drivers resolve per bit
:tags: 6.6.3 28.12.4
:type: simulation
*/
module top;
  wand [1:0] and_bus;
  wor  [1:0] or_bus;

  assign and_bus = 2'b11;
  assign and_bus = 2'b10;
  assign or_bus = 2'b00;
  assign or_bus = 2'b01;

  initial begin
    if (and_bus === 2'b10 && or_bus === 2'b01)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
