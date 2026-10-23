/*
:name: strobe_literal
:description: IEEE 1800-2023 Section 21.2.2 -- literal $strobe output is
  deferred until after active $display statements in the time-zero slot.
:tags: 21.2.2
:type: simulation
*/
module top;
  initial begin
    $display("DISPLAY");
    $strobe("STROBE");
    $display("DISPLAY2");
    $finish;
  end
endmodule
