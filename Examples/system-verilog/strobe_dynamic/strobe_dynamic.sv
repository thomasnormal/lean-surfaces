/*
:name: strobe_dynamic
:description: IEEE 1800-2023 Section 21.2 -- a strobe samples a pure
  expression at the postponed end of the current time step.
:tags: 21.2
:type: simulation
*/
module top;
  integer value;
  initial begin
    value = 4;
    $strobe("VALUE=%0d", value);
    value = 9;
    $display("PASS");
    // VALUE=9 is the postponed self-check line.
    $finish;
  end
endmodule
