/*
:name: fdisplay_stdout
:description: IEEE 1800-2023 Section 21.3.1 -- the predefined standard
  output descriptor is observable through the self-check output stream.
:tags: 21.3.1
:type: simulation
*/
module top;
  initial begin
    $fdisplay(32'h8000_0001, "PASS");
    $finish;
  end
endmodule
