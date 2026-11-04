/*
:name: printtimescale_decl
:description: IEEE 1800-2023 Section 20.4.2 -- the no-argument
  $printtimescale task reports scope metadata and does not alter simulation.
:tags: 20.4.2
:type: simulation
*/
module top;
  initial begin
    $printtimescale;
    $display("PASS");
    $finish;
  end
endmodule
