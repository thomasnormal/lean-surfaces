/*
:name: printtimescale_scope
:description: IEEE 1800-2023 Section 20.4.2 -- validated scope arguments
  are diagnostic-only in the self-check observable state.
:tags: 20.4.2
:type: simulation
*/
module top;
  initial begin
    $printtimescale($unit);
    $printtimescale($root);
    $printtimescale(top);
    $display("PASS");
    $finish;
  end
endmodule
