/*
:name: error_task
:description: IEEE 1800-2023 Section 20.10 -- $error reports a literal
  diagnostic but does not terminate simulation.
:tags: 20.10
:type: simulation
*/
module top;
  initial begin
    $error("diagnostic");
    $display("PASS");
    $finish;
  end
endmodule
