/*
:name: fatal_task
:description: IEEE 1800-2023 Section 20.10 -- a literal $fatal terminates
  simulation, so later statements are not executed.
:tags: 20.10
:type: simulation
*/
module top;
  initial begin
    $display("PASS");
    $fatal(0, "done");
    $display("FAIL");
  end
endmodule
