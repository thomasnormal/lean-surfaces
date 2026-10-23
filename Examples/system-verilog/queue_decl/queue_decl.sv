/*
:name: queue_decl
:description: IEEE 1800-2023 Section 7.10 -- an uninitialized 2-state
  queue declaration is inert until a queue operation observes it.
:tags: 7.10
:type: simulation
*/
module top;
  bit values[$];
  initial begin
    $display("PASS");
    $finish;
  end
endmodule
