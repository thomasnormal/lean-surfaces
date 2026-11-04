/*
:name: unobserved_queue_literal_write
:description: IEEE 1800-2023 §10.10 literal queue assignment with no later observation
:tags: 10.10 queue assignment
:type: simulation
*/
module top;
  int q[$];
  initial begin
    q = {1, 2, 3};
    $display("PASS");
    $finish;
  end
endmodule
