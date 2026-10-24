/*
:name: literal_semaphore_constructor
:description: IEEE 1800-2023 §15. semaphore construction with a known nonnegative literal key count is an opaque handle write in the self-check tier.
:tags: 15 semaphore class handle
:type: simulation
*/
module top;
  semaphore sem;
  initial begin
    sem = new(1);
    $display("PASS");
    $finish;
  end
endmodule
