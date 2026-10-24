/*
:name: semaphore_zero_key_methods
:description: IEEE 1800-2023 §15.3.2-15.3.3 zero-key semaphore methods are no-ops
:tags: 15.3.2 15.3.3 semaphore
:type: simulation
*/
module top;
  semaphore sem;
  initial begin
    sem = new(0);
    sem.put(0);
    sem.get(0);
    $display("PASS");
    $finish;
  end
endmodule
