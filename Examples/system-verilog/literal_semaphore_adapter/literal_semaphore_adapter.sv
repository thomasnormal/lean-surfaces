/*
:name: literal_semaphore_adapter
:description: A literal semaphore constructor in a local declaration is opaque metadata.
:tags: 15
:type: simulation
*/
module top;
  initial begin
    semaphore sem = new(5);
    $display("PASS");
    $finish;
  end
endmodule
