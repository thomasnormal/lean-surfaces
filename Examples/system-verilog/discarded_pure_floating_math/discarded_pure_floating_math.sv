/*
:name: discarded_pure_floating_math
:description: discarded pure floating math calls have no modeled state effect
:tags: 20.8
:type: simulation
*/
module top;
  initial begin
    $sqrt(16.0);
    $pow(2.0, 3.0);
    $sin($sqrt(4.0));
    $display("PASS");
    $finish;
  end
endmodule
