/*
:name: discarded_pure_real_to_bits
:description: discarded pure real-to-bits conversions have no modeled state effect
:tags: 20.5
:type: simulation
*/
module top;
  real value;

  initial begin
    $realtobits(value);
    $realtobits($sqrt(16.0));
    $shortrealtobits(value);
    $shortrealtobits($sin(0.0));
    $display("PASS");
    $finish;
  end
endmodule
