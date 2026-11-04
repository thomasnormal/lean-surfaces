/*
:name: discarded_pure_rtoi
:description: discarded pure $rtoi calls have no modeled state effect
:tags: 20.5
:type: simulation
*/
module top;
  real value;

  initial begin
    $rtoi(value);
    $rtoi($sqrt(16.0));
    $display("PASS");
    $finish;
  end
endmodule
