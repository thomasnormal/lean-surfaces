/*
:name: fatal_dynamic
:description: A pure dynamic argument is evaluated before $fatal halts.
:tags: 20.10
:type: simulation
*/
module top;
  logic [3:0] x;
  initial begin
    x = 4'd3;
    $display("PASS");
    $fatal(1, "done=%0d", x);
    $display("FAIL");
  end
endmodule
