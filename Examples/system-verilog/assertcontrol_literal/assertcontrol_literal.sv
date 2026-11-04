/* A literal assertion-control task has no modeled self-check state. */
module top;
  initial begin
    $assertcontrol(1);
    $display("PASS");
    $finish;
  end
endmodule
