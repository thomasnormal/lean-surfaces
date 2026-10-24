/* Literal assertion-control arguments are inert in the self-check state. */
module top;
  initial begin
    $assertcontrol(2, 5);
    $display("PASS");
    $finish;
  end
endmodule
