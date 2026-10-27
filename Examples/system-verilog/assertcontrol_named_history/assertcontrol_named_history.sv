/* Named literal assertion-control arguments are inert in the self-check state. */
module top;
  int action;
  int scope;
  initial begin
    action = 2;
    scope = 5;
    $assertcontrol(action, scope);
    $display("PASS");
    $finish;
  end
endmodule
