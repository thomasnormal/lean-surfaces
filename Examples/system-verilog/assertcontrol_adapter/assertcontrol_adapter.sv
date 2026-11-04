/*
:name: assertcontrol_adapter
:description: Literal assertion control has no represented self-check state.
:tags: 20.12
:type: simulation
*/
module top;
  initial begin
    $assertcontrol(2, 5);
    $display("PASS");
    $finish;
  end
endmodule
