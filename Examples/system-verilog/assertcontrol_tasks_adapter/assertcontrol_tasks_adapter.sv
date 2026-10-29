/*
:name: assertcontrol_tasks_adapter
:description: Bare assertion-control tasks are inert in the legacy adapter.
:tags: 20.12
:type: simulation
*/
module top;
  initial begin
    $asserton;
    $assertoff;
    $assertkill;
    $display("PASS");
    $finish;
  end
endmodule
