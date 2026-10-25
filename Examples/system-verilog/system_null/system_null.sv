/*
:name: system_null
:description: IEEE 1800-2023 Section 20.17.1 -- task-form $system()
  invokes the null command and discards its status.
:tags: 20.17.1
:type: simulation
*/
module top;
  initial begin
    $system();
    $display("PASS");
    $finish;
  end
endmodule
