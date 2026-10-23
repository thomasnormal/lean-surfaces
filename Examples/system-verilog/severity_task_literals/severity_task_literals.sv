/*
:name: severity_task_literals
:description: IEEE 1800-2023 Section 20.10 -- severity diagnostics with a
  literal format and literal argument do not alter simulation state.
:tags: 20.10
:type: simulation
*/
module top;
  initial begin
    $warning("value=%0d", 7);
    $info("hex=%h", 8'h3a);
    $display("PASS");
    $finish;
  end
endmodule
