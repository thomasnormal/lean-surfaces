/*
:name: severity_tasks
:description: IEEE 1800-2023 Section 20.10 -- literal $info and $warning
  report diagnostics without changing simulation state.
:tags: 20.10
:type: simulation
*/
module top;
  initial begin
    $info("informational message");
    $warning("warning message");
    $display("PASS");
    $finish;
  end
endmodule
