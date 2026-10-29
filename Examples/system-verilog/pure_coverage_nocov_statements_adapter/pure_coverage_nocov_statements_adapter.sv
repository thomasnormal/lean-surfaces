/*
:name: pure_coverage_nocov_statements_adapter
:description: Discarded literal coverage queries return the empty self-check coverage result.
:tags: 20.11
:type: simulation
*/
module top;
  initial begin
    $coverage_control(3, 23, 11, "top");
    $coverage_get_max(22, 11, "top");
    $coverage_get(22, 11, "top");
    $coverage_merge(23, "coverage_db");
    $coverage_save(23, "coverage_db");
    $display("PASS");
    $finish;
  end
endmodule
