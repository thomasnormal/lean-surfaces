/* Literal IEEE coverage queries use the empty self-check coverage database. */
module top;
  int control_status;
  int current_coverage;
  int maximum_coverage;
  int merge_status;
  int save_status;

  initial begin
    control_status = $coverage_control(3, 23, 11, "top");
    maximum_coverage = $coverage_get_max(22, 11, "top");
    current_coverage = $coverage_get(22, 11, "top");
    merge_status = $coverage_merge(23, "coverage_db");
    save_status = $coverage_save(23, "coverage_db");
    if (control_status == 0 && current_coverage == 0 &&
        maximum_coverage == 0 && merge_status == 0 && save_status == 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
