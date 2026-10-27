/*
:name: q_exam_stat_code_3_max_length_v3
:description: §20.15.5, Table 20-10 — q_stat_code 3 returns maximum queue length
:tags: 20.15.5
:type: simulation
*/
module top;
  int status;
  int max_len;
  initial begin
    $q_initialize(2, 1, 10, status);
    $q_add(2, 1, 100, status);
    $q_add(2, 2, 200, status);
    $q_exam(2, 3, max_len, status);  // q_stat_code 3 = max queue length
    if (status == 0 && max_len == 2) $display("PASS");
    else $display("FAIL status=%0d max_len=%0d", status, max_len);
    $finish;
  end
endmodule
