/*
:name: q_exam_length
:description: §20.15.5 — $q_exam with q_stat_code=1 returns current queue length
:tags: 20.15 20.15.5
:type: simulation
*/
module top;
  initial begin
    integer status;
    integer q_stat_value;
    $q_initialize(4, 1, 10, status);
    $q_add(4, 1, 0, status);
    $q_add(4, 2, 0, status);
    $q_exam(4, 1, q_stat_value, status); // q_stat_code=1: current length
    if (status === 0 && q_stat_value === 2)
      $display("PASS");
    else
      $display("FAIL: status=%0d length=%0d", status, q_stat_value);
    $finish;
  end
endmodule
