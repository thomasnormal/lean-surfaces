/*
:name: q_exam_static_history
:description: §20.15.5 — literal zero-time queue histories cover current/max length and zero timing statistics
:tags: 20.15 20.15.5
:type: simulation
*/
module top;
  integer status, stat_val, job, info;
  initial begin
    $q_initialize(30, 1, 10, status);
    $q_add(30, 1, 0, status);
    $q_add(30, 2, 0, status);
    $q_exam(30, 1, stat_val, status);
    if (status !== 0 || stat_val !== 2) begin
      $display("FAIL: length after 2 adds = %0d", stat_val);
      $finish;
    end
    $q_remove(30, job, info, status);
    $q_exam(30, 1, stat_val, status);
    if (status !== 0 || stat_val !== 1) begin
      $display("FAIL: length after remove = %0d", stat_val);
      $finish;
    end
    $q_exam(30, 2, stat_val, status);
    if (status !== 0 || stat_val !== 0) begin
      $display("FAIL: mean interarrival = %0d", stat_val);
      $finish;
    end
    $q_exam(30, 4, stat_val, status);
    if (status !== 0 || stat_val !== 0) begin
      $display("FAIL: shortest wait = %0d", stat_val);
      $finish;
    end
    $q_exam(30, 5, stat_val, status);
    if (status !== 0 || stat_val !== 0) begin
      $display("FAIL: longest wait = %0d", stat_val);
      $finish;
    end
    $q_exam(30, 6, stat_val, status);
    if (status !== 0 || stat_val !== 0) begin
      $display("FAIL: average wait = %0d", stat_val);
      $finish;
    end
    $display("PASS");
    $finish;
  end
endmodule
