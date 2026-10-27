/*
:name: q_exam_stat_codes
:description: §20.15.5 — $q_exam stat_code 1 shall return the current queue length; stat_code 3 shall return the maximum length seen
:tags: 20.15.5
:type: simulation
*/
module top;
  integer q_id, job_id, inform_id, stat_code, stat_value;
  initial begin
    q_id = 1;
    $q_initialize(q_id, 1, 10, stat_code);  // FIFO, max_length=10
    if (stat_code !== 0) begin
      $display("FAIL: q_initialize stat_code=%0d", stat_code);
      $finish;
    end

    job_id = 42; inform_id = 0;
    $q_add(q_id, job_id, inform_id, stat_code);
    if (stat_code !== 0) begin
      $display("FAIL: q_add stat_code=%0d", stat_code);
      $finish;
    end

    // stat_code 1 = current length
    $q_exam(q_id, 1, stat_value, stat_code);
    if (stat_value !== 1) begin
      $display("FAIL: current length expected 1, got %0d", stat_value);
      $finish;
    end

    // stat_code 3 = maximum length seen
    $q_exam(q_id, 3, stat_value, stat_code);
    if (stat_value < 1) begin
      $display("FAIL: max length expected >=1, got %0d", stat_value);
      $finish;
    end

    $display("PASS");
    $finish;
  end
endmodule
