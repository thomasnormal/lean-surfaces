/*
:name: q_exam_timed_statistics
:description: §20.15.5 — literal delayed queue history for statistic codes 2, 4, 5, and 6
:tags: 20.15 20.15.5
:type: simulation
*/
`timescale 1ns/1ps
module top;
  integer status, stat_val, longest, mean_interarrival, shortest, average;
  integer job_id, inform_id;
  initial begin
    $q_initialize(6155, 1, 8, status);
    $q_add(6155, 101, 0, status);
    #4;
    $q_add(6155, 202, 0, status);

    // The first job has waited four ticks when this query runs.
    $q_exam(6155, 5, longest, status);
    #6;
    $q_remove(6155, job_id, inform_id, status);
    $q_exam(6155, 2, mean_interarrival, status);
    $q_exam(6155, 4, shortest, status);
    $q_exam(6155, 6, average, status);
    if (status !== 0 || longest !== 4 || mean_interarrival !== 4 ||
        shortest !== 10 || average !== 10) begin
      $display("FAIL: timed statistics %0d %0d %0d %0d", longest,
               mean_interarrival, shortest, average);
      $finish;
    end
    $display("PASS q_exam_timed_statistics");
    $finish;
  end
endmodule
