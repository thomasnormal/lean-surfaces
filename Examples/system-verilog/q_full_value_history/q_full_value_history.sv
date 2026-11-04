/*
:name: q_full_value_history
:description: §20.15.4 — value-position $q_full follows source-pure queue status checks and literal adds
:tags: 20.15 20.15.4
:type: simulation
*/
module top;
  initial begin
    integer status, full;
    $q_initialize(1, 1, 2, status);
    if (status !== 0) begin
      $display("FAIL: initialize status=%0d", status);
      $finish;
    end
    full = $q_full(1, status);
    if (full !== 0) begin
      $display("FAIL: empty queue reported full");
      $finish;
    end
    $q_add(1, 10, 0, status);
    $q_add(1, 20, 0, status);
    full = $q_full(1, status);
    if (full === 1)
      $display("PASS");
    else
      $display("FAIL: full queue reported %0d", full);
    $finish;
  end
endmodule
