/*
:name: q_full_returns_one_when_full
:description: §20.15.4 — $q_full returns 1 when queue is full, 0 otherwise
:tags: 20.15.4
:type: simulation
*/
module top;
  initial begin
    int status;
    int jid_out, info_out;
    int full;
    $q_initialize(2, 1, 2, status);  // max 2
    full = $q_full(2, status);
    if (full != 0) begin $display("FAIL full_at_start=%0d", full); $finish; end
    $q_add(2, 10, 0, status);
    $q_add(2, 20, 0, status);
    full = $q_full(2, status);
    if (full == 1) $display("PASS");
    else $display("FAIL full=%0d", full);
    $finish;
  end
endmodule
