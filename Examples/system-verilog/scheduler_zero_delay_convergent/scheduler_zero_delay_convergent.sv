// SPDX-License-Identifier: Apache-2.0
// A zero-delay feedback loop settles when its guard stops publishing writes.
/*
:name: scheduler_zero_delay_convergent
:description: IEEE 1800-2023 Section 4.4 -- procedural NBA publication
  re-enters Active in the same time slot until a guarded loop settles.
:tags: 4.4 9.4 10.4
:type: simulation
// Expected transcript: N=3.
*/
module top;
  logic a = 1'b0;
  integer n = 0;
  always @(a) begin
    if (n < 3) begin
      n <= n + 1;
      a <= ~a;
    end
  end
  initial begin
    #0 a = 1'b1;
    #1 $display("N=%0d", n);
    $finish;
  end
endmodule
