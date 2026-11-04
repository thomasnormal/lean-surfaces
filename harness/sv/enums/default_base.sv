// IEEE 1800-2023 6.19: default int base and base defaults, not first labels.
module top;
  typedef enum {FIRST = 7, SECOND} default_t;
  typedef enum integer {FOUR_FIRST = 7, FOUR_SECOND} four_t;
  default_t two_state_default;
  four_t four_state_default;
  initial begin
    if (two_state_default === 32'd0 && four_state_default === 32'bx &&
        FIRST == 7 && SECOND == 8 && default_t'(-1) < 0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 6b71060f2242e96e76aeb908 xrun(64) 24.03-s004 2026-10-09T23:16:55Z; PASS.
