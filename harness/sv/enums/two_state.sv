// IEEE 1800-2023 6.19 and 6.24: bit base defaults and x/z conversion.
module top;
  typedef enum bit [2:0] {FIRST = 5, SECOND} state_t;
  state_t state;
  initial begin
    if (state === 3'b000) begin
      state = state_t'(3'bx1z);
      if (state === 3'b010 && FIRST == 5 && SECOND == 6)
        $display("PASS");
      else
        $display("FAIL");
    end else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: a390c1ba0c4d796f6e1f0207 xrun(64) 24.03-s004 2026-10-09T23:17:06Z; PASS.
