// IEEE 1800-2023 6.19: four-state enum default and x/z member values.
module top;
  typedef enum logic [3:0] {HAS_X = 4'bx010, HAS_Z = 4'bz101,
                          KNOWN = 4'b0011} state_t;
  state_t state;
  initial begin
    if (state === 4'bxxxx) begin
      state = HAS_X;
      if (state === 4'bx010 && HAS_Z === 4'bz101 && KNOWN == 3) begin
        state = HAS_Z;
        if (state === 4'bz101)
          $display("PASS");
        else
          $display("FAIL");
      end else
        $display("FAIL");
    end else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 05addd04ab16a6b5618600a7 xrun(64) 24.03-s004 2026-10-09T23:16:58Z; PASS.
