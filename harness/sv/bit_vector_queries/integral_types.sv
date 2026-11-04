module top;
  initial begin
    typedef logic signed [7:0] signed_t;
    typedef enum logic [3:0] {EMPTY = 4'd0, SINGLE = 4'd8} tag_t;
    signed_t signed_value;
    tag_t tag;
    bit [7:0] two_state;
    logic [79:0] wide;
    signed_value = -1;
    tag = SINGLE;
    two_state = 8'b10xz0011;
    wide = 80'hffff_ffff_ffff_ffff_ffff;
    if ($countones(signed_value) == 8 && $countones(8'sh80) == 1 &&
        $countones(-1) == 32 && $countones(64'sh8000_0000_0000_0000) == 1 &&
        $countones(wide) == 80 && $countones(two_state) == 3 &&
        !$isunknown(two_state) && $onehot(tag) && $countones(tag) == 1)
      $display("PASS");
    else
      $display("FAIL: integral widths and signedness");
    $finish;
  end
endmodule
// REFERENCE: 34eeff5d0fe2262f523a33b7 xrun(64) 24.03-s004 2026-10-10T09:45:11Z; PASS.
