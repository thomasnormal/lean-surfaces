module top;
  initial begin
    if ($bits(bit) == 1 && $bits(logic) == 1 &&
        $bits(byte) == 8 && $bits(shortint) == 16 &&
        $bits(int) == 32 && $bits(integer) == 32 &&
        $bits(longint) == 64 && $bits(time) == 64)
      $display("PASS");
    else
      $display("FAIL: builtin type widths");
    $finish;
  end
endmodule
// REFERENCE: 6fbef9e828cf0d41d1719e88 xrun(64) 24.03-s004 2026-10-10T03:16:14Z; PASS.
