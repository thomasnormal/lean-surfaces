/* Time-zero $realtime feeds the exact real-conversion calls. */
module top;
  integer as_int;
  logic [63:0] as_bits;
  logic [31:0] as_short;
  initial begin
    as_int = $rtoi($realtime);
    as_bits = $realtobits($realtime);
    as_short = $shortrealtobits($realtime);
    if (as_int === 0
        && as_bits === 64'b0
        && as_short === 32'b0)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
