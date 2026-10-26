/* Literal-bound real storage feeds the exact IEEE conversion functions. */
module top;
  logic [63:0] dbits;
  logic [31:0] sbits;
  real d;
  shortreal s = 1.0;
  initial begin
    d = -2.5;
    dbits = $realtobits(d);
    sbits = $shortrealtobits(s);
    if (dbits === 64'hC004_0000_0000_0000 &&
        sbits === 32'h3F80_0000)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
