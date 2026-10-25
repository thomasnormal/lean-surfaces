/* Literal string radix conversions retain four-state radix digits. */
module top;
  string h = "2x";
  string b = "10x1";
  string o = "7?";
  logic [31:0] hv, bv, ov;
  initial begin
    hv = h.atohex();
    bv = b.atobin();
    ov = o.atooct();
    if (hv === 32'h0000002x &&
        bv === 32'b000000000000000000000000000010x1 &&
        ov === 32'b00000000000000000000000000111zzz)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
