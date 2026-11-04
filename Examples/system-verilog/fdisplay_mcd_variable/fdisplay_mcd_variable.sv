/* The predefined stdout MCD may be carried by a direct integer assignment. */
module top;
  integer mcd;
  initial begin
    mcd = 1;
    $fdisplay(mcd, "PASS via MCD bit 0");
    $finish;
  end
endmodule
