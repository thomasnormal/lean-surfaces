/* Querying the predefined stdout descriptor reports the standard error code. */
module top;
  int position;
  initial begin
    position = $ftell(32'h8000_0001);
    if (position == -1)
      $display("PASS");
    else
      $display("FAIL: position=%0d", position);
    $finish;
  end
endmodule
