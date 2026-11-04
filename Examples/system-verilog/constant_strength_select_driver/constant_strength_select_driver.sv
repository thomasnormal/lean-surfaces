/* One explicitly strengthened packed-bit driver has a fixed value. */
module top;
  wire [3:0] bus;
  assign (strong1, strong0) bus[2] = 1'b1;
  initial begin
    if (bus[2] === 1'b1)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
