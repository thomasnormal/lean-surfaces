/* Disjoint literal packed-net windows are independent time-zero writes. */
module top;
  wire [3:0] bus;
  assign bus[1:0] = 2'b01;
  assign bus[3:2] = 2'b10;
  initial begin
    if (bus === 4'b1001)
      $display("PASS");
    else
      $display("FAIL %b", bus);
    $finish;
  end
endmodule
