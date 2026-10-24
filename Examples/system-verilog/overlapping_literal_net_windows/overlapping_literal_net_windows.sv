/* Literal packed-net windows resolve overlapping bits at time zero. */
module top;
  wire [3:0] bus;
  assign bus[2:0] = 3'b101;
  assign bus[3:1] = 3'b100;
  initial begin
    if (bus === 4'b1x01)
      $display("PASS");
    else
      $display("FAIL %b", bus);
    $finish;
  end
endmodule
