/* Local bit declarations use the adapter's existing LocalDecl state. */
// PASS
module top;
  initial begin
    bit flag = 1'bx;
    bit [3:0] nibble = 4'b1x0z;
    $display("PASS");
    $finish;
  end
endmodule
