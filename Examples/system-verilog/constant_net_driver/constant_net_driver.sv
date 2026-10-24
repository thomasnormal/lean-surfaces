/* One literal continuous net driver is fixed at time zero. */
module top;
  wire y;
  assign y = 1'b1;
  initial begin
    if (y === 1'b1) $display("PASS");
    else $display("FAIL");
    $finish;
  end
endmodule
