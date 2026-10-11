module top;
  logic [3:0] value, delta;
  initial begin
    value = 4'b0001;
    delta = 4'b0011;
    value += delta;
    value -= 4'b0001;
    value &= 4'b0110;
    value |= 4'b1000;
    value ^= 4'b0011;
    if (value !== 4'b1001) begin
      $display("FAIL: scalar compound assignment sequence");
      $finish;
    end
    $display("PASS");
    $finish;
  end
endmodule
// REFERENCE: 7124a2e2d04a5577256e0376 independent-simulator 2026-10-11T13:47:45Z
