module top;
  logic [7:0] value;
  logic [3:0] index;
  integer signed_index;
  bit [3:0] two_state;
  initial begin
    value = 8'b10101010;
    index = 4'd2;
    value[index] = 1'b1;
    if (value !== 8'b10101110) begin
      $display("FAIL: runtime bit write");
      $finish;
    end
    signed_index = -1;
    value[signed_index] = 1'b1;
    if (value !== 8'b10101110) begin
      $display("FAIL: negative bit index");
      $finish;
    end
    index = 4'bxxxx;
    value[index] = 1'b0;
    if (value !== 8'b10101110) begin
      $display("FAIL: unknown bit index");
      $finish;
    end
    value[5:2] = 4'bxz01;
    if (value !== 8'b10xz0110) begin
      $display("FAIL: four-state simple part write");
      $finish;
    end
    value = 8'b00000000;
    signed_index = 4;
    value[signed_index -: 4] = 4'b0101;
    if (value !== 8'b00001010) begin
      $display("FAIL: runtime indexed-down write");
      $finish;
    end
    value[5 +: 2] = 2'b11;
    if (value !== 8'b01101010) begin
      $display("FAIL: indexed-up write");
      $finish;
    end
    two_state = 4'b1111;
    two_state[2:1] = 2'bxz;
    if (two_state !== 4'b1001) begin
      $display("FAIL: two-state selected conversion");
      $finish;
    end
    $display("PASS");
    $finish;
  end
endmodule
// REFERENCE: 8188f8f612e2b03648119832 xrun(64) 24.03-s004 2026-10-10T12:48:22Z; PASS.
