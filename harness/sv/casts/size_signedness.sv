module top;
  logic signed [3:0] signed_source;
  logic [3:0] unsigned_source;
  logic [7:0] signed_bits;
  logic [7:0] unsigned_bits;
  logic [1:0] truncated;

  initial begin
    signed_source = 4'b1001;
    unsigned_source = 4'b1001;
    signed_bits = 8'(signed_source);
    unsigned_bits = 8'(unsigned_source);
    truncated = 2'(signed_source);
    $display("size=[%b][%b][%b]", signed_bits, unsigned_bits, truncated);
    if ((signed_bits === 8'b11111001) &&
        (unsigned_bits === 8'b00001001) &&
        (truncated === 2'b01) &&
        (8'(signed_source) < 0) && !(8'(unsigned_source) < 0))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: e11ed76a56c04644d86269f4 TOOL:	xrun(64)	24.03-s004 2026-10-09T21:34:34Z
