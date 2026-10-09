module top;
  logic signed [7:0] signed_source;
  logic [7:0] unsigned_source;
  logic [15:0] signed_nested;
  logic [15:0] unsigned_nested;
  logic [15:0] frozen_sum;
  logic [15:0] propagated_sum;
  logic [7:0] cast_chain;

  initial begin
    signed_source = 8'h79;
    unsigned_source = 8'h79;
    signed_nested = 8'(4'(signed_source));
    unsigned_nested = 8'(4'(unsigned_source));
    frozen_sum = 4'(signed_source + 8'd1);
    propagated_sum = signed_source + 8'd1;
    cast_chain = 8'(int'(4'(signed_source)));
    $display("nested=[%h][%h][%h][%h][%h]", signed_nested,
             unsigned_nested, frozen_sum, propagated_sum, cast_chain);
    if ((signed_nested === 16'hfff9) &&
        (unsigned_nested === 16'h0009) &&
        (frozen_sum === 16'h000a) &&
        (propagated_sum === 16'h007a) && (cast_chain === 8'hf9))
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 028afae42c02c2959b2869f2 TOOL:	xrun(64)	24.03-s004 2026-10-09T21:34:29Z
