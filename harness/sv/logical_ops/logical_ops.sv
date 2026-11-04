module logical_ops (
  input logic clk,
  input logic [1:0] value,
  output logic both,
  output logic either
);
  always_ff @(posedge clk) begin
    both = value && 2'b01;
    either = value || 2'b00;
  end
endmodule
