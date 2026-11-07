// Clean-room R2 wall: an unpacked register file with run-time read/write indices.
module unpacked_cpuregs #(parameter int N = 32) (
  input logic clk,
  input logic [4:0] raddr,
  input logic [4:0] waddr,
  input logic [31:0] wdata,
  input logic we,
  output logic [31:0] rdata
);
  logic [31:0] cpuregs [0:N-1];
  always_ff @(posedge clk) begin
    if (we) cpuregs[waddr] <= wdata;
  end
  assign rdata = cpuregs[raddr];
endmodule
