// Clean-room E memory witness: one-rank unpacked storage with runtime
// read and write indices, matching the PicoRV32 register-file shape.
module unpacked_cpuregs_canonical_e #(parameter int N = 32) (
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
