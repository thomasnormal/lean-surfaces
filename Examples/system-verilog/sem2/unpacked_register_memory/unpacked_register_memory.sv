// Clean-room R2 memory wall: a small register file with run-time read/write indices.
module unpacked_register_memory #(parameter int N = 4) (
  input logic clk,
  input logic we,
  input logic [1:0] waddr,
  input logic [1:0] raddr,
  input logic [7:0] d,
  output logic [7:0] q
);
  logic [7:0] regs [0:N-1];
  always_ff @(posedge clk)
    if (we) regs[waddr] <= d;
  assign q = regs[raddr];
endmodule
