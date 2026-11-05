// R1 toy only: a one-cycle RV32I retirement shell.
//
// This is deliberately a small, hand-written core-shaped block rather than a
// claim about a production implementation.  The R1 Lean proof models the
// admitted ADDI stream below against LeanModels.Rv.isaStep.  The source uses
// an edge process, so it is intentionally not loaded by today's SV tier until
// the retained edge-process request lands in ls-sv.
module toy_rv32i(
    input  logic        clk,
    input  logic        rst,
    input  logic [31:0] instr,
    output logic [31:0] pc,
    output logic [31:0] x1,
    output logic        commit_valid
);
  always_ff @(posedge clk) begin
    if (rst) begin
      pc           <= 32'd0;
      x1           <= 32'd0;
      commit_valid <= 1'b0;
    end else if (instr == 32'h00100093) begin // addi x1, x0, 1
      pc           <= pc + 32'd4;
      x1           <= 32'd1;
      commit_valid <= 1'b1;
    end else begin
      pc           <= pc;
      x1           <= x1;
      commit_valid <= 1'b0;
    end
  end
endmodule
