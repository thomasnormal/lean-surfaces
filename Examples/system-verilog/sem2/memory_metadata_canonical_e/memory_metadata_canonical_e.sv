// Canonical-E metadata receipt: an empty task and an unsized x/z literal
// beside a source-shaped one-rank memory.
module memory_metadata_canonical_e #(parameter integer N = 4) (
    input logic clk,
    output logic [31:0] q
);
  logic [31:0] mem [0:N-1];

  task empty_statement;
    begin end
  endtask

  initial begin
    empty_statement;
    mem[0] = 'bx;
  end

  assign q = mem[0];
endmodule
