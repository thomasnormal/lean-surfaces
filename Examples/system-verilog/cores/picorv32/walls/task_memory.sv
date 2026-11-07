// Clean-room R2 wall: a referenced module task beside a source-shaped memory.
module task_memory #(parameter int N = 4) (
  input logic clk,
  output logic [31:0] q
);
  logic [31:0] mem [0:N-1];
  task empty_statement;
    begin end
  endtask
  always_ff @(posedge clk) begin
    empty_statement;
  end
  assign q = mem[0];
endmodule
