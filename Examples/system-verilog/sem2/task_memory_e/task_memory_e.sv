// Clean-room E witness: a referenced empty input-only task beside memory.
module task_memory_e #(parameter int N = 4) (
  input logic clk,
  input logic [7:0] d,
  output logic [7:0] q
);
  logic [7:0] mem [0:N-1];
  task empty_statement;
    begin end
  endtask

  always_ff @(posedge clk) begin
    empty_statement;
    mem[0] <= d;
  end
  assign q = mem[0];
endmodule
