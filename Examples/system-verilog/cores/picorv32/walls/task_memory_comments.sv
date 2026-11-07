module task_memory_comments #(parameter int N = 4) (
  input logic clk, output logic [31:0] q
);
  logic [31:0] mem [0:N-1];
  task empty_statement;
    // This task is used by the `assert directive in non-formal mode to
    // avoid empty statement (which are unsupported by plain Verilog syntax).
    begin end
  endtask
  always_ff @(posedge clk) begin
    empty_statement;
  end
  assign q = mem[0];
endmodule
