// Outside the FF-only profile: a blocking self-read and write in always_ff
// (the process reads the window it writes with a blocking assignment).
module blocking_self(input logic clk, output logic [3:0] q);
  logic [3:0] x;
  always_ff @(posedge clk) begin
    x = x + 4'd1;
    q <= x;
  end
endmodule
