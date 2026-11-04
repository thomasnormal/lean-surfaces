// Outside the FF-only profile: a two-process dependency cycle through blocking temporaries.
// Each process reads the temporary the other writes, so the result depends on the order they run in.
module temp_cycle(input logic clk, input logic [3:0] d, output logic [3:0] a, b);
  logic [3:0] t1, t2;
  always_ff @(posedge clk) begin
    t1 = d;
    a <= t2;
  end
  always_ff @(posedge clk) begin
    t2 = t1;
    b <= t1;
  end
endmodule
