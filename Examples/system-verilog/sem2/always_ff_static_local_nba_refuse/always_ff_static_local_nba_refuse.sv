// A static block-local NBA target in a loop remains outside the exact tier.
module always_ff_static_local_nba_refuse (
  input logic clk,
  input logic d,
  output logic q
);
  always_ff @(posedge clk) begin : proc
    logic t;
    for (int i = 0; i < 2; i++) begin
      t <= d;
    end
    q <= t;
  end
endmodule
