// Output-port declaration initializers, ANSI forms that share one
// declaration (`output logic [1:0] y5 = 2'b01, y6 = 2'b10`) and a packed
// struct port (2026-10-28, round 4 Lane A). Icarus 12.0 and Xcelium 24.03
// give the same trace; Yosys 0.53 does not parse the shared declaration
// ("SystemVerilog interface in module port list cannot have a default
// value") and asserts on the struct port, so it is not a witness here.
typedef struct packed { logic hi; logic lo; } pi_ansi_multi_t;
module pi_ansi_multi (
  input  logic           clk,
  input  logic           a,
  output logic     [1:0] y5 = 2'b01, y6 = 2'b10,
  output pi_ansi_multi_t y7 = 2'b10
);
  always @(posedge clk) begin
    y6[0] <= a;
    y7.lo <= a;
  end
endmodule
