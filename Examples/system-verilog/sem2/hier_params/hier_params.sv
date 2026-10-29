// F3 differential design: parameter overrides (named, ordered, defaults),
// named and ordered port connections, expressions on input ports, an
// output into a part select, and three instances of ONE definition at
// three different parameter points.
module hp_child #(parameter int W = 2, parameter int K = W + 1) (
  input  logic [W-1:0] x,
  input  logic         en,
  output logic [K-1:0] y
);
  assign y = en ? {x, 1'b1} : '0;
endmodule

module hier_params #(parameter int N = 3) (
  input  logic [N-1:0] a,
  input  logic         e,
  output logic [N:0]   o1,
  output logic [N+2:0] o2,
  output logic [3:0]   o3
);
  hp_child #(.W(N)) c1 (.x(a), .en(e), .y(o1));
  hp_child #(N, N + 3) c2 (a, e & a[0], o2);
  hp_child c3 (.x(a[1:0] ^ 2'b11), .en(a[N-1] | e), .y(o3[2:0]));
  assign o3[3] = ^a;
endmodule
