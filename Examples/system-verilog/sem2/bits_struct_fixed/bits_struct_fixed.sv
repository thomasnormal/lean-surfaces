// A packed struct and union whose layout is FIXED at every point, inside a
// parameterized module: kept, exact at every point — member windows, `$bits`
// in labels (reads and a target), and a cell array over a fixed dimension.
module bits_struct_fixed #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [31:0]  v,
  input  logic [2:0]   c,
  output logic [N+5:0] o,
  output logic [1:0]   o1,
  output logic [1:0]   o2,
  output logic [2:0]   x,
  output logic [N-1:0] m1,
  output logic [N+7:0] y
);
  localparam int L = 3;
  typedef struct packed { logic [L-1:0] x; logic [2:0] y; } st_t;
  typedef union packed { logic [3:0] p; logic [3:0] q; } u_t;
  st_t s;
  u_t uv;
  logic [N-1:0] mem [0:1];
  assign s = {c, ~c};
  assign uv = v[3:0];
  assign o = {a, s};
  assign x = s.x;
  assign o1 = v[$bits(s) +: 2];
  assign o2 = v[$bits(uv) - 1 -: 2];
  assign mem[0] = a;
  assign mem[1] = ~a;
  assign m1 = mem[1];
  always_comb begin
    y = '0;
    y[$bits(s) + 1 -: 2] = c[1:0];
  end
endmodule
