// `$bits` of a packed struct/union whose layout depends on a parameter, in
// select labels (verifier rows `vg1`, `vj1`): its width would be the DEFAULT
// point's at every point. Refused at the declaration
// (`VariableSymbol:default-point-aggregate`) and at the labels
// (`…:query-label`).
module bits_aggregate #(parameter int N = 3) (
  input  logic [N-1:0] a,
  input  logic [31:0]  v,
  input  logic [1:0]   b,
  output logic [1:0]   o1,
  output logic [1:0]   o2,
  output logic [31:0]  y
);
  typedef struct packed { logic [N-1:0] x; logic [1:0] y; } st_t;
  typedef union packed { logic [N-1:0] x; logic [N-1:0] y; } u_t;
  st_t s;
  u_t uv;
  assign s = {a, b};
  assign uv = a;
  assign o1 = v[$clog2($bits(s)) +: 2];
  assign o2 = v[$bits(uv) +: 2];
  always_comb begin
    y = '0;
    y[$bits(s) - 1 -: 2] = b;
  end
endmodule
