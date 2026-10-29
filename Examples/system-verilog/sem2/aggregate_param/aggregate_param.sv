// A localparam typed with a packed struct whose width depends on a
// parameter: its type is emitted unrecoverable (`packed: null`), so the
// instantiation is loud instead of reading the DEFAULT width (37 truncated
// to 5 bits) at every point.
module aggregate_param #(parameter int N = 3) (
  input  logic         a,
  output logic [N+1:0] o
);
  typedef struct packed { logic [N-1:0] x; logic [1:0] y; } st_t;
  localparam st_t P = 37;
  assign o = P;
endmodule
