// A fixed packed-struct signed member retains signed comparison semantics.
module signed_member_fixed (
  input logic signed [7:0] a,
  output logic lt
);
  typedef struct packed { logic signed [7:0] x; } st_t;
  st_t s;
  always_comb begin
    s.x = a;
    lt = s.x < 8'sd0;
  end
endmodule
