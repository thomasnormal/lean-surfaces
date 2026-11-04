// A fixed packed struct with root signedness is one exact flat vector.
module signed_struct_fixed (
  input logic [7:0] a,
  output logic signed [7:0] y,
  output logic lt
);
  typedef struct packed signed { logic [7:0] x; } st_t;
  st_t s;
  always_comb begin
    s = a;
    y = s;
    lt = s < 8'sd0;
  end
endmodule
