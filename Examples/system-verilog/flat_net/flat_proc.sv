// A FLAT design with an `always_comb`: no parameter, no generate loop. The `always_comb` is the LAST
// process of the file and writes a bit of the vector output `y`, the shape that made `sv_equations` give
// up naming its equations (see `proc_hint.lean`).
module flat_proc (
  input  logic       a, b, c,
  output logic       t,
  output logic [1:0] y
);
  assign t    = a ^ b;
  assign y[0] = a & c;
  always_comb begin
    if (c) y[1] = t;
    else   y[1] = a & b;
  end
endmodule
