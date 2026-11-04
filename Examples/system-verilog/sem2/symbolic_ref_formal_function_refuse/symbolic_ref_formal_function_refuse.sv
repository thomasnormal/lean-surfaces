// Ref formals require runtime aliasing and copyback semantics.
module symbolic_ref_formal_function_refuse (
  input logic [3:0] a,
  output logic [3:0] y
);
  logic [3:0] tmp;
  function automatic logic [3:0] f(input logic [3:0] x,
                                    ref logic [3:0] out);
    out = x;
    return x + 4'd1;
  endfunction
  always_comb y = f(a, tmp);
endmodule
