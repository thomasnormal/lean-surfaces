// A source-pure function with initialized and assigned locals.
module symbolic_mixed_local_function (
  input logic [3:0] a,
  output logic [3:0] y
);
  function automatic logic [3:0] bump(input logic [3:0] x);
    logic [3:0] t = x + 4'd1;
    logic [3:0] u;
    u = t + 4'd1;
    return u;
  endfunction
  assign y = bump(a);
endmodule
