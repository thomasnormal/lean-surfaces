// Stateful and multiply-written function locals remain a loud call boundary.
module symbolic_stateful_function_refuse (
  input logic [3:0] a,
  output logic [3:0] y
);
  logic [3:0] state;
  function automatic logic [3:0] bump(input logic [3:0] x);
    state = x;
    state = state + 4'd1;
    return state;
  endfunction
  assign y = bump(a);
endmodule
