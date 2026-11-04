// SPDX-License-Identifier: Apache-2.0
// A short pure chain of local initializers with an implicit return.
module symbolic_local_chain_implicit_function (
  input logic [3:0] a,
  output logic [3:0] y
);
  function automatic logic [3:0] bump(input logic [3:0] x);
    logic [3:0] t = x + 4'd1;
    logic [3:0] u = t + 4'd1;
    bump = u;
  endfunction
  assign y = bump(a);
endmodule
