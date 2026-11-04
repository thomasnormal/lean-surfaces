// SPDX-License-Identifier: Apache-2.0
// A pure local declaration initializer feeding an implicit function return.
module symbolic_local_initializer_implicit_function (
  input logic [3:0] a,
  output logic [3:0] y
);
  function automatic logic [3:0] bump(input logic [3:0] x);
    logic [3:0] t = x + 4'd1;
    bump = t;
  endfunction
  assign y = bump(a);
endmodule
