// SPDX-License-Identifier: Apache-2.0
// A pure local temporary in a function is erased into the caller expression.
module symbolic_local_function (
  input logic [3:0] a,
  output logic [3:0] y
);
  function automatic logic [3:0] bump(input logic [3:0] x);
    logic [3:0] t;
    t = x + 4'd1;
    return t;
  endfunction
  assign y = bump(a);
endmodule
