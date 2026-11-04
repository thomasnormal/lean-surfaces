// SPDX-License-Identifier: Apache-2.0
// A pure conditional user-function return inlines as a typed ternary.
module symbolic_conditional_function (
  input logic c,
  input logic [3:0] a,
  input logic [3:0] b,
  output logic [3:0] y
);
  function automatic logic [3:0] mux(input logic s,
                                      input logic [3:0] x,
                                      input logic [3:0] z);
    if (s) return x;
    else return z;
  endfunction
  assign y = mux(c, a, b);
endmodule
