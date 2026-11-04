// SPDX-License-Identifier: Apache-2.0
// A pure local blocking assignment feeding an implicit function return.
module symbolic_local_function_implicit (
  input logic [3:0] a,
  output logic [3:0] y
);
  function automatic logic [3:0] bump(input logic [3:0] x);
    logic [3:0] t;
    t = x + 4'd1;
    bump = t;
  endfunction
  assign y = bump(a);
endmodule
