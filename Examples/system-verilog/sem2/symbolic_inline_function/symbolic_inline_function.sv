// SPDX-License-Identifier: Apache-2.0
// Pure input-only functions retained as source-shaped calls in the symbolic tree.
module symbolic_inline_function (
  input logic [3:0] a,
  output logic [3:0] y,
  output logic [3:0] z
);
  function automatic logic [3:0] id(input logic [3:0] x);
    return x;
  endfunction
  function automatic logic [3:0] bump(input logic [3:0] x);
    return x + 4'd1;
  endfunction
  assign y = id(a);
  assign z = bump(a);
endmodule
