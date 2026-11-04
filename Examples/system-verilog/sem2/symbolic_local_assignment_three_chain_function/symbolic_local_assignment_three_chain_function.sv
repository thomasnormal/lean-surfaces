// SPDX-License-Identifier: Apache-2.0
// Three pure locals assigned once before an explicit return.
module symbolic_local_assignment_three_chain_function (
  input logic [3:0] a,
  output logic [3:0] y
);
  function automatic logic [3:0] bump(input logic [3:0] x);
    logic [3:0] t;
    logic [3:0] u;
    logic [3:0] v;
    t = x + 4'd1;
    u = t + 4'd1;
    v = u + 4'd1;
    return v;
  endfunction
  assign y = bump(a);
endmodule
