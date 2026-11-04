// SPDX-License-Identifier: Apache-2.0
// Two pure locals assigned once before an explicit return.
module symbolic_local_assignment_chain_function (
  input logic [3:0] a,
  output logic [3:0] y
);
  function automatic logic [3:0] bump(input logic [3:0] x);
    logic [3:0] t;
    logic [3:0] u;
    t = x + 4'd1;
    u = t + 4'd1;
    return u;
  endfunction
  assign y = bump(a);
endmodule
