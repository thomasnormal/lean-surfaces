// SPDX-License-Identifier: Apache-2.0
// A discarded pure input-only function call is an empty symbolic statement.
module symbolic_statement_function (
  input logic [3:0] a,
  output logic [3:0] y
);
  function automatic logic [3:0] id(input logic [3:0] x);
    return x;
  endfunction
  always_comb begin
    id(a);
    y = a;
  end
endmodule
