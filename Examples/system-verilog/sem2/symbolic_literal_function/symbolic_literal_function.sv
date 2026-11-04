// SPDX-License-Identifier: Apache-2.0
// A pure literal-return user function is materialized in sv-0.2.
module symbolic_literal_function (
  output logic [3:0] y
);
  function automatic logic [3:0] seven(input logic selector);
    return 4'd7;
  endfunction
  assign y = seven(1'b0);
endmodule
