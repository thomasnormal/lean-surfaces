// SPDX-License-Identifier: Apache-2.0
// A pure constant expression in a user-function return is materialized in sv-0.2.
module symbolic_constant_function (
  output logic [3:0] y
);
  function automatic logic [3:0] nine(input logic selector);
    return 4'd3 + 4'd6;
  endfunction
  assign y = nine(1'b0);
endmodule
