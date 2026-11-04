// SPDX-License-Identifier: Apache-2.0
// A pure function may return a parameter without a runtime call frame.
module symbolic_parameter_function #(
  parameter logic [3:0] P = 4'd9
) (
  output logic [3:0] y
);
  function automatic logic [3:0] choose(input logic selector);
    return P;
  endfunction
  assign y = choose(1'b0);
endmodule
