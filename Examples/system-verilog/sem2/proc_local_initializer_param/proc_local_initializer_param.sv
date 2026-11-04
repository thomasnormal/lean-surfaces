// SPDX-License-Identifier: Apache-2.0
// A closed parameter initializer on a static always_comb local is hoisted.
module proc_local_initializer_param #(
  parameter logic [7:0] B = 8'h5a
) (
  input  logic [7:0] a,
  output logic [7:0] y
);
  always_comb begin
    logic [7:0] bias = B;
    y = a ^ bias;
  end
endmodule
