// SPDX-License-Identifier: Apache-2.0
// Fixed-width one-hot predicates count definite one bits; x/z bits are ignored.
module onehot_fixed (
  input logic [3:0] a,
  output logic one,
  output logic zero
);
  assign one = $onehot(a);
  assign zero = $onehot0(a);
endmodule
