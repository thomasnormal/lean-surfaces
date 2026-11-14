// Canonical-E clean-room fixture: a parameter-sized unpacked array crosses a
// child instance boundary (§23.3.3, IEEE 1800-2023).
module unpacked_port_parameterized_child #(parameter int W = 4, parameter int N = 2) (
  input logic [W-1:0] a [N],
  output logic [W-1:0] y
);
  assign y = a[0] ^ a[1];
endmodule

module unpacked_port_parameterized_canonical_e #(parameter int W = 4, parameter int N = 2) (
  input logic [W-1:0] data [N],
  output logic [W-1:0] y
);
  unpacked_port_parameterized_child #(.W(W), .N(N)) u (.a(data), .y(y));
endmodule
