// SPDX-License-Identifier: Apache-2.0
// WP-PROC N3: the top is a module that another module of the same file instantiates (`--top pt_child`).
module pt_child (input logic [3:0] a, output logic [3:0] y);
  assign y = ~a;
endmodule

module pt_parent (input logic [3:0] a, output logic [3:0] y);
  pt_child u (.a(a), .y(y));
endmodule
