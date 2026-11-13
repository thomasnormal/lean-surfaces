// IEEE 1800-2023 §27.2: an initial process inside a generate branch remains
// source-shaped and executes once at time zero.
module generate_if_initial_canonical_e #(parameter integer N = 1) (
  output logic q
);
  generate
    if (N) begin : g_yes
      initial begin q = 1'b0; end
    end else begin : g_no
      initial begin q = 1'b1; end
    end
  endgenerate
endmodule
