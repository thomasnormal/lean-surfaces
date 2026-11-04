// A named structural generate block wrapping an instance loop.
module named_generate_wrapper_loop_child (
  input logic a,
  output logic y
);
  assign y = a;
endmodule

module named_generate_wrapper_loop #(parameter int N = 2) (
  input logic [N-1:0] a,
  output logic [N-1:0] y
);
  generate begin : lanes
    for (genvar i = 0; i < N; i++) begin : lane
      named_generate_wrapper_loop_child u (.a(a[i]), .y(y[i]));
    end
  end endgenerate
endmodule
