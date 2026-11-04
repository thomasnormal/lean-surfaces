// A child instance in a generate-if whose condition depends on the loop genvar.
module generate_if_instance_fixed_child (
  input logic a,
  output logic y
);
  assign y = a;
endmodule

module generate_if_instance_fixed #(parameter int N = 2) (
  input logic [N-1:0] a,
  output logic [N-1:0] y
);
  assign y[0] = 1'b0;
  for (genvar i = 0; i < N; i++) begin : g
    if (i == 1) begin : hit
      generate_if_instance_fixed_child u (.a(a[i]), .y(y[i]));
    end
  end
endmodule
