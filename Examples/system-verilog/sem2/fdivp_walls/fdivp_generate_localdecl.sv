module generate_wall #(parameter int NS=8) (input logic [NS-1:0] a, output logic [NS-1:0] y);
  genvar i;
  generate for (i=0; i<NS; i++) begin : g
    localparam int SH = 2**(NS-1-i);
    logic top_a, top_b;
    assign top_a = a[i];
    assign top_b = top_a;
    assign y[i] = top_b;
  end endgenerate
endmodule
