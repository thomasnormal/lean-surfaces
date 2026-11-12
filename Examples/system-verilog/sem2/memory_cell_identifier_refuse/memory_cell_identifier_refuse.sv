module generated_cell(input logic clk, input logic [7:0] d, output logic [7:0] q);
  genvar i;
  generate for (i = 0; i < 2; i = i + 1) begin : cells
    logic [7:0] cell;
    always_ff @(posedge clk) cell <= d;
    assign q = cell;
  end endgenerate
endmodule
