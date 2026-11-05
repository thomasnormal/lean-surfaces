module qualified_case_post_edge(input logic clk, input logic rstn, input logic d, output logic q);
  always_ff @(posedge clk or negedge rstn) begin
    if (!rstn) q <= 1'b0;
    else begin
      q <= d;
      unique case (q)
        1'b0: q <= d;
      endcase
    end
  end
endmodule
