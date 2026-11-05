module qualified_case_pre_edge(input logic clk, input logic d, output logic q);
  always_ff @(posedge clk) begin
    unique case (q)
      1'b0: q <= d;
    endcase
  end
endmodule
