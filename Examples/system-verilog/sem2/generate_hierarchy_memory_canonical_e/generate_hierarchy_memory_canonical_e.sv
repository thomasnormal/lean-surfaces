module generate_hierarchy_memory_child #(parameter integer W=4)(input logic clk,input logic [W-1:0] d,output logic [W-1:0] q);
  logic [W-1:0] s [2];
  always_ff @(posedge clk) s[0] <= d;
  assign q = s[0];
endmodule
module generate_hierarchy_memory_canonical_e #(parameter integer N=1,parameter integer W=4)(input logic clk,input logic [W-1:0] d,output logic [W-1:0] q0);
  genvar g;
  generate for(g=0;g<N;g++) begin : gen
    generate_hierarchy_memory_child #(.W(W)) c(.clk(clk),.d(d),.q(q0));
  end endgenerate
endmodule
