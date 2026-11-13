module memory_shape_d_canonical_e_tb;
  logic clk=0; logic [3:0] d4=0; logic [7:0] d8=0; logic [1:0] idx=0;
  wire [3:0] q4, selected4; wire [7:0] q8, selected8;
  memory_shape_d_canonical_e #(.W(4)) dut4(.clk(clk), .d(d4), .idx(idx), .q(q4), .selected(selected4));
  memory_shape_d_canonical_e #(.W(8)) dut8(.clk(clk), .d(d8), .idx(idx), .q(q8), .selected(selected8));
  initial begin
    #1; $display("ROW W=4 i=0 q=%b selected=%b",q4,selected4);
    d4=1; d8=1; idx=0; clk=1; #1; $display("ROW W=4 i=1 q=%b selected=%b",q4,selected4);
    d4=2; d8=2; idx=2'bxx; clk=0; #1; $display("ROW W=4 i=2 q=%b selected=%b",q4,selected4);
    $finish;
  end
endmodule
