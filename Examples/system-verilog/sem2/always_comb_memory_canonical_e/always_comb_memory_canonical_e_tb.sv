module always_comb_memory_canonical_e_tb;
  logic clk = 0;
  logic en = 0;
  logic [3:0] d = 0;
  wire [3:0] q;
  always_comb_memory_canonical_e #(.W(4)) dut(.clk(clk), .en(en), .d(d), .q(q));
  initial begin
    #1 $display("ROW i=0 q=%b", q);
    d = 4'h5; clk = 1; #1 $display("ROW i=1 q=%b", q);
    clk = 0; en = 1; d = 4'h9; #1 $display("ROW i=2 q=%b", q);
    en = 0; #1 $display("ROW i=3 q=%b", q);
    $finish;
  end
endmodule
