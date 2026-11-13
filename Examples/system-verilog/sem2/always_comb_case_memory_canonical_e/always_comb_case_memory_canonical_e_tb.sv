module always_comb_case_memory_canonical_e_tb;
  logic [1:0] sel = 0;
  logic [3:0] d = 4'hc;
  wire [3:0] q;
  always_comb_case_memory_canonical_e #(.W(4)) dut(.sel(sel), .d(d), .q(q));
  initial begin
    #1 $display("ROW i=0 q=%b", q);
    sel = 2'd1; #1 $display("ROW i=1 q=%b", q);
    sel = 2'd2; #1 $display("ROW i=2 q=%b", q);
    d = 4'h5; #1 $display("ROW i=3 q=%b", q);
    $finish;
  end
endmodule
