module untyped_localparam_refuse_tb;
  logic [31:0] k,a,k2,a2;
  untyped_localparam_refuse d(.k(k),.a(a));
  untyped_localparam_refuse #(.N(8)) e(.k(k2),.a(a2));
  initial begin #1; $display("ROW N=10000 k=%0d a=%0d",k,a); $display("ROW N=8 k=%0d a=%0d",k2,a2); $finish; end
endmodule
