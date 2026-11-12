module initial_enum_checks_e_tb;
  logic [1:0] a; logic y;
  initial begin a=0; #1; if (y!==0) $fatal; a=1; #1; if (y!==1) $fatal; a=2; #1; if(y!==0) $fatal; $display("PASS"); $finish; end
  initial_enum_checks_e dut(.a(a),.y(y));
endmodule
