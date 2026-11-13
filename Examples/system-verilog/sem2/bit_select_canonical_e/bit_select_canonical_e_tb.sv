`timescale 1ns/1ps
module bit_select_canonical_e_tb;
  logic [7:0] d;
  logic [2:0] idx;
  wire q0;
  wire qidx;
  bit_select_canonical_e #(.W(8)) dut(.*);
  initial begin
    d = 8'ha5; idx = 3'd3; #1;
    $display("ROW known q0=%b qidx=%b", q0, qidx);
    d = 8'h5a; idx = 3'd6; #1;
    $display("ROW second q0=%b qidx=%b", q0, qidx);
    d = 8'bxxxxxxxx; idx = 3'd3; #1;
    $display("ROW xvalue q0=%b qidx=%b", q0, qidx);
    d = 8'ha5; idx = 3'bxxx; #1;
    $display("ROW xindex q0=%b qidx=%b", q0, qidx);
    idx = 3'bzzz; #1;
    $display("ROW zindex q0=%b qidx=%b", q0, qidx);
    $finish;
  end
endmodule
