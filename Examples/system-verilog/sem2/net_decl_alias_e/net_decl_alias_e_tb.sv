`timescale 1ns/1ps
module net_decl_alias_e_tb;
  logic a;
  wire q;
  net_decl_alias_e dut(.a(a), .q(q));

  task automatic row(input logic [8*4-1:0] name, input logic value);
    begin
      a = value;
      #1 $display("ROW %0s q=%b", name, q);
    end
  endtask

  initial begin
    row("zero", 1'b0);
    row("one", 1'b1);
    row("x", 1'bx);
    row("z", 1'bz);
    $finish;
  end
endmodule
