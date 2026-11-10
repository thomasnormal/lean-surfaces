`timescale 1ns/1ps
module reset_event_iff_tb;
  logic clk, rn, rp, en, d;
  wire guarded_n, guarded_p, plain_n, plain_p;
  reset_event_iff dut (.*);
  initial begin
    clk=0; rn=1; rp=0; en=0; d=1;
    #1 clk=1; #1 clk=0;
    #1 rn=0; rp=1;
    #1 $display("ROW disabled %b%b%b%b", guarded_n, guarded_p, plain_n, plain_p);
    if ({guarded_n, guarded_p, plain_n, plain_p} !== 4'b1100) $fatal(1, "disabled reset guard");
    rn=1; rp=0; en=1;
    #1 rn=0; rp=1;
    #1 $display("ROW enabled %b%b%b%b", guarded_n, guarded_p, plain_n, plain_p);
    if ({guarded_n, guarded_p, plain_n, plain_p} !== 4'b0000) $fatal(1, "enabled reset guard");
    $finish;
  end
endmodule
