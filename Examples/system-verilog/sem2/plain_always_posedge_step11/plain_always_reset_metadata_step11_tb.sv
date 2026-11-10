`timescale 1ns/1ps
module plain_always_reset_metadata_step11_tb;
    logic clk = 0, rn = 1, gate = 0, d = 1;
    wire q, r;
    plain_always_reset_metadata_step11 dut (.*);
    task automatic show(input string label);
        $display("ROW %s %b %b", label, q, r);
    endtask
    task automatic tick(input logic value);
        clk = 0; d = value;
        #4 clk = 1;
        #1;
        clk = 0;
        #1;
    endtask
    initial begin
        #1 show("first");
        tick(1); show("clock");
        rn = 0; #1 show("masked_reset");
        rn = 1; #1;
        tick(0); show("clock_gate_zero");
        tick(1); show("reload");
        gate = 1; rn = 0; #1 show("enabled_reset");
        rn = 1; #1;
        tick(1'bx); show("data_x");
        tick(1'bz); show("data_z");
        tick(1); show("reload_for_unknown_gate");
        gate = 1'bx; rn = 0; #1 show("gate_x");
        rn = 1; #1;
        gate = 1'bz; rn = 0; #1 show("gate_z");
        $finish;
    end
endmodule
