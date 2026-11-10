`timescale 1ns/1ps
module static_local_lifetime_step11_tb;
    logic clk = 0;
    logic reset, load;
    logic [3:0] d;
    wire [3:0] q_old, q_new, q_shadow, q_known;
    wire [7:0] q_signed;
    static_local_lifetime_step11 dut (.*);
    task automatic show;
        $display("ROW %b %b %b %b %b", q_old, q_new, q_shadow, q_known, q_signed);
    endtask
    task automatic row(input logic r, l, input logic [3:0] value);
        clk = 0; reset = r; load = l; d = value;
        #5 clk = 1;
        #1 show();
        #4;
    endtask
    initial begin
        reset = 0; load = 0; d = 0;
        #1 show();
        row(0, 0, 4'b0000);
        row(0, 1, 4'b1010);
        row(0, 0, 4'b1111);
        row(0, 1, 4'bxz01);
        row(0, 0, 4'b0000);
        row(0, 1, 4'bzzzz);
        row(0, 0, 4'b1111);
        row(1, 0, 4'b0000);
        row(0, 0, 4'b1111);
        $finish;
    end
endmodule
