`timescale 1ns/1ps

module plain_always_kinds_step11_tb;
    logic clk = 1'b0;
    logic [1:0] sel;
    logic [3:0] d;
    logic [3:0] q;
    logic [3:0] q_old;
    logic [3:0] q_case;

    plain_always_kinds_step11 dut (.*);
    task automatic row(input logic [1:0] select, input logic [3:0] value);
        clk = 1'b0;
        #1;
        sel = select;
        d = value;
        #1 clk = 1'b1;
        #1 $display("ROW %b %b %b", q, q_old, q_case);
    endtask

    task automatic clock_row(input logic next_clk, input logic [3:0] value);
        sel = 2'b00;
        d = value;
        #1 clk = next_clk;
        #1 $display("ROW %b %b %b", q, q_old, q_case);
    endtask

    initial begin
        sel = 2'bxx;
        d = 4'bxxxx;
        #1 $display("ROW %b %b %b", q, q_old, q_case);
        row(2'b00, 4'b0000);
        row(2'b1x, 4'b0011);
        row(2'b1z, 4'bxz01);
        row(2'b00, 4'bzzzz);
        row(2'b11, 4'b1010);
        row(2'b00, 4'b0110);
        clk = 1'b0;
        #1;
        clock_row(1'bx, 4'b1001); // 0 -> x is a positive edge.
        clock_row(1'bz, 4'b0001); // x -> z is not an edge.
        clock_row(1'b1, 4'b0101); // z -> 1 is a positive edge.
        clock_row(1'bx, 4'b1111); // 1 -> x is a negative edge.
        clock_row(1'b1, 4'bzzzz); // x -> 1 is a positive edge.
        clk = 1'b0;
        #1;
        clock_row(1'bz, 4'b0011); // 0 -> z is a positive edge.
        $finish;
    end
endmodule
