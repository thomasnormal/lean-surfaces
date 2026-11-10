`timescale 1ns/1ps
module dynamic_nba_issue_step11_tb;
    logic clk = 0;
    logic reset;
    logic [2:0] idx, idx2;
    logic signed [2:0] sidx;
    logic [1:0] d, cursor;
    logic [3:0] q, signed_q, old_q;
    logic [3:0][1:0] words;
    logic [7:0] old_words;
    dynamic_nba_issue_step11 dut (.*);

    task automatic show;
        $display("ROW %b %b %b %b %b %b", cursor, q, signed_q, old_q, words, old_words);
    endtask
    task automatic row(input logic r, input logic [2:0] i, j,
                       input logic signed [2:0] s, input logic [1:0] value);
        clk = 0; reset = r; idx = i; idx2 = j; sidx = s; d = value;
        #5 clk = 1;
        #1 show();
        #4;
    endtask
    initial begin
        reset = 1; idx = 0; idx2 = 0; sidx = 0; d = 0;
        #1 show();
        row(1, 0, 0, 0, 0);
        row(0, 3, 1, 1, 2'b10); // cursor update cannot redirect its earlier sample
        row(0, 2, 2, 2, 2'b10); // last of the overlapping NBAs wins
        row(0, 1, 0, -1, 2'bzz); // signed negative write holds; z data retained
        row(0, 3'bx0x, 3'bz01, 3'bxxx, 2'b01);
        row(0, 3'bz01, 3'bx10, 3'bz01, 2'bxz);
        row(0, 4, 7, -4, 2'b11); // both out-of-range and signed-negative holds
        row(0, 0, 3, 3, 2'bx0);
        row(0, 3, 0, 0, 2'b0z);
        row(0, 1, 1, 1, 2'b01);
        row(1, 0, 0, 0, 0);
        row(0, 0, 0, 0, 2'b10); // all three same-bit NBAs: last zero wins
        $finish;
    end
endmodule
