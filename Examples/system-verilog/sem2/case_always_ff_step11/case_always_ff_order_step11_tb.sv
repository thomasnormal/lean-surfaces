`timescale 1ns/1ps
module case_always_ff_order_step11_tb;
    logic clk = 1'b0;
    logic [1:0] sel;
    logic [3:0] d;
    logic [3:0] q, q_hold, q_empty, q_nested;
    case_always_ff_order_step11 dut (.*);

    task automatic row(input logic [1:0] s, input logic [3:0] v);
        begin
            clk = 0; sel = s; d = v;
            #5 clk = 1;
            #1 $display("ROW %b %b %b %b", q, q_hold, q_empty, q_nested);
        end
    endtask

    initial begin
        #1 $display("ROW %b %b %b %b", q, q_hold, q_empty, q_nested);
        row(2'b00, 4'b0101);
        row(2'b01, 4'bzzzz);
        row(2'b1x, 4'bxxxx);
        row(2'bz1, 4'bxz01);
        row(2'b11, 4'b0110);
        row(2'b00, 4'b1010);
        $finish;
    end
endmodule
