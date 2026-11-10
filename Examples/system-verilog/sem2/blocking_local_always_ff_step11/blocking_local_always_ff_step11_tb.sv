`timescale 1ns/1ps

module blocking_local_always_ff_step11_tb;
    logic clk = 1'b0;
    logic [3:0] d;
    logic [3:0] q;
    logic [3:0] q_not;

    blocking_local_always_ff_step11 dut (.*);

    always #5 clk = ~clk;

    task automatic row(input logic [8*24-1:0] name,
                       input logic [3:0] value);
        begin
            @(negedge clk);
            d = value;
            @(posedge clk);
            #1 $display("ROW %0s q=%b q_not=%b", name, q, q_not);
        end
    endtask

    initial begin
        d = 4'bxxxx;
        #1 $display("ROW first q=%b q_not=%b", q, q_not);
        row("local_0000", 4'b0000);
        row("local_1010", 4'b1010);
        row("local_xz01", 4'bxz01);
        row("local_zzzz", 4'bzzzz);
        $finish;
    end
endmodule
