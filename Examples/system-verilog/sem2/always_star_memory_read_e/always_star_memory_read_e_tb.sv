`timescale 1ns/1ps
module always_star_memory_read_e_tb;
    logic clk = 1'b0;
    logic we = 1'b0;
    logic [1:0] widx = 2'b00;
    logic [1:0] ridx = 2'b00;
    logic [7:0] d = 8'b0;
    wire [7:0] q;

    always_star_memory_read_e #(.N(4)) dut (.*);

    task automatic row(input string label);
        #1 $display("ROW %s we=%b widx=%b ridx=%b d=%b q=%b", label, we, widx, ridx, d, q);
    endtask

    initial begin
        row("first");
        we = 1'b1; widx = 2'b10; d = 8'ha5; clk = 1'b1; #1; clk = 1'b0;
        row("write2");
        ridx = 2'b10; row("read2");
        ridx = 2'b01; row("read1");
        we = 1'b1; widx = 2'b01; d = 8'h3c; clk = 1'b1; #1; clk = 1'b0;
        row("write1");
        ridx = 2'b01; row("read1_after");
        ridx = 2'bxx; row("readx");
        ridx = 2'bzz; row("readz");
        ridx = 2'b11; row("read3");
        $finish;
    end
endmodule
