module concat_nba_target_step11_tb;
    logic clk;
    logic [7:0] d;
    logic [7:0] q;

    concat_nba_target_step11 dut (.*);

    task automatic row;
        $display("ROW q=%b", q);
    endtask

    initial begin
        clk = 1'b0;
        d = 8'hA5;
        row();
        #1 row();
        clk = 1'b1;
        #1 row();
        clk = 1'b0;
        d = 8'h3C;
        #1 row();
        clk = 1'b1;
        #1 row();
        clk = 1'b0;
        d = 8'bx101_zz01;
        #1 row();
        clk = 1'b1;
        #1 row();
        $finish;
    end
endmodule
