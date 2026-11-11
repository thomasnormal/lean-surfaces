`timescale 1ns/1ps
module always_star_timezero_e_tb;
    logic [3:0] a = 4'b0011;
    wire [3:0] y_star, y_comb;
    always_star_timezero_e #(.W(4)) dut (.a(a), .y_star(y_star), .y_comb(y_comb));

    task automatic row(input string label);
        #1 $display("ROW %s a=%b k=%b y_star=%b y_comb=%b", label, a, dut.k, y_star, y_comb);
    endtask

    initial begin
        row("first");
        a = 4'b1010; row("known");
        a = 4'bxz01; row("xz");
        a = 4'bzzzz; row("z");
        $finish;
    end
endmodule
