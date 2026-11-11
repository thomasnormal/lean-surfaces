`timescale 1ns/1ps
module always_star_case_latch_e_tb;
    logic [1:0] sel = 2'b00;
    logic [3:0] d = 4'b0011;
    wire [3:0] q;
    always_star_case_latch_e #(.W(4)) dut (.sel(sel), .d(d), .q(q));

    task automatic row(input string label);
        #1 $display("ROW %s sel=%b d=%b q=%b", label, sel, d, q);
    endtask

    initial begin
        row("first");
        sel = 2'b01; row("invert");
        sel = 2'b10; row("hold_unmatched");
        d = 4'b1010; row("hold_data");
        sel = 2'b00; row("capture");
        sel = 2'bxz; row("hold_xz");
        sel = 2'b01; d = 4'bzzzz; row("invert_z");
        sel = 2'b11; row("hold_last");
        $finish;
    end
endmodule
