module always_star_generate_step11_tb;
    logic [6:0] a = 0, b = 0;
    logic [2:0] lane_a = 0;
    wire [3:0] y_a, y_b;
    wire [6:0] y_wide;
    wire [1:0] lanes_a, lanes_b;
    wire [2:0] lanes_wide;

    always_star_generate_step11 #(.W(4), .USE_A(1), .LANES(2)) selected_a
        (a[3:0], b[3:0], lane_a[1:0], y_a, lanes_a);
    always_star_generate_step11 #(.W(4), .USE_A(0), .LANES(2)) selected_b
        (a[3:0], b[3:0], lane_a[1:0], y_b, lanes_b);
    always_star_generate_step11 #(.W(7), .USE_A(1), .LANES(3)) wider
        (a, b, lane_a, y_wide, lanes_wide);

    task show(input string label);
        $display("ROW %s %b %b %b %b %b %b", label,
                 y_a, y_b, y_wide, lanes_a, lanes_b, lanes_wide);
    endtask

    initial begin
        // Each sample follows an explicit event after startup. Port startup
        // ordering is covered separately by the original fixture.
        #2; a = 7'b1010011; b = 7'b0101100; lane_a = 3'b101;
        #1; show("known");
        b = 7'b1110101;
        #1; show("b_only");
        a = 7'b0111000;
        #1; show("a_only");
        lane_a = 3'b110;
        #1; show("lane_only");
        a = 7'b1x0x01x;
        #1; show("a_x");
        a = 7'bz1z010z;
        #1; show("a_z");
        b = 7'b01x0x11;
        #1; show("b_x");
        b = 7'bz01zz10;
        #1; show("b_z");
        a = 7'b1000001; lane_a = 3'b0x1;
        #1; show("lane_x");
        lane_a = 3'bz10;
        #1; show("lane_z");
        a = 7'b0001110; b = 7'b1010010; lane_a = 3'b011;
        #1; show("recovered");
        $finish;
    end
endmodule
