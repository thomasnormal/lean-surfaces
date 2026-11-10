module always_event_generate_refusal_step11_tb;
    logic a = 0;
    wire y;
    always_event_generate_refusal_step11 dut(a, y);
    initial begin
        // Observe only explicit input events, after process startup.
        #2; a = 1;
        #1; $display("ROW one %b", y);
        a = 0;
        #1; $display("ROW zero %b", y);
        a = 1'bx;
        #1; $display("ROW x %b", y);
        a = 1'bz;
        #1; $display("ROW z %b", y);
        $finish;
    end
endmodule
