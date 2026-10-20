module top;
  logic[7:0] four_state;
  bit[7:0] two_state;
  initial begin
    four_state=(8'hxz:8'hzz:8'hxx);
    two_state=(8'b1x0z1010:8'b01xz0101:8'bzzzz0011);
    $display("states %h %b",four_state,two_state);
    $finish;
  end
endmodule
