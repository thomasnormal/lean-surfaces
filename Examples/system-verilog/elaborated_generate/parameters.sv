module top;
  parameter logic [3:0] UNKNOWN = 4'b10xz;
  parameter int signed NEGATIVE = -3;
  localparam logic [7:0] WIDE = 8'hc7;
  logic [7:0] value = WIDE;
  initial begin
    $display("parameters %b %0d %h %0d", UNKNOWN, NEGATIVE, value, top.NEGATIVE);
    $finish;
  end
endmodule
