/* A named literal timeformat is inert when no time consumer exists. */
module top;
  integer unit;
  integer precision;
  integer width;
  initial begin
    unit = -9;
    precision = 2;
    width = 10;
    $timeformat(unit, precision, " ns", width);
    $display("PASS");
    $finish;
  end
endmodule
