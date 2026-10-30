// A priority case without a default retains its no-match diagnostic boundary.
module top;
  initial begin
    int value;
    int result;
    value = 0;
    result = 0;
    priority case (value)
      1: result = 1;
      2: result = 2;
    endcase
  end
endmodule
