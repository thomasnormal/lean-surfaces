// Dynamic unique0-case labels retain the qualifier boundary.
module top;
  initial begin
    int value;
    int label;
    int result;
    value = 2;
    label = 1;
    result = 0;
    unique0 case (value)
      label: result = 1;
      2: result = 2;
    endcase
  end
endmodule
