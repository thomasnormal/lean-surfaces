// Dynamic unique-if conditions retain the qualifier boundary.
module top;
  initial begin
    int value;
    int label;
    int result;
    value = 2;
    label = 2;
    result = 0;
    unique if (value == label)
      result = 1;
    else if (value == 1)
      result = 2;
  end
endmodule
