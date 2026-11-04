// A priority-if chain without a fallback retains its no-match diagnostic.
module top;
  initial begin
    int value;
    int label;
    int result;
    value = 2;
    label = 2;
    result = 0;
    priority if (value == label)
      result = 1;
    else if (value == 1)
      result = 2;
  end
endmodule
