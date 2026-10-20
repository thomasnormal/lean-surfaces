module top;
  if (2'b1x) begin : definite
    int value = 1;
  end else begin : false_dead
    string unsupported_value;
  end
  if (1'bx) begin : unknown_dead
    string unsupported_value;
  end else begin : ambiguous
    int value = 2;
  end
  case (2'bxz)
    2'bxz: begin : exact
      int value = 3;
    end
    default: begin : other_dead
      string unsupported_value;
    end
  endcase
  initial begin
    $display("choices %0d %0d %0d", definite.value, ambiguous.value, exact.value);
    $finish;
  end
endmodule
