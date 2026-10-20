module top;
  parameter int CHOICE = 2;
  if (CHOICE == 1) begin : first
    int value = 11;
  end else if (CHOICE == 2) begin : second
    int value = 22;
  end else begin : dead
    string unsupported_value = "unused";
  end
  case (CHOICE)
    1: begin : case_first
      int value = 1;
    end
    2: begin : selected
      logic [3:0] value = 4'ha;
      initial value = 4'hc;
    end
    default: begin : case_dead
      string unsupported_value;
    end
  endcase
  begin : outer
    logic [7:0] value = 8'h55;
    begin : inner
      logic [7:0] value = 8'haa;
    end
  end
  for (genvar i=0; i<0; i++) begin : empty
    string unsupported_value;
  end
  initial begin
    #1;
    $display("scopes %0d %h %h %h", second.value, selected.value, outer.value, outer.inner.value);
    $finish;
  end
endmodule
