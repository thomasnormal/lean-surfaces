module top;
  timeunit 1ns;
  timeprecision 1ns;
  logic [3:0] selector=4'b1xz0;
  int choice=0;
  initial begin
    casez(selector)
      4'b1??0: begin #2; choice=1; end
      4'bx1?0: begin #2; choice=2; end
      default: choice=3;
    endcase
    $display("casez %0d live %b",choice,selector);
    casex(selector)
      4'b0101: begin #2; choice=4; end
      default: choice=5;
    endcase
    $display("casex %0d live %b",choice,selector);
    $finish;
  end
  initial begin
    #1; selector=4'bx101;
    #2; selector=4'b1110;
  end
endmodule
