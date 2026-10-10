module top;
  logic [1:0] subject;
  logic [3:0] result;
  initial begin
    subject = 2'd1;
    case (subject)
      2'd0, 2'd1: result = 4'd5;
      2'd1: result = 4'd9;
      default: result = 4'd0;
    endcase
    if (result == 4'd5) begin
      subject = 2'd3;
      case (subject)
        2'd0, 2'd1: result = 4'd1;
        2'd2, 2'd3: result = 4'd7;
        2'd3: result = 4'd9;
        default: result = 4'd0;
      endcase
      if (result == 4'd7)
        $display("PASS");
      else
        $display("FAIL");
    end else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: 465cfa6986e05e5d4ff15c6f xrun(64) 24.03-s004 2026-10-10T02:18:28Z; PASS.
