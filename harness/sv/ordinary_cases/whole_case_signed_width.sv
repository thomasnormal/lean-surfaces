module top;
  logic signed [3:0] subject;
  logic [3:0] result;
  initial begin
    subject = 4'b1111;
    case (subject)
      8'shff: result = 4'd1;
      4'sh0: result = 4'd0;
      default: result = 4'd9;
    endcase
    if (result == 4'd1) begin
      case (subject)
        8'shff: result = 4'd1;
        4'sh0: result = 4'd0;
        16'h000f: result = 4'd3;
        default: result = 4'd9;
      endcase
      if (result == 4'd3)
        $display("PASS");
      else
        $display("FAIL");
    end else
      $display("FAIL");
    $finish;
  end
endmodule
// REFERENCE: c2e55dbb70453301d187cb87 xrun(64) 24.03-s004 2026-10-10T02:18:36Z; PASS.
