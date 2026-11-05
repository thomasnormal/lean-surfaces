module srt_case #(parameter int N = 1)(input logic [2:0] da, input logic [N-1:0] dummy, output logic [6:0] t2);
  always_comb begin
    case (da)
      3'd0: t2 = 7'd12;
      3'd1: t2 = 7'd13;
      3'd2: t2 = 7'd14;
      3'd3: t2 = 7'd15;
      3'd4: t2 = 7'd16;
      3'd5: t2 = 7'd17;
      3'd6: t2 = 7'd18;
      default: t2 = 7'd19;
    endcase
  end
endmodule
