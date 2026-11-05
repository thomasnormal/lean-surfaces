// A qualified case in a pure automatic function.  The labels are distinct
// and the default arm makes every qualifier claim hold for every input.
module function_unique_case_eval(input logic [3:0] a, output logic [3:0] y);
  function automatic logic [3:0] step(input logic [3:0] x);
    logic [3:0] t;
    begin
      unique case (x)
        4'h0: t = 4'h3;
        4'h1: t = 4'h4;
        default: t = 4'hc;
      endcase
      return t;
    end
  endfunction
  assign y = step(a);
endmodule
