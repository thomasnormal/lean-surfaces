// Refused construct: an automatic function with a local temporary and case.
// Refused by: the SV envelope loader/process evaluator.
// Exact message: unsupported expression 'CallExpression'
module function_case_eval(input logic [3:0] a, output logic [3:0] y);
  function automatic logic [3:0] step(input logic [3:0] x);
    logic [3:0] t;
    begin
      case (x)
        4'h0: t = 4'h3;
        default: t = 4'hc;
      endcase
      return t;
    end
  endfunction
  assign y = step(a);
endmodule
