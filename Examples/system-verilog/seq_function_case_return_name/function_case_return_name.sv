// Clean-room function-case wall: the default writes the function name while
// the explicit return publishes the local temporary, which remains x.
module function_case_return_name(input logic [3:0] a, output logic [3:0] y);
  function automatic logic [3:0] step(input logic [3:0] x);
    logic [3:0] t;
    begin
      unique case (x)
        4'h0: t = 4'h3;
        default: step = 4'hc;
      endcase
      return t;
    end
  endfunction
  assign y = step(a);
endmodule
