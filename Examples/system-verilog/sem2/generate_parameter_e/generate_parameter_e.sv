module generate_parameter_e #(parameter integer W = 8)(input logic x, output logic y);
  if (W > 4) assign y = x;
  else assign y = !x;
endmodule
