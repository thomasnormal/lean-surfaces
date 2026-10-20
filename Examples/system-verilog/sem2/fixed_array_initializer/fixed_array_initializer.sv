// Pure assignment-pattern initialization is lowered into flat array cells.
module fixed_array_initializer (
    output logic [3:0] first,
    output logic [3:0] second
);
  logic [3:0] arr [0:1] = '{4'h1, 4'hx};

  assign first = arr[0];
  assign second = arr[1];
endmodule
