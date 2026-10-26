/*
:name: struct_array_field_windows
:description: §7.4 — fixed unpacked array elements inside an unpacked struct flatten to independent cells
:tags: 7.4 unpacked-struct fixed-array selected-write
:type: simulation
*/
module top;
  typedef struct {
    logic [3:0] values [0:1];
  } bucket_t;
  bucket_t bucket;
  int index;

  initial begin
    bucket.values[0] = 4'h1;
    bucket.values[1] = 4'h2;
    index = 1;
    bucket.values[index] = 4'h3;
    if (bucket.values[0] === 4'h1 && bucket.values[1] === 4'h3)
      $display("PASS");
    else
      $display("FAIL");
    $finish;
  end
endmodule
