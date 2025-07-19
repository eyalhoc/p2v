module _or_gate__bits8 (
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] c
);

    // _or_gate module parameters:
    //  * bits = 8 (int) # None

    assign c = a | b;

endmodule  // _or_gate__bits8
