module _or_gate__bits32 (
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] c
);

    // _or_gate module parameters:
    //  * bits = 32 (int) # None

    assign c = (a | b);

endmodule  // _or_gate__bits32
