module _or_gate__bits34 (
    input  logic [33:0] a,
    input  logic [33:0] b,
    output logic [33:0] c
);

    // _or_gate module parameters:
    //  * bits = 34 (int) # None

    assign c = (a | b);

endmodule  // _or_gate__bits34
