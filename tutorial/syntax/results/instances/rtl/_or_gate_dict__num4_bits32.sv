module _or_gate_dict__num4_bits32 (
    input  logic [31:0] i__0__w,
    input  logic [31:0] i__0__r,
    output logic [31:0] c__0,
    input  logic [31:0] i__1__w,
    input  logic [31:0] i__1__r,
    output logic [31:0] c__1,
    input  logic [31:0] i__2__w,
    input  logic [31:0] i__2__r,
    output logic [31:0] c__2,
    input  logic [31:0] i__3__w,
    input  logic [31:0] i__3__r,
    output logic [31:0] c__3
);

    // _or_gate_dict module parameters:
    //  * num = 4 (int) #  number of inputs
    //  * bits = 32 (int) #  data width

    assign c__0 = (i__0__w | i__0__r);
    assign c__1 = (i__1__w | i__1__r);
    assign c__2 = (i__2__w | i__2__r);
    assign c__3 = (i__3__w | i__3__r);

endmodule  // _or_gate_dict__num4_bits32
