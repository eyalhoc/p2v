module _or_gate_dict__num2_bits8 (
    input  logic [7:0] i__0__w,
    input  logic [7:0] i__0__r,
    output logic [7:0] c__0,
    input  logic [7:0] i__1__w,
    input  logic [7:0] i__1__r,
    output logic [7:0] c__1
);

    // _or_gate_dict module parameters:
    //  * num = 2 (int) #  number of inputs
    //  * bits = 8 (int) #  data width

    assign c__0 = (i__0__w | i__0__r);
    assign c__1 = (i__1__w | i__1__r);

endmodule  // _or_gate_dict__num2_bits8
