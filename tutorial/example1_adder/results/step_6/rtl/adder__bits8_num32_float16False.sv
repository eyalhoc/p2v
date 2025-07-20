module adder__bits8_num32_float16False (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic [7:0] i0,
    input logic [7:0] i1,
    input logic [7:0] i2,
    input logic [7:0] i3,
    input logic [7:0] i4,
    input logic [7:0] i5,
    input logic [7:0] i6,
    input logic [7:0] i7,
    input logic [7:0] i8,
    input logic [7:0] i9,
    input logic [7:0] i10,
    input logic [7:0] i11,
    input logic [7:0] i12,
    input logic [7:0] i13,
    input logic [7:0] i14,
    input logic [7:0] i15,
    input logic [7:0] i16,
    input logic [7:0] i17,
    input logic [7:0] i18,
    input logic [7:0] i19,
    input logic [7:0] i20,
    input logic [7:0] i21,
    input logic [7:0] i22,
    input logic [7:0] i23,
    input logic [7:0] i24,
    input logic [7:0] i25,
    input logic [7:0] i26,
    input logic [7:0] i27,
    input logic [7:0] i28,
    input logic [7:0] i29,
    input logic [7:0] i30,
    input logic [7:0] i31,
    output logic [7:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 8 (int) #  data width
    //  * num = 32 (int) #  number of inputs
    //  * float16 = False (bool) #  use a float16 adder

    logic [7:0] o0;
    logic valid_out0;
    adder__bits8_num16_float16False adder0 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .i0(i0),  // input
        .i1(i1),  // input
        .i2(i2),  // input
        .i3(i3),  // input
        .i4(i4),  // input
        .i5(i5),  // input
        .i6(i6),  // input
        .i7(i7),  // input
        .i8(i8),  // input
        .i9(i9),  // input
        .i10(i10),  // input
        .i11(i11),  // input
        .i12(i12),  // input
        .i13(i13),  // input
        .i14(i14),  // input
        .i15(i15),  // input
        .o(o0),  // output
        .valid_out(valid_out0)  // output
    );

    logic [7:0] o1;
    logic valid_out1;
    adder__bits8_num16_float16False adder1 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .i0(i16),  // input
        .i1(i17),  // input
        .i2(i18),  // input
        .i3(i19),  // input
        .i4(i20),  // input
        .i5(i21),  // input
        .i6(i22),  // input
        .i7(i23),  // input
        .i8(i24),  // input
        .i9(i25),  // input
        .i10(i26),  // input
        .i11(i27),  // input
        .i12(i28),  // input
        .i13(i29),  // input
        .i14(i30),  // input
        .i15(i31),  // input
        .o(o1),  // output
        .valid_out(valid_out1)  // output
    );

    adder__bits8_num2_float16False adder_out (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid((valid_out0 & valid_out1)),  // input
        .i0(o0),  // input
        .i1(o1),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );


endmodule  // adder__bits8_num32_float16False
