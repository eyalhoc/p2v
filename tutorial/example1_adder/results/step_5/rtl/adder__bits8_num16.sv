module adder__bits8_num16 (
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
    output logic [7:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 8 (int) #  data width
    //  * num = 16 (int) #  number of inputs

    logic [7:0] data_out0;
    logic valid_out0;
    adder__bits8_num8 adder0 (
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
        .o(data_out0),  // output
        .valid_out(valid_out0)  // output
    );

    logic [7:0] data_out1;
    logic valid_out1;
    adder__bits8_num8 adder1 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .i0(i8),  // input
        .i1(i9),  // input
        .i2(i10),  // input
        .i3(i11),  // input
        .i4(i12),  // input
        .i5(i13),  // input
        .i6(i14),  // input
        .i7(i15),  // input
        .o(data_out1),  // output
        .valid_out(valid_out1)  // output
    );

    adder__bits8_num2 adder_out (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid((valid_out0 & valid_out1)),  // input
        .i0(data_out0),  // input
        .i1(data_out1),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );


endmodule  // adder__bits8_num16
