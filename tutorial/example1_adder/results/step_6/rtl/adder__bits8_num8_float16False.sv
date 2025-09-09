module adder__bits8_num8_float16False (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic [7:0] data_in__0,
    input logic [7:0] data_in__1,
    input logic [7:0] data_in__2,
    input logic [7:0] data_in__3,
    input logic [7:0] data_in__4,
    input logic [7:0] data_in__5,
    input logic [7:0] data_in__6,
    input logic [7:0] data_in__7,
    output logic [7:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 8 (int) #  data width
    //  * num = 8 (int) #  number of inputs
    //  * float16 = False (bool) #  use a float16 adder

    logic [7:0] datas__0;
    logic valids__0;
    adder__bits8_num4_float16False adder0 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input // assumes port name equals wire name
        .data_in__0(data_in__0),  // input[7:0]
        .data_in__1(data_in__1),  // input[7:0]
        .data_in__2(data_in__2),  // input[7:0]
        .data_in__3(data_in__3),  // input[7:0]
        .o(datas__0),  // output[7:0]
        .valid_out(valids__0)  // output
    );

    logic [7:0] datas__1;
    logic valids__1;
    adder__bits8_num4_float16False adder1 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input // assumes port name equals wire name
        .data_in__0(data_in__4),  // input[7:0]
        .data_in__1(data_in__5),  // input[7:0]
        .data_in__2(data_in__6),  // input[7:0]
        .data_in__3(data_in__7),  // input[7:0]
        .o(datas__1),  // output[7:0]
        .valid_out(valids__1)  // output
    );

    adder__bits8_num2_float16False adder_out (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid((valids__0 & valids__1)),  // input
        .data_in__0(datas__0),  // input[7:0]
        .data_in__1(datas__1),  // input[7:0]
        .o(o),  // output[7:0]
        .valid_out(valid_out)  // output
    );


endmodule  // adder__bits8_num8_float16False
