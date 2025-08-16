module adder__bits16_num4_float16False (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic [15:0] data_in__0,
    input logic [15:0] data_in__1,
    input logic [15:0] data_in__2,
    input logic [15:0] data_in__3,
    output logic [15:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 16 (int) #  data width
    //  * num = 4 (int) #  number of inputs
    //  * float16 = False (bool) #  use a float16 adder

    logic [15:0] datas__0;
    logic valids__0;
    adder__bits16_num2_float16False adder0 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .data_in__0(data_in__0),  // input
        .data_in__1(data_in__1),  // input
        .o(datas__0),  // output
        .valid_out(valids__0)  // output
    );

    logic [15:0] datas__1;
    logic valids__1;
    adder__bits16_num2_float16False adder1 (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid(valid),  // input
        .data_in__0(data_in__2),  // input
        .data_in__1(data_in__3),  // input
        .o(datas__1),  // output
        .valid_out(valids__1)  // output
    );

    adder__bits16_num2_float16False adder_out (
        .clk(clk),  // input
        .rst_n(rst_n),  // input
        .valid((valids__0 & valids__1)),  // input
        .data_in__0(datas__0),  // input
        .data_in__1(datas__1),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );


endmodule  // adder__bits16_num4_float16False
