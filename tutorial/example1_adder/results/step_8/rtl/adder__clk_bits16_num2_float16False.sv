module adder__clk_bits16_num2_float16False (
    input logic clk,
    input logic reset,
    input logic valid,
    input logic [15:0] data_in__0,
    input logic [15:0] data_in__1,
    output logic [15:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_srst() (p2v_clock) # None
    //  * bits = 16 (int) #  data width
    //  * num = 2 (int) #  number of inputs
    //  * float16 = False (bool) #  use a float16 adder

    logic [15:0] o_pre;
    assign o_pre = (data_in__0 + data_in__1);
    always_ff @(posedge clk)
        if (reset) o <= 16'd0;
        else if (valid) o <= o_pre;

    always_ff @(posedge clk)
        if (reset) valid_out <= 1'd0;
        else valid_out <= valid;


endmodule  // adder__clk_bits16_num2_float16False
