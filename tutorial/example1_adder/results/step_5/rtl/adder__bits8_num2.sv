module adder__bits8_num2 (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic [7:0] i0,
    input logic [7:0] i1,
    output logic [7:0] o,
    output logic valid_out
);

    // adder module parameters:
    //  * clk = clk_arst() (p2v_clock) # None
    //  * bits = 8 (int) #  data width
    //  * num = 2 (int) #  number of inputs

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) o <= 8'd0;
        else if (valid) o <= i0 + i1;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) valid_out <= 1'd0;
        else valid_out <= valid;


endmodule
