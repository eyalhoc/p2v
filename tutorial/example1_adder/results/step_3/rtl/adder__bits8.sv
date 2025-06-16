module adder__bits8 (
    input logic clk,
    input logic rst_n,
    input logic valid,
    input logic [7:0] a,
    input logic [7:0] b,
    output logic [7:0] o,
    output logic valid_out
);

    // module parameters:
    // clk = p2v_clock.clk_arst() (p2v_clock)
    // bits = 8 (int) # data width

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) o <= 8'd0;
        else if (valid) o <= a + b;

    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) valid_out <= 1'd0;
        else valid_out <= valid;


endmodule
