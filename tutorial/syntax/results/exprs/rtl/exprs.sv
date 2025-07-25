module exprs (
    input logic [7:0] a,
    input logic [7:0] b,
    output logic [7:0] bitwise,
    output logic boolean,
    output logic [10:0] lshift,
    output logic [7:0] rshift
);

    // exprs module parameters:

    assign bitwise = (a + b) | (a - b) & (a * b) ^ (a - b) | ~(a);
    assign boolean = (a == b) | (a != b) | (a > b) | (a >= b) | (a < b) | (a <= b);
    assign lshift  = {a, 3'd0};
    assign rshift  = {3'd0, b[7:3]};

endmodule  // exprs
