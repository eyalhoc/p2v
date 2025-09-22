module exprs (
    input logic [7:0] a,
    input logic [7:0] b,
    output logic [7:0] bitwise,
    output logic boolean,
    output logic [10:0] lshift,
    output logic [7:0] rshift,
    output logic [7:0] o0,
    output logic [7:0] o1,
    output logic [7:0] o2,
    output logic [7:0] o3,
    output logic [7:0] o4,
    output logic [7:0] o5,
    output logic [7:0] o6,
    output logic [7:0] o7
);


    assign bitwise = (((a + b) | (((a - b) & (a * b)) ^ (a - b))) | ~a);
    assign boolean = ((((((a == b) | (a != b)) | (a > b)) | (a >= b)) | (a < b)) | (a <= b));
    assign lshift = {a, 3'd0};
    assign rshift = {3'd0, b[7:3]};
    assign o0 = 8'd0;
    assign o1 = a;
    assign o2 = a;
    assign o3 = (8'd0 - a);
    assign o4 = bitwise[0] ? a : bitwise[1] ? b : bitwise[2] ? o1 : 8'd0;
    assign o5 = bitwise[0] ? a : bitwise[1] ? b : o1;
    assign {o6, o7} = bitwise[0] ? {a, b} : bitwise[1] ? {b, a} : bitwise[2] ? {2{o1}} : 16'd0;

endmodule  // exprs
