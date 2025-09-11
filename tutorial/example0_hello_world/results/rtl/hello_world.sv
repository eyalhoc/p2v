module hello_world (
    input  logic a,
    input  logic b,
    output logic o
);


    assign o = (a | b);

endmodule  // hello_world
