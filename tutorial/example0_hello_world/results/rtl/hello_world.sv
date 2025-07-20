module hello_world (
    input  logic a,
    input  logic b,
    output logic o
);

    // hello_world module parameters:

    assign o = (a | b);

endmodule  // hello_world
