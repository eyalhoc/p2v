module tb ();

    // tb_adder module parameters:
    //  * async_reset = True (bool) #  sync reset or async reset
    //  * size = 4 (int) #  number of inputs to test

    logic clk;
    logic resetn;

    initial
        forever begin
            clk = 0;
            #3;
            clk = 1;
            #3;
        end


    initial begin
        resetn = 1;
        repeat (5) @(negedge clk);  // async reset occurs not on posedge of clock
        resetn = 0;
        repeat (20) @(posedge clk);
        resetn = 1;
    end

    logic valid;
    logic [15:0] inputs__0;
    initial inputs__0 = 16'd0;

    logic [15:0] inputs__1;
    initial inputs__1 = 16'd0;

    logic [15:0] inputs__2;
    initial inputs__2 = 16'd0;

    logic [15:0] inputs__3;
    initial inputs__3 = 16'd0;

    logic [15:0] o;
    logic valid_out;
    adder__clk_bits16_num4_float16False adder (
        .clk(clk),  // input
        .resetn(resetn),  // input
        .valid(valid),  // input
        .data_in__0(inputs__0),  // input
        .data_in__1(inputs__1),  // input
        .data_in__2(inputs__2),  // input
        .data_in__3(inputs__3),  // input
        .o(o),  // output
        .valid_out(valid_out)  // output
    );

    logic en;
    initial en = 1'd0;

    always_ff @(posedge clk or negedge resetn)
        if (!resetn) valid <= 1'd0;
        else valid <= en;

    reg   [63:0] data_in_q [$];
    reg   [15:0] expected_q[$];
    logic [63:0] data_in;
    initial data_in = 64'd0;

    logic [15:0] expected;
    initial expected = 16'd0;


    initial begin

        data_in_q.push_back({16'h20a6, 16'h0f17, 16'h3f6a, 16'h3988});
        expected_q.push_back(16'ha8af);
        data_in_q.push_back({16'h3c72, 16'h3097, 16'h1adf, 16'h0c03});
        expected_q.push_back(16'h93eb);
        data_in_q.push_back({16'h3e72, 16'h03a0, 16'h31e5, 16'h3764});
        expected_q.push_back(16'hab5b);
        data_in_q.push_back({16'h0045, 16'h3902, 16'h2217, 16'h1d48});
        expected_q.push_back(16'h78a6);

    end


    initial begin
        @(posedge resetn);
        repeat (10) @(posedge clk);
        en = 1;
    end

    // drive inputs
    always @(posedge clk)
        if (valid && (data_in_q.size() > 0)) begin
            data_in = data_in_q.pop_front();
            {inputs__0, inputs__1, inputs__2, inputs__3} = data_in;
        end

    // check output
    always @(posedge clk)
        if (valid_out) begin
            expected = expected_q.pop_front();
            if ((o != expected)) begin
                $display("test FAILED: mismatch expected: 0x%0h, actual: 0x%0h", expected, o);
                #10;
                $finish;
            end

            if (expected_q.size() == 0) begin
                $display("test PASSED: successfully tested 4 additions");
                #10;
                $finish;
            end

        end

    logic [31:0] _count_timeout__clk;
    initial _count_timeout__clk = 32'd0;


    always @(posedge clk) _count_timeout__clk <= (_count_timeout__clk + 32'd1);

    reached_timeout_after_400_cycles_of_clk_assert :
    assert property (@(posedge clk) disable iff (!resetn) (_count_timeout__clk < 32'd400))
    else $fatal(1, "reached timeout after 400 cycles of clk");

    // CODE ADDED TO SUPPORT LEGACY SIMULATOR vvp THAT DOES NOT SUPPORT CONCURRENT ASSERTIONS
    logic assert_never__reached_timeout_after_400_cycles_of_clk;
    assign assert_never__reached_timeout_after_400_cycles_of_clk = ~((_count_timeout__clk < 32'd400));

    always @(posedge clk)
        if (resetn & assert_never__reached_timeout_after_400_cycles_of_clk)
            $fatal(1, "reached timeout after 400 cycles of clk");


    initial begin
        $dumpfile("dump.fst");
        $dumpvars;
        $dumpon;
    end


endmodule  // tb
