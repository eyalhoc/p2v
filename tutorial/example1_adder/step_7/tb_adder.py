
# tb step 1: create a test bench that drives inputs and tests sum of adder

from p2v import p2v, misc, clock

import adder

class tb_adder(p2v):
    def module(self, async_reset=True, size=32):
        self.set_param(async_reset, bool) # sync reset or async reset
        self.set_param(size, int, size > 0) # number of inputs to test
        self.set_modname("tb") # explicitly set module name
        
        if async_reset:
            clk = clock("clk", rst_n="resetn")
        else:
            clk = clock("clk", reset="reset")
        
        self.logic(clk)
        self.tb.gen_clk(clk, cycle=self.tb.rand_int(2, 20))
        
        
        args = adder.adder(self).gen_rand_args(override={"float16":False}) # float16 is not yet supported
        num = args["num"]
        bits = args["bits"]
        
        valid = self.logic("valid")
        inputs = []
        for n in range(num):
            inputs.append(self.logic(f"i{n}", bits, initial=0))
        o = self.logic("o", bits)
        valid_out = self.logic("valid_out")
            
        son = adder.adder(self).module(clk, **args)
        son.connect_in(clk)
        son.connect_in("valid")
        for n in range(num):
            son.connect_in(f"i{n}")
        son.connect_out("o")
        son.connect_out("valid_out")
        son.inst()
        
        
        en = self.logic("en", initial=0)
        valid = self.sample(clk, valid, en)
        
        self.tb.fifo("data_in_q", bits*num)
        self.tb.fifo("expected_q", bits)
        data_in = self.logic("data_in", bits*num, initial=0)
        expected = self.logic("expected", bits, initial=0)
        
        self.line(f"""
                    initial
                        begin
                   """)
        for i in range(size):
            input_vec = []
            input_sum = 0
            for j in range(num):
                val = self.tb.rand_int(1<<bits)
                input_sum += val
                input_vec.append(misc.hex(val, bits))
            self.line(f"data_in_q.push_back({misc.concat(input_vec)});")
            self.line(f"expected_q.push_back({misc.hex(input_sum, bits)});")
        self.line(f"""
                        end
                   """)
        
        
        self.line(f"""
                    initial
                        begin
                            {misc.cond(async_reset, f"@(posedge {clk.rst_n});")}
                            repeat (10) @(posedge {clk});
                            en = 1;
                        end
                        
                        // drive inputs
                        always @(posedge {clk})
                            if (valid && (data_in_q.size() > 0))
                                begin
                                    data_in = data_in_q.pop_front();
                                    {misc.concat(inputs)} = data_in;
                                end
                                
                        // check output
                        always @(posedge {clk})
                            if (valid_out)
                                begin
                                    expected = expected_q.pop_front();
                                    {self.tb.test_fail(condition=o != expected, message="mismatch expected: 0x%0h, actual: 0x%0h", params=[expected, o])}
                                    if (expected_q.size() == 0)
                                        {self.tb.test_pass(message=f"successfully tested {size} additions")}
                                end
                   """)
        
        
        self.allow_unused([valid_out, o, data_in, expected])
        
        
        self.tb.set_timeout(clk, size * 100)
        self.tb.dump()

        return self.write()
