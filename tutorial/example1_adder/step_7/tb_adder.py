
# tb step 1: create a test bench that drives inputs and tests sum of adder

from p2v import p2v, misc, clock

import adder

class tb_adder(p2v):
    def module(self, async_reset=True, size=32):
        self.set_param(async_reset, bool) # sync reset or async reset
        self.set_param(size, int, size > 0) # number of inputs to test
        
        if async_reset:
            clk = clock("clk", rst_n="resetn")
        else:
            clk = clock("clk", reset="reset")
        
        args = adder.adder(self).gen_rand_args(override={"num":2, "float16":False}) # float16 is not yet supported
        num = args["num"]
        bits = args["bits"]
            
        son = adder.adder(self).module(clk, **args)
        
        