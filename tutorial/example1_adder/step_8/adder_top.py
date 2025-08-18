
from p2v import p2v, misc

import adder

class adder_top(p2v):
    def module(self):
        self.set_modname()

        args = adder.adder(self).gen_rand_args() # get random args
        clk = args["clk"]
        
        self.remark("""
                    clock and reset generation
                    """)
        self.output(clk)
        self.tb.gen_clk(clk, cycle=self.tb.rand_int(5, 25))

        son = adder.adder(self).module(**args)
        son.connect_in(clk)
        son.connect_auto(ports=True)
        son.inst()

        self.tb.set_timeout(clk, 10000)

        return self.write()

