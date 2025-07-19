
from p2v import p2v, clock, default_clk

class params(p2v):
    def module(self, clk=default_clk, bits=8, name="foo", sample=False, d={}, depth=128):
        self.set_param(clk, clock) # p2v clock
        self.set_param(bits, int, bits > 0) # integer parameter
        self.set_param(name, str, name != "") # string parameter
        self.set_param(sample, bool) # bool parameter - no constraint
        self.set_param(d, dict, suffix="_".join(d.keys())) # dictionary parameter - complex parameter does not create suffix automatcically
        self.set_param(depth, int, suffix=None) # integer parameter - does not affect module name
        self.set_modname()
        
        return self.write()

