
from p2v import p2v, misc

class _or_gate_list(p2v):
    def module(self, num=2, bits=8):
        self.set_param(num, int, num > 0) # number of inputs
        self.set_param(bits, int, bits > 0) # data width
        self.set_modname()
        
        i = {}
        for n in range(num):
            i[n] = self.input(bits)
        c = self.output(bits)
        
        self.assign(c, misc.concat(i, sep="|"))
        
        return self.write()

