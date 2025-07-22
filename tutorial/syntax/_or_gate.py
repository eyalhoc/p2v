
from p2v import p2v

class _or_gate(p2v):
    def module(self, bits=8):
        self.set_param(bits, int, bits > 0)
        self.set_modname()
        
        a = self.input(bits)
        b = self.input(bits)
        c = self.output(bits)
        
        self.assign(c, a | b)
        
        return self.write()

