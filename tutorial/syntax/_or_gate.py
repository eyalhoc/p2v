
from p2v import p2v

class _or_gate(p2v):
    def module(self, bits=8):
        self.set_param(bits, int, bits > 0)
        self.set_modname()
        
        self.input("a", bits)
        self.input("b", bits)
        self.output("c", bits)
        
        self.assign("c", "a | b")
        
        return self.write()

