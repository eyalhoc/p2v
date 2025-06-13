
# step 1: create a module that receives two 8 bit inputs and outputs the sum
# step 2: make the number of bits parametric

from p2v import p2v

class adder(p2v):
    def module(self, bits=8):
        self.set_param(bits, int, bits > 0, remark="data width") # set_param(var, type, constraints)
        self.set_modname()
        
        self.input("a", bits)
        self.input("b", bits)
        self.output("o", bits)
        
        self.assign("o", "a + b")
        
        return self.write()

