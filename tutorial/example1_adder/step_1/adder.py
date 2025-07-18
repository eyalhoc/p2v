
# step 1: create a module that receives two 8 bit inputs and outputs the sum

from p2v import p2v # all modules inherit the p2v class

class adder(p2v):
    def module(self):
        self.set_modname()
        
        a = self.input("a", 8)
        b = self.input("b", 8)
        o = self.output("o", 8)
        
        self.assign(o, a + b)
        
        return self.write()

