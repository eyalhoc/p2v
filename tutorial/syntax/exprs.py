
from p2v import p2v, misc, clock, default_clk

class exprs(p2v):
    def module(self):
        self.set_modname()

        a = self.input(8)
        b = self.input(8)
        bitwise = self.output(8)
        boolean = self.output()
        lshift = self.output(11)
        rshift = self.output(8)
        
        o0 = self.output(8)
        o1 = self.output(8)
        o2 = self.output(8)
        
        
        self.assign(bitwise, \
                            (a + b) | \
                            (a - b) & \
                            (a * b) ^ \
                            (a - b) | \
                            ~a \
                    )
                    
        self.assign(boolean, \
                            (a == b) | \
                            (a != b) | \
                            (a > b)  | \
                            (a >= b) | \
                            (a < b)  | \
                            (a <= b)   \
                   )          

        self.assign(lshift, a << 3)
        self.assign(rshift, b >> 3)
        
        self.assign(o0, a & 0)
        self.assign(o1, a | 0)
        self.assign(o2, a ^ 0)
        
        return self.write()

