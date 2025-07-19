
from p2v import p2v, misc

import _or_gate

class instances(p2v):
    def module(self, num=4, bits=32):
        self.set_param(num, int, 0 < num < 8)
        self.set_param(bits, int, bits > 0)
        self.set_modname()
        
        a = []
        b = []
        c = []
        for n in range(num):
            a.append(self.input(f"a{n}", bits+n))
            b.append(self.input(f"b{n}", bits+n))
            c.append(self.output(f"c{n}", bits+n))
        
            son = _or_gate._or_gate(self).module(bits=bits+n) # creates son module
            son.connect_in(son.a, a[n])
            son.connect_in(son.b, b[n])
            son.connect_out(son.c, c[n])
            son.inst(suffix=n) # make instance name unique

        
        a = self.input(16)
        b = self.input(16)
        c = self.output(16)
        son = _or_gate._or_gate(self).module(bits=16)
        son.connect_in(a) # assumes wire name equals port name
        son.connect_in(b) # assumes wire name equals port name
        son.connect_out(c) # assumes wire name equals port name
        son.inst("my_or_gate") # specific instance name
    
        
        ca = self.output(16)
        son = _or_gate._or_gate(self).module(bits=16)
        son.connect_out(son.c, ca)
        son.connect_auto() # trivially connects all missing ports (wire name equals port name)
        son.inst("my_auto_connect_or") # specific instance name
        
        
        son = _or_gate._or_gate(self).module(bits=16)
        son.connect_auto(ports=True, suffix="_01") # 
        son.inst("my_auto_connect_ports_or") # specific instance name
        
        
        # Verilog instance
        aa = self.input(bits)
        bb = self.input(bits)
        cc = self.output(bits)
        son = self.verilog_module("_and_gate", params={"BITS":bits}) # setting instance Verilog parameter
        son.connect_in(son.a, aa) # connecting Verilog is same as connecting a p2v instance
        son.connect_in(son.b, bb) # connecting Verilog is same as connecting a p2v instance
        son.connect_out(son.c, cc) # connecting Verilog is same as connecting a p2v instance
        son.inst() # instance name equals module name
        
        return self.write()

