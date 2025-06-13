
from p2v import p2v, misc

import _or_gate

class instances(p2v):
    def module(self, num=4, bits=32):
        self.set_param(num, int, 0 < num < 8)
        self.set_param(bits, int, bits > 0)
        self.set_modname()
        
        for n in range(num):
            self.input(f"a{n}", bits+n)
            self.input(f"b{n}", bits+n)
            self.output(f"c{n}", bits+n)
        
            son = _or_gate._or_gate(self).module(bits=bits+n) # creates son module
            son.connect_in("a", f"a{n}")
            son.connect_in("b", f"b{n}")
            son.connect_out("c", f"c{n}")
            son.inst(suffix=n) # make instance name unique

        
        self.input(["a", "b"], 16)
        self.output("c", 16)
        son = _or_gate._or_gate(self).module(bits=16)
        son.connect_in("a") # assumes wire name equals port name
        son.connect_in("b") # assumes wire name equals port name
        son.connect_out("c") # assumes wire name equals port name
        son.inst("my_or_gate") # specific instance name
    
        
        self.output("ca", 16)
        son = _or_gate._or_gate(self).module(bits=16)
        son.connect_out("c", "ca")
        son.connect_auto() # trivially connects all missing ports (wire name equals port name)
        son.inst("my_auto_connect_or") # specific instance name
        
        
        son = _or_gate._or_gate(self).module(bits=16)
        son.connect_auto(ports=True, suffix="_01") # 
        son.inst("my_auto_connect_ports_or") # specific instance name
        
        
        # Verilog instance
        self.input(["aa", "bb"], bits)
        self.output("cc", bits)
        son = self.verilog_module("_and_gate", params={"BITS":bits}) # setting instance Verilog parameter
        son.connect_in("a", "aa") # connecting Verilog is same as connecting a p2v instance
        son.connect_in("b", "bb") # connecting Verilog is same as connecting a p2v instance
        son.connect_out("c", "cc") # connecting Verilog is same as connecting a p2v instance
        son.inst() # instance name equals module name
        
        return self.write()

