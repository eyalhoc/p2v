
from p2v import p2v

num = 4
bits = 8
var = True

strct = {}
strct["ctrl"] = 8
strct["data"] = 32

class ports(p2v):
    def module(self):
        self.set_modname()
        
        self.input("a") # default is single bit
        self.input("b", 1) # same as the above
        self.input("c", 8) # multi bit bus
        self.input("dd", bits) # parametric width
        self.input("e", [bits]) # parametric width but forces [0:0] bus if width is 1
        
        for n in range(num):
            self.input(f"f{n}", bits) # port in loop
        
        if var:
            self.input("g", bits*2) # conditional port
        
        self.output("ao") # default is single bit
        self.output("bo", 1) # same as the above
        self.output("co", 8) # multi bit bus
        self.output("ddo", bits) # parametric width
        self.output("eo", [bits]) # parametric width but forces [0:0] bus if width is 1
        
        for n in range(num):
            self.output(f"f{n}o", bits) # port in loop
        
        if var:
            self.output("go", bits*2) # conditional port
        
        lst =  ["a", "b", "c", "dd", "e"]
        for n in range(num):
            lst.append(f"f{n}")
        if var:
            lst.append("g")
        for x in lst:
            self.assign(f"{x}o", x)
        
        
        self.inout("q") #inout ports width is always 1
        
        self.input("s", strct) # data struct as Python dictionary
        self.output("t", strct) # data struct as Python dictionary
        
        self.assign("t", "s")
        
        
        self.parameter("BITS", 32) # Verilog parameter
        
        self.input("z", "BITS") # Verilog parametric port
        self.output("zo", "BITS") # Verilog parametric port
        
        self.assign("zo", "z")
        
        return self.write()

