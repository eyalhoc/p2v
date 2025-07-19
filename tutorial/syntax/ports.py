
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
        
        a = self.input() # default is single bit
        b =self.input(1) # same as the above
        c = self.input(8) # multi bit bus
        dd = self.input(bits) # parametric width
        e = self.input([bits]) # parametric width but forces [0:0] bus if width is 1
        
        f = []
        for n in range(num):
            f.append(self.input(f"f{n}", bits)) # port in loop
        
        if var:
            g = self.input(bits*2) # conditional port
        
        ao = self.output() # default is single bit
        bo = self.output(1) # same as the above
        co = self.output(8) # multi bit bus
        ddo = self.output(bits) # parametric width
        eo = self.output([bits]) # parametric width but forces [0:0] bus if width is 1
        
        fo = []
        for n in range(num):
            fo.append(self.output(f"f{n}o", bits)) # port in loop
        
        if var:
            go = self.output(bits*2) # conditional port
        
        lst =  [a, b, c, dd, e]
        for n in range(num):
            lst.append(f[n])
        if var:
            lst.append(g)
        for x in lst:
            self.assign(f"{x}o", x)
        
        
        q = self.inout() #inout ports width is always 1
        
        s = self.input(strct) # data struct as Python dictionary
        t = self.output(strct) # data struct as Python dictionary
        
        self.assign(t, s)
        
        
        self.parameter("BITS", 32) # Verilog parameter
        
        z = self.input("z", "BITS") # Verilog parametric port - name must be explicit
        zo = self.output("zo", "BITS") # Verilog parametric port - name must be explicit
        
        self.assign(zo, z)
        
        return self.write()

