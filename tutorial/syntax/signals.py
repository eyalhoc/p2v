
from p2v import p2v, misc, clock, default_clk

num = 4
bits = 8
var = True

strct = {}
strct["ctrl"] = 8
strct["data"] = 32

strct_handshake = {}
strct_handshake["ctrl"] = 8
strct_handshake["data"] = 32
strct_handshake["valid"] = 1.0 # value reserved to mark qualifier
strct_handshake["ready"] = -1.0 # value reserved to mark back pressure


class signals(p2v):
    def module(self):
        self.set_modname()
        
        self.logic("a") # default is single bit
        self.logic("b", 1) # same as the above
        self.logic("c", 8) # multi bit bus
        self.logic("d", bits) # parametric width
        self.logic("e", [bits]) # parametric width but forces [0:0] bus if width is 1
        
        for n in range(num):
            self.logic(f"f{n}", bits) # port in loop
        
        if var:
            self.logic("g", bits*2) # conditional port
            self.logic("h", bits*2) # conditional port
        
        
        clk = default_clk
        clk2 = clock("clk2", rst_n="clk2_rstn")
        self.logic(clk) # p2v clock
        self.logic(clk2) # p2v clock
        
        self.assign(clk.name, "1'b1") # clock assignment
        self.assign(clk.rst_n, "1'b1") # reset assignment
        
        self.parameter("BITS", 32) # Verilog parameter
        
        self.logic("z", "BITS", assign="'0") # Verilog parametric port
        self.allow_unused("z")
        
        self.parameter("IDLE", "2'd0", local=True) # local parameter
        self.logic("iii", 2, assign="IDLE")
        self.allow_unused("iii")
        
        self.line() # insert empty line to Verilog file
        self.assign("b", "1'b1") # assign to const
        self.assign("e", misc.dec(3, bits)) # assign to const
        for n in range(num):
            self.assign(f"f{n}", "d | e") # assign expression
        self.assign("a", "b") # trivial Verilog assign
        self.assign("c", 0) # assign to const
        self.assign("d", f"e + {misc.dec(1, bits)}") # assign expression
        self.assign("g", misc.concat(["f0", "f1"])) # assign conctenation
        self.assign(misc.bits("h", bits), "f2") # partial bits
        self.assign(misc.bits("h", bits, start=bits), "f3") # partial bits
        
        self.line() # insert empty line to Verilog file
        self.assign(clk2.rst_n, "1'b1")
        self.assign(clk2, clk)
        
        self.allow_unused([clk2, clk.rst_n])
        
        self.logic("aa", 8, assign=misc.hex(-1, 8)) # inline assignment
        self.logic("bb", 8, initial=misc.hex(-1, 8)) # inline initial assignment
        self.allow_unused(["aa", "bb"])
        
        # struct assignment
        self.line() # insert empty line to Verilog file
        self.logic("s", strct) # data struct as Python dictionary
        self.logic("t", strct) # data struct as Python dictionary
        self.assign("t", "s") # struct assignment
        self.allow_undriven("s")
        
        # struct assignment with field change
        s1 = self.logic("s1", strct) # data struct as Python dictionary
        t1 = self.logic("t1", strct) # data struct as Python dictionary
        self.assign(t1["ctrl"], "d") # struct assignment
        self.assign("t1", "s1") # struct assignment
        self.allow_undriven("s1")
        
        # struct assignment with control
        self.line() # insert empty line to Verilog file
        s2 = self.logic("s2", strct_handshake) # data struct as Python dictionary
        t2 = self.logic("t2", strct_handshake) # data struct as Python dictionary
        self.assign("t2", "s2") # struct assignment (ready assignment will be reversed: s2.ready = t2.ready)
        self.allow_undriven(["s2", t2["ready"]])
        
        self.allow_unused(["t", "t1", "t2", s1["ctrl"]])
        
        
        self.allow_unused(["a", "b", "c", "d", "e"])
        for n in range(num):
            self.allow_unused(f"f{n}")
        
        if var:
            self.allow_unused(["g", "h"])
            
        return self.write()

