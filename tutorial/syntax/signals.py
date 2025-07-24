
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
        
        a = self.logic() # default is single bit
        b = self.logic(1) # same as the above
        c = self.logic(8) # multi bit bus
        d = self.logic(bits) # parametric width
        e = self.logic([bits]) # forces signal to be bus and not scalar even if 1 bit wide(range [0:0])
        
        f = []
        for n in range(num):
            f.append(self.logic(f"f{n}", bits)) # port in loop with explicit name
        
        if var:
            g = self.logic(bits*2) # conditional port
            h = self.logic(bits*2) # conditional port
            i = self.logic(bits*2) # conditional port
        
        
        clk = default_clk
        clk2 = clock("clk2", rst_n="clk2_rstn")
        self.logic(clk) # p2v clock
        self.logic(clk2) # p2v clock
        
        ext_clk = self.input()
        self.assign(clk.name, ext_clk) # clock assignment
        self.assign(clk.rst_n, 1) # reset assignment
        
        self.parameter("BITS", 32) # Verilog parameter
        
        z = self.logic("z", "BITS", assign=0) # Verilog parametric port
        self.allow_unused(z)
        
        IDLE = self.parameter("IDLE", "2'd0", local=True) # local parameter
        iii = self.logic(2, assign=IDLE)
        self.allow_unused(iii)
        
        self.line() # insert empty line to Verilog file
        self.assign(b, 1) # assign to const
        self.assign(e, misc.dec(3, bits)) # assign to const
        for n in range(num):
            self.assign(f[n], d | e) # assign expression
        self.assign(a, b) # trivial Verilog assign
        self.assign(c, 0) # assign to const
        self.assign(d, e + misc.dec(1, bits)) # assign expression
        if var:
            self.assign(g, misc.concat(f[:2])) # assign conctenation
            self.assign(h[0:bits], f[2]) # partial bits
            self.assign(h[bits:bits*2], f[3]) # partial bits
            for m in range(bits*2):
                self.assign(i[m], h[m]) # bit by bit
        
        q = self.logic(8, assign=7)
        qq = self.output(5)
        self.assign(qq, q[3:])
        
        self.line() # insert empty line to Verilog file
        self.assign(clk2.rst_n, 1)
        self.assign(clk2, clk)
        
        self.allow_unused([clk2, clk.rst_n])
        
        aa = self.logic(8, assign=misc.hex(-1, 8)) # inline assignment
        bb = self.logic(8, initial=misc.hex(-1, 8)) # inline initial assignment
        self.allow_unused([aa, bb])
        
        # struct assignment
        self.line() # insert empty line to Verilog file
        s = self.logic(strct) # data struct as Python dictionary
        t = self.logic(strct) # data struct as Python dictionary
        self.assign(t, s) # struct assignment
        self.allow_undriven(s)
        
        # struct assignment with field change
        s1 = self.logic(strct) # data struct as Python dictionary
        t1 = self.logic(strct) # data struct as Python dictionary
        self.assign(t1.ctrl, d) # struct assignment
        self.assign(t1, s1) # struct assignment
        self.allow_undriven(s1)
        
        # struct assignment with control
        self.line() # insert empty line to Verilog file
        s2 = self.logic(strct_handshake) # data struct as Python dictionary
        t2 = self.logic(strct_handshake) # data struct as Python dictionary
        self.assign(t2, s2) # struct assignment (ready assignment will be reversed: s2.ready = t2.ready)
        self.allow_undriven([s2, t2.ready])
        
        self.allow_unused([t, t1, t2, s1.ctrl])
        
        
        self.allow_unused([a, b, c, d, e])
        for n in range(num):
            self.allow_unused(f[n])
        
        if var:
            self.allow_unused([g, h, i])
            
        return self.write()

