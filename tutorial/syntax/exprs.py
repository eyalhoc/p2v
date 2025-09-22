
from p2v import p2v

class exprs(p2v):
    """ test exprs """
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
        o3 = self.output(8)
        o4 = self.output(8)
        o5 = self.output(8)
        o6 = self.output(8)
        o7 = self.output(8)


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

        self.assign(o3, -a)

        self.assign(o4, {bitwise[0]: a,
                         bitwise[1]: b,
                         bitwise[2]: o1
                        })

        self.assign(o5, {bitwise[0]: a,
                         bitwise[1]: b,
                         True: o1 # default
                        })

        self.assign([o6, o7], {bitwise[0]: [a, b],
                               bitwise[1]: [b, a],
                               bitwise[2]: [o1, o1]
                              })

        return self.write()
