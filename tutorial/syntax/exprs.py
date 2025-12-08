
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
        o8_sel = self.input(3)
        o8 = self.output()
        o8_neg = self.output()

        o = {}
        for i in range(12):
            o[i] = self.output()


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

        self.assign(o8, {o8_sel: o7})
        self.assign(o8_neg, {o8_sel: ~o7})


        self.assign(o[0], (a + 2) == (2 + a))
        self.assign(o[1], (a * 2) == (2 * a))
        self.assign(o[2], (a | 2) == (2 | a))
        self.assign(o[3], (a & 2) == (2 & a))
        self.assign(o[4], (a ^ 2) == (2 ^ a))
        self.assign(o[5], (a == 2) == (2 == a))
        self.assign(o[6], (a != 2) == (2 != a))
        self.assign(o[7], (a > 2) == (2 < a))
        self.assign(o[8], (a < 2) == (2 > a))
        self.assign(o[9], (a >= 2) == (2 <= a))
        self.assign(o[10], (a <= 2) == (2 >= a))
        self.assign(o[11], (a - 2) == (-2 + a))

        return self.write()
