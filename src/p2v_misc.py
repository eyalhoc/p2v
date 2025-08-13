# -----------------------------------------------------------------------------
#  Copyright (C) 2025 Eyal Hochberg (eyalhoc@gmail.com)
#
#  This file is part of an open-source Python-to-Verilog synthesizable converter.
#
#  Licensed under the GNU General Public License v3.0 or later (GPL-3.0-or-later).
#  You may use, modify, and distribute this software in accordance with the GPL-3.0 terms.
#
#  This software is distributed WITHOUT ANY WARRANTY; without even the implied
#  warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
#  GPL-3.0 license for full details: https://www.gnu.org/licenses/gpl-3.0.html
# -----------------------------------------------------------------------------

"""
p2v_misc module
"""

import re
import hashlib
import math
import os
from decimal import Decimal


from p2v_signal import p2v_signal #pylint: disable=cyclic-import

def _get_hash(s):
    assert isinstance(s, str), s
    hash_object = hashlib.sha1(s.encode())
    return hash_object.hexdigest()

def _is_legal_name(name):
    if isinstance(name, p2v_signal):
        name = str(name)
    if not isinstance(name, str) or len(name) == 0:
        return False
    if name.startswith("__"):
        return False
    return (name[0].isalpha() or name[0] == "_") and name.replace("_", "").isalnum()

def _fix_legal_name(name):
    assert isinstance(name, str), name
    fixed = ""
    for c in name:
        if not c.isalnum():
            fixed += "_"
        else:
            fixed += c
    return fixed

def _get_names(s):
    names = []
    clean = ""
    s = re.sub("'[a-z]", "", s)
    for c in s:
        if c.isalnum() or c == "_" or c == ".":
            clean += c
        else:
            clean += " "
    for name in clean.split():
        if f"${name}" in s: # sv tasks
            return _get_names(s.replace(f"${name}", ""))
        if _is_legal_name(name):
            names.append(name)
    return names

def _declare_bits(bits, start=0): # pylint: disable=redefined-outer-name
    bus = isinstance(bits, list)
    if bus:
        bits = bits[0]
    if isinstance(bits, str):
        if start == 0:
            return f"[{bits}-1:0]"
        return f"[{bits}+{start}-1:{start}]"
    if bits == 1 and not bus:
        return ""
    return f"[{start+bits-1}:{start}]"

def _declare(name, bits, start=0): # pylint: disable=redefined-outer-name)
    assert isinstance(bits, int), type(bits)
    return  p2v_signal(None, name + _declare_bits([bits], start=start), bits=0)

def _get_paren_depth(line, open_char="(", close_char=")"):
    depth = 0
    for c in line:
        depth = depth + (c == open_char) - (c == close_char)
    return depth

def _is_quote_closed(line, q='"'):
    closed = True
    for c in line:
        if c == q:
            closed = not closed
    return closed

def _is_paren_balanced(line, open_char="(", close_char=")"):
    return _get_paren_depth(line, open_char=open_char, close_char=close_char) == 0

def _is_in_paren(line, open_char="(", close_char=")"):
    if len(line) < 4:
        return False
    line = line.strip()
    if line[0] == open_char and line[-1] == close_char and _is_paren_balanced(line, open_char=open_char, close_char=close_char):
        if line[1] == open_char and line[-2] == close_char:
            return _is_in_paren(line[1:-1], open_char=open_char, close_char=close_char)
        return True
    return False

def _get_bit_range(wire):
    if "[" not in wire:
        return None, None
    assert _is_paren_balanced(wire, open_char="[", close_char="]"), wire
    paren = wire.split("]")[0].split("[")[-1].replace(" ", "")
    if ":" in paren:
        subs = paren.split(":")
        assert len(subs) == 2, f"weird bit range in {wire}"
        msb = int(subs[0])
        lsb = int(subs[1])
    else:
        msb = lsb = int(paren)
    return msb, lsb

def _is_int(n):
    if isinstance(n, int):
        return True
    if isinstance(n, str):
        return n.isdigit()
    if isinstance(n, float):
        return int(n) == n
    return False

def _to_int(n, allow=False):
    if _is_int(n):
        return int(n)
    if allow:
        return n
    raise RuntimeError(f"cannot convert {n} to int")

def _path_to_dict(path, value=None, sep="__"):
    d = {}
    keys = path.split(sep)
    current = d
    for key in keys[:-1]:
        if _is_int(key):
            key = int(key)
        current = current.setdefault(key, {})
    last_key = keys[-1]
    if _is_int(last_key):
        last_key = int(last_key)
    current[last_key] = value
    return d

def _merge_dict(a, b):
    for k, v in b.items():
        if k in a and isinstance(a[k], dict) and isinstance(v, dict):
            _merge_dict(a[k], v)
        else:
            a[k] = v
    return a

def _get_base_str(base):
    if base == 16:
        return "x"
    if base == 2:
        return "b"
    raise RuntimeError(f"unknown base {base} for decimal conversion")

def _base(base, n, bits=None, add_sep=4, prefix=None): # pylint: disable=redefined-outer-name
    assert prefix is None or len(prefix) > 0, f"illegal base prefix {prefix}"
    base_s = _get_base_str(base)
    n = _to_int(n)

    if bits is None:
        assert n >= 0, "negative hex representation must specify number of bits"
        n_bits = 128
    else:
        _check_bits(n, bits)
        n_bits = bits

    s = f"{n & ((1 << n_bits) - 1):0{int((n_bits + log2(base) - 1) / log2(base))}{base_s}}"
    nibbles = (n_bits // log2(base)) + ((n_bits % log2(base)) > 0)
    assert len(s) <= nibbles, f"{n} cannot be represented in {n_bits} bits (base {base})"
    s = (nibbles - len(s)) * "0" + s
    if add_sep > 0:
        s =  s[::-1] # reverse
        new_s = ""
        for i, c in enumerate(s):
            if (i % add_sep) == 0 and i > 0:
                new_s += "_"
            new_s += c
        s =  new_s[::-1] # reverse
    if prefix is None:
        if bits is None:
            while s.startswith("0") or s.startswith("_"):
                if s == "0":
                    break
                s = s.replace("0", "", 1)
                s = s.replace("_", "", 1)
    else:
        s = prefix + s
        if "'" in prefix and bits is not None and not s.startswith(f"{n_bits}'"):
            s = str(n_bits) + s
        else:
            while s.startswith(f"{prefix}0") or s.startswith(f"{prefix}_"):
                if s == f"{prefix}0":
                    break
                s = s.replace(f"{prefix}0", prefix)
                s = s.replace(f"{prefix}_", prefix)
    return s

def _type2str(n):
    if n is None:
        n = type(n)
    if isinstance(n, list):
        l = []
        for s in n:
            l.append(_type2str(s))
        return str(l)
    assert isinstance(n, type), type(n)
    return "'" + str(n).split("'")[1] + "'"

def _make_name_legal(name):
    legal_name = ""
    for char in name:
        if not char.isalnum():
            if len(legal_name) > 0 and legal_name[-1] != "_":
                legal_name += "_"
        else:
            legal_name += char
    return legal_name

def _read_file(filename):
    with open(filename, "r", encoding="utf-8") as file:
        s = file.read()
        file.close()
        return s

def _write_file(filename, s, append=False):
    if append:
        mode = "a"
    else:
        mode = "w"
    with open(filename, mode, encoding="utf-8") as file:
        file.write(s + "\n")
        file.close()

def _compare_files(filename1, filename2):
    with open(filename1, 'r', encoding='utf-8') as f1, open(filename2, 'r', encoding='utf-8') as f2:
        return f1.read() == f2.read()

def _link(src, name):
    if not os.path.exists(name):
        os.symlink(src, name)

def _comment_remover(s):
    # remove all occurrences streamed comments (/*COMMENT */) from string
    s = re.sub(re.compile(r"/\*.*?\*/", re.DOTALL), "", s)
    # remove all occurrence single-line comments (//COMMENT\n ) from string
    s = re.sub(re.compile(r"//.*?\n" ), "\n", s)
    return s

def _remove_spaces(line):
    return line.replace(" ", "").replace("\t", "")

def _remove_extra_paren(line, open_char="(", close_char=")"):
    if _is_in_paren(line, open_char=open_char, close_char=close_char):
        while _is_in_paren(line, open_char=open_char, close_char=close_char): # remove all paren
            line = line[1:-1]
        line = f"{open_char}{line}{close_char}" # put one back
    return line

def _remark_line(line):
    line = re.sub("\n *","\n ", line)
    remark_line = "// " + line.replace("\n", "\n// ")
    remark_line = re.sub(r"// *\n", "//\n", remark_line)
    return re.sub(r"\s+$", "", remark_line)

def _assert_signal(name, var):
    assert isinstance(var, p2v_signal), f"{name} value {var} of type {type(var)} is expected to be of type {p2v_signal}"

def _check_bits(num, _bits):
    if num > 0:
        assert _bits >= log2(num), f"cannot represent the number {num} with {_bits} bits"

def _invert(var, not_op="~"):
    var = str(var)
    if var.startswith(not_op):
        var_not = var.replace(not_op, "", 1)
        if _is_in_paren(var_not):
            return _remove_extra_paren(var_not)
    if not _is_legal_name(var):
        var = f"({var})"
    rtrn = not_op + var
    return p2v_signal(None, str(rtrn), bits=1)

def _add_paren(expr, open_char="(", close_char=")"):
    return _remove_extra_paren(open_char + str(expr) + close_char)

def _verilog_keywords():
    return [
    "always", "and", "assign", "begin", "buf", "bufif0", "bufif1", "case", "casex", "casez",
    "cmos", "deassign", "default", "defparam", "disable", "edge", "else", "end", "endcase",
    "endfunction", "endmodule", "endprimitive", "endspecify", "endtable", "endtask", "event",
    "for", "force", "forever", "fork", "function", "if", "initial", "inout", "input", "join",
    "macromodule", "module", "nand", "negedge", "nmos", "nor", "not", "notif0", "notif1",
    "or", "output", "parameter", "pmos", "posedge", "primitive", "pull0", "pull1", "pulldown",
    "pullup", "rcmos", "reg", "release", "repeat", "rnmos", "rpmos", "rtran", "rtranif0",
    "rtranif1", "scalared", "small", "specify", "specparam", "strong0", "strong1", "supply0",
    "supply1", "table", "task", "time", "tran", "tranif0", "tranif1", "tri", "tri0", "tri1",
    "triand", "trior", "trireg", "vectored", "wait", "wand", "weak0", "weak1", "while", "wire",
    "wor", "xnor", "xor"]

def _systemverilog_keywords():
    return _verilog_keywords() + [
    "accept_on", "alias", "always_comb", "always_ff", "always_latch", "assert", "assume",
    "before", "bind", "bins", "binsof", "bit", "break", "byte", "chandle", "class", "clocking",
    "const", "constraint", "context", "continue", "cover", "covergroup", "coverpoint", "cross",
    "dist", "do", "endclass", "endclocking", "endgroup", "endinterface", "endpackage",
    "endprogram", "endproperty", "endsequence", "enum", "expect", "export", "extends", "extern",
    "final", "first_match", "foreach", "forkjoin", "generate", "genvar", "highz0", "highz1",
    "iff", "ignore_bins", "illegal_bins", "import", "inside", "int", "interface", "intersect",
    "join_any", "join_none", "local", "localparam", "logic", "longint", "matches", "modport",
    "new", "null", "package", "packed", "priority", "program", "property", "protected",
    "pure", "rand", "randc", "randcase", "randsequence", "ref", "return", "sequence", "shortint",
    "shortreal", "solve", "static", "string", "struct", "super", "tagged", "this", "throughout",
    "timeprecision", "timeunit", "type", "typedef", "union", "unique", "var", "virtual", "void",
    "wait_order", "wildcard", "with", "within"]


def ceil(n):
    """
    Round to ceil.

    Args:
        n([int, float]): input value

    Returns:
        int
    """
    assert isinstance(n, (int, float)), n
    return int(math.ceil(n))

def log2(n):
    """
    Log2 of number.

    Args:
        n(int): input value

    Returns:
        int
    """
    assert isinstance(n, (int, str)), n
    if isinstance(n, str):
        return f"$clog2({n})"
    assert n > 0, n
    return ceil(math.log2(n))

def root(n, dim=2):
    """
    Root of number (default is square root).

    Args:
        n(int): input value
        dim(int): root dimension

    Returns:
        Decimal
    """
    return Decimal(n) ** (Decimal(1) / Decimal(dim))

def is_pow2(n):
    """
    Returns True if number is power to 2.

    Args:
        n(int): input value

    Returns:
        bool
    """
    assert isinstance(n, int), n
    return n > 0 and n == (1 << log2(n))

def is_prime(n):
    """
    Returns True if number is prime.

    Args:
        n(int): input value

    Returns:
        bool
    """
    if n < 2:
        return False
    for i in range(2, int(math.isqrt(n)) + 1):
        if n % i == 0:
            return False
    return True

def roundup(num, round_to):
    """
    Round number to the closest dividing number.

    Args:
        num(int): input value
        round_to(int): returned values must divide by this value

    Returns:
        rounded integer
    """
    assert isinstance(num, int), num
    assert isinstance(round_to, int), round_to
    rounded = round_to
    while num > rounded:
        rounded += round_to
    return rounded

def cond(condition, true_var, false_var=""):
    """
    Converts a Python list into Verilog concatenation or join list of signals with operator.

    Args:
        condition(bool): condition
        true_var:  variable for True condition
        false_var: variable for False condition

    Returns:
        Selected input parameter
    """
    if isinstance(true_var, p2v_signal):
        _bits = true_var._bits
    else:
        _bits = 0
    if not isinstance(condition, bool): # verilog condition
        rtrn = f"{condition} ? {true_var} : {false_var}"
        return p2v_signal(None, str(rtrn), bits=_bits)

    if condition:
        return true_var
    return false_var

def concat(vals, sep=None, nl_every=None):
    """
    Converts a Python list into Verilog concatenation or join list of signals with operator.

    Args:
        vals(list): list of signals
        sep([None, str]): if None will perform Verilog concatenation else will perfrom join on sep
        nl_every([None, int]): insert new line every number of items

    Returns:
        Verilog code
    """
    if isinstance(vals, dict):
        vals = list(vals.values())
    assert isinstance(vals, list), f"variable {vals} expected to be of type list"
    assert isinstance(sep, (type(None), str)), sep
    assert isinstance(nl_every, (type(None), int)), nl_every
    assert len(vals) >= 0, vals

    _bits = 0
    new_vals = []
    for n, val in enumerate(vals):
        _assert_signal("concat", val)
        if isinstance(val, p2v_signal):
            _bits += val._bits
        if val is not None:
            val = str(val)
            if nl_every is not None and ((n > 0) and (n%nl_every) == 0):
                val += "\n"
            new_vals.append(val)

    vals = new_vals
    if sep is None:
        if len(set(vals)) == 1: # all items are the same
            if len(vals) == 1:
                rtrn = vals[0]
            else:
                rtrn = "{" + str(len(vals)) + "{" + str(vals[0]) + "}}"
        else:
            rtrn = "{" + ", ".join(vals) + "}"
    else:
        for i, val in enumerate(vals):
            if not val.startswith("(") or not val.endswith(")"):
                if not _is_legal_name(val): # don't add brackets on single variable
                    vals[i] = f"({val})"
        if len(sep) == 1:
            sep = f" {sep} "
        rtrn = sep.join(vals)
    return p2v_signal(None, str(rtrn), bits=_bits)

def pad(left, name, right=0, val=0):
    """
    Verilog padding for lint and for shift left.

    Args:
        left(int): msb padding bits
        name(str): signal name
        right(int): lsb padding bits
        val(int): value for padding

    Returns:
        Verilog code
    """
    assert isinstance(left, int) and left >= 0, f"illegal left padding {left}"
    assert isinstance(right, int) and right >= 0, f"illegal left padding {right}"
    assert isinstance(val, int), f"illegal pad value {val}"
    _assert_signal("pad", name)
    _bits = name._bits + left + right
    vals = []
    if left > 0:
        vals.append(dec(val, left))
    vals.append(name)
    if right > 0:
        vals.append(dec(val, right))
    rtrn = concat(vals)
    return p2v_signal(None, str(rtrn), bits=_bits)

def dec(num, bits=1): # pylint: disable=redefined-outer-name
    """
    Represent integer in Verilog decimal representation.

    Args:
        num(int): input value
        bits(int): number of bits for value

    Returns:
        Verilog code
    """
    assert isinstance(num, int), num
    assert isinstance(bits, int), bits
    _check_bits(num, bits)

    bits = abs(bits)
    if isinstance(num, bool):
        num = int(num)
        bits=1
    if num == -1:
        return "{" + str(bits) + "{1'b1}}"
    if num < 0:
        return bin(num + (1<<bits), bits)
    rtrn = f"{bits}'d{num}"
    return p2v_signal(None, str(rtrn), bits=bits)

def hex(num, bits=None, add_sep=4, prefix="'h"): # pylint: disable=redefined-builtin,redefined-outer-name
    """
    Represent integer in Verilog hexademical representation.

    Args:
        num(int): input value
        bits([None, int]): number of bits for value
        add_sep(int): add underscore every few characters for easier reading of large numbers
        prefix([None, str]): hexadecimal annotation

    Returns:
        Verilog code
    """
    assert isinstance(num, int), f"hex() expects integer value but got {type(num)}"
    assert isinstance(bits, (type(None), int)), bits
    assert isinstance(add_sep, int) and add_sep >= 0, add_sep
    assert isinstance(prefix, (type(None), str)), prefix
    rtrn = _base(16, num, bits, add_sep, prefix)
    if bits is None:
        bits = log2(num)
    return p2v_signal(None, str(rtrn), bits=bits)

def bin(num, bits=None, add_sep=4, prefix="'b"): # pylint: disable=redefined-builtin,redefined-outer-name
    """
    Represent integer in Verilog binary representation.

    Args:
        num(int): input value
        bits([None, int]): number of bits for value
        add_sep(int): add underscore every few characters for easier reading of large numbers
        prefix([None, str]): hexadecimal annotation

    Returns:
        Verilog code
    """
    assert isinstance(num, int), num
    assert isinstance(bits, (type(None), int)), bits
    assert isinstance(add_sep, int) and add_sep >= 0, add_sep
    assert isinstance(prefix, (type(None), str)), prefix
    rtrn = _base(2, num, bits, add_sep, prefix)
    if bits is None:
        bits = log2(num)
    return p2v_signal(None, str(rtrn), bits=bits)

def format_str(s, params=None):
    """
    Create Verilog formated string like: "address = 0x%0h", addr

    Args:
        s(src): string
        params([str, p2v_signal, list]): format parameters

    Returns:
        Verilog code
    """
    if params is None:
        params = []
    assert isinstance(s, str), s
    assert isinstance(params, (p2v_signal, str, list)), params
    full_s = f'"{s}"'
    if isinstance(params, (p2v_signal, str)):
        params = [params]
    for param in params:
        full_s += f", {param}"
    return full_s

### SYSTEM VERILOG ASSERTION FUNCTIONS
def onehot(expression):
    """ SystemVerilog assertion function
        Checks if exactly one bit in expression is high (1). Returns true if it is, false otherwise.
    """
    if isinstance(expression, p2v_signal):
        _bits = expression._bits
    else:
        _bits = 0
    return p2v_signal(None, f"$onehot({expression})", bits=_bits)

def onehot0(expression):
    """ SystemVerilog assertion function
        Checks if at most one bit in expression is high (1), including the case where no bits are high. Returns true if it is, false otherwise.
    """
    if isinstance(expression, p2v_signal):
        _bits = expression._bits
    else:
        _bits = 0
    return p2v_signal(None, f"$onehot0({expression})", bits=_bits)

def isunknown(expression):
    """ SystemVerilog assertion function
        Returns true if any bit in expression is unknown (X or Z). Otherwise, it returns false.
    """
    if isinstance(expression, p2v_signal):
        _bits = expression._bits
    else:
        _bits = 0
    return p2v_signal(None, f"$isunknown({expression})", bits=_bits)

def countones(expression):
    """ SystemVerilog assertion function
        Returns the number of bits in expression that are high (1).
    """
    if isinstance(expression, p2v_signal):
        _bits = expression._bits
    else:
        _bits = 0
    return p2v_signal(None, f"$countones({expression})", bits=_bits)

def countbits(expression, *control_bits):
    """ SystemVerilog assertion function
        Counts the number of bits in expression that match the specified control_bits (e.g., to count 1s, 0s, Xs, or Zs).
    """
    if isinstance(expression, p2v_signal):
        _bits = expression._bits
    else:
        _bits = 0
    return p2v_signal(None, f"$countbits({expression}, {', '.join(control_bits)})", bits=_bits)

def rose(expression):
    """ SystemVerilog assertion function
        Returns true if the least significant bit of the expression changed from 0 to 1 between the previous and current clock cycles. It returns false otherwise.
    """
    if isinstance(expression, p2v_signal):
        _bits = expression._bits
    else:
        _bits = 0
    return p2v_signal(None, f"$rose({expression})", bits=_bits)

def fell(expression):
    """ SystemVerilog assertion function
        Returns true if the least significant bit of the expression changed from 1 to 0 between the previous and current clock cycles.
    """
    if isinstance(expression, p2v_signal):
        _bits = expression._bits
    else:
        _bits = 0
    return p2v_signal(None, f"$fell({expression})", bits=_bits)

def stable(expression):
    """ SystemVerilog assertion function
        Returns true if the value of expression did not change between the previous and current clock cycles. Otherwise, it returns false.
    """
    if isinstance(expression, p2v_signal):
        _bits = expression._bits
    else:
        _bits = 0
    return p2v_signal(None, f"$stable({expression})", bits=_bits)

def past(expression, num_cycles):
    """ SystemVerilog assertion function
        Returns the value of expression from num_cycles ago. If num_cycles is not specified, it defaults to 1.
    """
    if isinstance(expression, p2v_signal):
        _bits = expression._bits
    else:
        _bits = 0
    return p2v_signal(None, f"$past({expression}, {num_cycles})", bits=_bits)
