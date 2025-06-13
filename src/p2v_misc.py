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

import re
import hashlib
import math
import os

def _get_hash(s):
    assert type(s) is str, s
    hash_object = hashlib.sha1(s.encode())
    return hash_object.hexdigest()
    
def _is_legal_name(name):
    if type(name) is not str or len(name) == 0:
        return False
    else:
        return (name[0].isalpha() or name[0] == "_") and name.replace("_", "").isalnum()

def _fix_legal_name(name):
    assert type(name) is str, name
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
        elif _is_legal_name(name):
            names.append(name)
    return names

def _get_paren_depth(line, open="(", close=")"):
    depth = 0
    for c in line:
        depth = depth + (c == open) - (c == close)
    return depth

def _is_quote_closed(line, q='"'):
    closed = True
    for c in line:
        if c == q:
            closed = not closed
    return closed

def _is_paren_balanced(line, open="(", close=")"):
    return _get_paren_depth(line, open=open, close=close) == 0

def _get_bit_range(wire):
    if "[" not in wire:
        return None, None
    else:
        assert _is_paren_balanced(wire, open="[", close="]"), wire
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
    try:
        int(n)
        return True
    except:
        return False

def _to_int(n):
    try:
        n_int = int(n)
    except:
        raise Exception(f"unkonw type {type(n)}")
    assert n_int == n, f"cannot be perfomed on non-round float {n}"
    return n_int

def _base(base, n, bits=None, add_sep=4, prefix=None):
    if base == 16:
        base_s = "x"
    elif base == 2:
        base_s = "b"
    else:
        raise Exception(f"unknown base {base} for decimal conversion")

    n = _to_int(n)

    if bits is None:
        assert n >= 0, "negative hex representation must specify number of bits"
        n_bits = 128
    else:
        n_bits = bits

    s = '{:0{}{}}'.format(n & ((1 << n_bits)-1), int((n_bits+log2(base)-1)/log2(base)), base_s)
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
    if prefix is not None:
        s = prefix + s
        if bits is not None and not s.startswith(f"{n_bits}'"):
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
    if type(n) is list:
        l = []
        for s in n:
            l.append(_type2str(s))
        return str(l)
    else:
        assert type(n) is type, type(n)
        return "'" + str(n).split("'")[1] + "'"

def _make_name_legal(name):
    legal_name = ""
    for c in name:
        if not c.isalnum():
            if len(legal_name) > 0 and legal_name[-1] != "_":
                legal_name += "_"
        else:
            legal_name += c
    return legal_name

def _read_file(filename):
    with open(filename, 'r') as file:
        s = file.read()
        file.close()
        return s

def _write_file(filename, s, append=False):
    with open(filename, cond(append, "a", "w")) as file:
        file.write(s + "\n")
        file.close()

def _link(src, name):
    if not os.path.exists(name):
        os.symlink(src, name)

def _comment_remover(string):
    string = re.sub(re.compile("/\*.*?\*/", re.DOTALL), "", string) # remove all occurrences streamed comments (/*COMMENT */) from string
    string = re.sub(re.compile("//.*?\n" ), "\n", string) # remove all occurrence single-line comments (//COMMENT\n ) from string
    return string


def ceil(n):
    """
    Round to ceil.

    Args:
        n([int, float]): input value

    Returns:
        int
    """
    assert type(n) in [int, float], n
    return int(math.ceil(n))

def log2(n):
    """
    Log2 of number.

    Args:
        n(int): input value

    Returns:
        int
    """
    assert type(n) is int and n > 0, n
    return ceil(math.log2(n))

def is_pow2(n):
    """
    Returns True of number is power to 2.

    Args:
        n(int): input value

    Returns:
        bool
    """
    assert type(n) is int, n
    return n > 0 and n == (1 << log2(n))

def roundup(num, round_to):
    """
    Round number to the closest dividing number.

    Args:
        num(int): input value
        round_to(int): returned values must divide by this value

    Returns:
        bool
    """
    assert type(num) is int, num
    assert type(round_to) is int, round_to
    rounded = round_to
    while num > rounded:
        rounded += round_to
    return rounded

def cond(condition, true_var, false_var=None):
    """
    Converts a Python list into Verilog concatenation or join list of signals with operator.

    Args:
        condition(bool): condition
        true_var:  variable for True condition
        false_var: variable for False condition

    Returns:
        Selected input parameter
    """
    assert type(condition) is bool, condition
    
    if condition:
        return true_var
    elif false_var is not None:
        return false_var
    else:
        return ""

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
    assert type(vals) is list, vals
    assert type(sep) in [type(None), str], sep
    assert type(nl_every) in [type(None), int], nl_every
    assert len(vals) >= 0, vals
    new_vals = []
    for n, val in enumerate(vals):
        if val is not None:
            if nl_every is not None and ((n > 0) and (n%nl_every) == 0):
                val += "\n"
            new_vals.append(val)
            
    vals = new_vals
    if sep is None:
        if len(set(vals)) == 1: # all items are the same
            if len(vals) == 1:
                return vals[0]
            else:
                return "{" + str(len(vals)) + "{" + str(vals[0]) + "}}"
        else:
            return "{" + ", ".join(vals) + "}"
    else:
        for i, val in enumerate(vals):
            if not val.startswith("(") or not val.endswith(")"):
                if not _is_legal_name(val): # don't add brackets on single variable
                    vals[i] = f"({val})"
        if len(sep) == 1:
            sep = f" {sep} "
        return sep.join(vals)
        
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
    assert type(name) is str, name
    assert type(left) is int and left >= 0, left
    assert type(right) is int and right >= 0, right
    assert type(val) is int, val
    vals = []
    if left > 0:
        vals.append(dec(val, left))
    vals.append(str(name))
    if right > 0:
        vals.append(dec(val, right))
    return concat(vals)

def dec(n, bits=1):
    """
    Represent integer in Verilog decimal representation.

    Args:
        n(int): input value
        bits(int): number of bits for value

    Returns:
        Verilog code
    """
    assert type(n) is int, n
    assert type(bits) is int, bits
    
    bits = abs(bits)
    if type(n) is bool:
        n = int(n)
        bits=1
    if n == -1:
        return "{" + str(bits) + "{1'b1}}"
    elif n < 0:
        return bin(n + (1<<bits), bits)
    else:
        return f"{bits}'d{n}"

def hex(n, bits=None, add_sep=4, prefix="'h"):
    """
    Represent integer in Verilog hexademical representation.

    Args:
        n(int): input value
        bits([None, int]): number of bits for value
        add_sep(int): add underscore every few characters for easier reading of large numbers
        prefix(str): hexadecimal annotation

    Returns:
        Verilog code
    """
    assert type(n) is int, n
    assert type(bits) in [type(None), int], bits
    assert type(add_sep) is int and add_sep >= 0, add_sep
    assert type(prefix) is str, prefix
    return _base(16, n, bits, add_sep, prefix)

def bin(n, bits=None, add_sep=4, prefix="'b"):
    """
    Represent integer in Verilog binary representation.

    Args:
        n(int): input value
        bits([None, int]): number of bits for value
        add_sep(int): add underscore every few characters for easier reading of large numbers
        prefix(str): binary annotation

    Returns:
        Verilog code
    """
    assert type(n) is int, n
    assert type(bits) in [type(None), int], bits
    assert type(add_sep) is int and add_sep >= 0, add_sep
    assert type(prefix) is str, prefix
    return _base(2, n, bits, add_sep, prefix)

def bits(name, bits, start=0):
    """
    Extract a partial range from a Verilog bus.

    Args:
        name(str): signal name
        bits(int): number of bits to extract
        start(int): lsb

    Returns:
        Verilog code
    """
    assert type(name) is str
    assert type(bits) is int and bits > 0, bits
    assert type(start) is int, start
    end = start + bits - 1
    if start == end:
        return f"{name}[{start}]"
    elif start > end:
        return None
    else:
        return f"{name}[{end}:{start}]"

def bit(name, idx):
    """
    Extract a single bit from a Verilog bus.

    Args:
        name(str): signal name
        idx([int, str]): bit location (can also be a Verilog signal for multi dimention arrays)

    Returns:
        Verilog code
    """
    assert type(name) is str
    assert type(idx) in [int, str]
    return f"{name}[{idx}]"

def is_hotone(var, bits, allow_zero=False):
    """
    Check if a Verilog expression is hot one.

    Args:
        var(str): Verilog expression
        bits(int): number of bits of expression
        allow_zero(bool): allow expression to be zero or hot one

    Returns:
        Verilog code
    """
    assert type(var) is str, var
    assert type(bits) is int and bits > 0, bits
    assert type(allow_zero) is bool, allow_zero
    if bits == 1:
        if allow_zero:
            return "1'b1"
        else:
            return var
    else:
        return f"(~|({var} & ({var} - {dec(1, bits)})))" + cond(allow_zero, f" | (~|{var})")
