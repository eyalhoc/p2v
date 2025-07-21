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

from p2v_signal import p2v_signal #pylint: disable=cyclic-import

def _get_hash(s):
    assert isinstance(s, str), s
    hash_object = hashlib.sha1(s.encode())
    return hash_object.hexdigest()

def _is_legal_name(name):
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

def  _get_base_str(base):
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
    return " // " + line.replace("\n", "\n// ")


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
    assert isinstance(n, int) and n > 0, n
    return ceil(math.log2(n))

def is_pow2(n):
    """
    Returns True of number is power to 2.

    Args:
        n(int): input value

    Returns:
        bool
    """
    assert isinstance(n, int), n
    return n > 0 and n == (1 << log2(n))

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
    if not isinstance(condition, bool): # verilog condition
        rtrn = f"{condition} ? {true_var} : {false_var}"
        return p2v_signal(None, rtrn, bits=1)

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
    assert isinstance(vals, list), f"variable {vals} expected to be of type list"
    assert isinstance(sep, (type(None), str)), sep
    assert isinstance(nl_every, (type(None), int)), nl_every
    assert len(vals) >= 0, vals
    new_vals = []
    for n, val in enumerate(vals):
        if val is not None:
            val = str(val)
            if nl_every is not None and ((n > 0) and (n%nl_every) == 0):
                val += "\n"
            new_vals.append(val)

    vals = new_vals
    if sep is None:
        if len(set(vals)) == 1: # all items are the same
            if len(vals) == 1:
                return vals[0]
            return "{" + str(len(vals)) + "{" + str(vals[0]) + "}}"
        return "{" + ", ".join(vals) + "}"
    for i, val in enumerate(vals):
        if not val.startswith("(") or not val.endswith(")"):
            if not _is_legal_name(val): # don't add brackets on single variable
                vals[i] = f"({val})"
    if len(sep) == 1:
        sep = f" {sep} "
    rtrn = sep.join(vals)
    return p2v_signal(None, rtrn, bits=1)

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
    name = str(name)
    assert isinstance(left, int) and left >= 0, f"illegal left padding {left}"
    assert isinstance(right, int) and right >= 0, f"illegal left padding {right}"
    assert isinstance(val, int), f"illegal pad value {val}"
    vals = []
    if left > 0:
        vals.append(dec(val, left))
    vals.append(str(name))
    if right > 0:
        vals.append(dec(val, right))
    rtrn = concat(vals)
    return p2v_signal(None, rtrn, bits=1)

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

    bits = abs(bits)
    if isinstance(num, bool):
        num = int(num)
        bits=1
    if num == -1:
        return "{" + str(bits) + "{1'b1}}"
    if num < 0:
        return bin(num + (1<<bits), bits)
    rtrn = f"{bits}'d{num}"
    return p2v_signal(None, rtrn, bits=1)

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
    return p2v_signal(None, rtrn, bits=1)

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
    return p2v_signal(None, rtrn, bits=1)

def bits(name, bits, start=0): # pylint: disable=redefined-outer-name
    """
    Extract a partial range from a Verilog bus.

    Args:
        name(str): signal name
        bits(int): number of bits to extract
        start(int): lsb

    Returns:
        Verilog code
    """
    name = str(name)
    assert _is_legal_name(name), f"{name} is not a legal name"
    assert isinstance(bits, int) and bits > 0, f"{name} cannot be of {bits} bits"
    assert isinstance(start, int) and start >= 0, f"{name} bit range cannot start a bit {start}"
    end = start + bits - 1
    if start == end:
        return f"{name}[{start}]"
    if start > end:
        return None
    rtrn = f"{name}[{end}:{start}]"
    return p2v_signal(None, rtrn, bits=1)

def bit(name, idx):
    """
    Extract a single bit from a Verilog bus.

    Args:
        name(str): signal name
        idx([int, str]): bit location (can also be a Verilog signal for multi dimention arrays)

    Returns:
        Verilog code
    """
    name = str(name)
    idx = str(idx)
    assert _is_legal_name(name), f"{name} is not a legal name"
    rtrn = f"{name}[{idx}]"
    return p2v_signal(None, rtrn, bits=1)

def is_hotone(var, bits, allow_zero=False): # pylint: disable=redefined-outer-name
    """
    Check if a Verilog expression is hot one.

    Args:
        var(str): Verilog expression
        bits(int): number of bits of expression
        allow_zero(bool): allow expression to be zero or hot one

    Returns:
        Verilog code
    """
    var = str(var)
    assert isinstance(bits, int) and bits > 0, f"variable {bits} expected to be a non zero positive integer"
    assert isinstance(allow_zero, bool), f"variable {allow_zero} expected to be of type bool"
    if bits == 1:
        if allow_zero:
            return "1'b1"
        return var
    rtrn = f"(({var} & ({var} - {dec(1, bits)})) == {dec(0, bits)})" + cond(allow_zero, f" | ({var} == {dec(0, bits)})")
    return p2v_signal(None, rtrn, bits=1)

def invert(var, not_op="~"):
    """
    Verilog not expression, removed previous not if present.

    Args:
        var(str): Verilog expression
        not_op(str): not operand

    Returns:
        Verilog code
    """
    var = str(var)
    if var.startswith(not_op):
        var_not = var.replace(not_op, "", 1)
        if _is_in_paren(var_not):
            return _remove_extra_paren(var_not)
    rtrn = f"{not_op}({var})"
    return p2v_signal(None, rtrn, bits=1)

def add_paren(expr, open_char="(", close_char=")"):
    """
    Verilog not expression, removed previous not if present.

    Args:
        expr(str): Verilog expression
        open_char(str): open paren
        close_char(str): close paren

    Returns:
        Verilog code
    """
    return _remove_extra_paren(open_char + expr + close_char)
