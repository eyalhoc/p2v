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

import tempfile
import os
import json

from p2v_signal import p2v_signal


def get_ast(filename, modname, params={}, cleanup=True):
    _, path = tempfile.mkstemp()
    logfile = f"{path}.log"
    slang_flags = f"--top {modname} --ast-json {path} -Wno-empty-body -q"
    slang_cmd = f"slang {filename} {slang_flags}"
    for name in params:
        slang_cmd += f" -G {name}={params[name]}"
    os.system(f"{slang_cmd} 2> {logfile}")
    with open(path, 'r') as f:
        ast = json.load(f)
    if cleanup:
        os.remove(path)
        os.remove(logfile)

    if ast is not None:
        for member in ast['members']:
            if member['name'] == modname:
                return member['body']
        
    return None

def get_ports(ast):
    signals = {}
    for body_member in ast["members"]:
        name = body_member["name"]
        kind = body_member["kind"].lower()
        if kind == "port":
            bit_range = body_member["type"].split("[")[-1].split("]")[0].strip()
            if ":" in bit_range:
                msb, lsb = bit_range.split(":")
            else:
                msb = lsb = 0
            bits = int(msb) + 1 - int(lsb)
            kind = body_member["direction"].lower()
            if kind in ["in", "out"]:
                kind += "put"
            signals[name] = p2v_signal(kind, name, bits)
        elif kind == "parameter":
            value = body_member["value"]
            try:
                value = int(value)
            except:
                pass
            signals[name] = p2v_signal(kind, name, value)
    return signals
    