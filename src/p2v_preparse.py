
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
p2v_preparse module. Responsible for preparsing p2v modules. Enables creation of Python variations.
"""

import os
import argparse
import re

import p2v_misc as misc

def _parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('-filenames', default=[], nargs='*', help="p2v flies to parse")
    parser.add_argument("-outdir", type=str, default=None, help="name of output directory")
    parser.add_argument('-defines', default=[], nargs='*', help="defines for pre parsing")
    return parser.parse_args()

def _parse_file(filename, outdir=None, defines=None):
    assert os.path.isfile(filename), f"{filename} does not exist"

    if defines is None:
        defines = []

    s = misc._read_file(filename)

    not_defined = []
    for line in s.split("\n"):
        if line.lstrip().startswith("#_IFDEF ") or line.lstrip().startswith("#_ENDIF "):
            line = line.strip()
            subs = line.split()
            assert len(subs) == 2, f"illegal command: {line}"
            name = subs[1]
            if name not in defines and name not in not_defined:
                not_defined.append(name)

    # keep all defined ifdef blocks
    for name in defines:
        assert misc._is_legal_name(name), f"define {name} does not have a legal name"
        s = re.sub(rf"#_IFDEF *{name}\b.*\n", "", s)
        s = re.sub(rf"#_ENDIF *{name}\b.*\n", "", s)

    # remove all remaining ifdef blocks
    for name in not_defined:
        s = re.sub(rf"#_IFDEF *{name}[\s\S]*?#_ENDIF *{name} *\n", "", s, flags=re.MULTILINE)

    if outdir is None:
        outfile = None
    else:
        outfile = os.path.join(outdir, os.path.basename(filename))
    _write_file(outfile, s)

def _write_file(filename, s):
    if filename is None:
        for line in s.split("\n"):
            print(line)
    else:
        misc._write_file(filename, s)
        path = os.path.abspath(filename).replace(os.getcwd(), "", 1).strip("/")
        print(f"wrote {path}")

def _main():
    args = _parse_args()
    if args.outdir is not None:
        assert os.path.isdir(args.outdir), f"directory {args.outdir} does not exist"

    for filename in args.filenames:
        _parse_file(filename, outdir=args.outdir, defines=args.defines)


if __name__ == '__main__':
    _main()
