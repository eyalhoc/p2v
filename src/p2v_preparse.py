
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

import p2v_misc as misc

IFDEF = "#_IFDEF "
IFNDEF = "#_IFNDEF "
ENDIF = "#_ENDIF "

def _parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument('-filenames', default=[], nargs='*', help="p2v flies to parse")
    parser.add_argument('-header', type=str, default=None, help="add header to all files")
    parser.add_argument("-outdir", type=str, default=None, help="name of output directory")
    parser.add_argument('-defines', default=[], nargs='*', help="defines for pre parsing")
    return parser.parse_args()


def _get_name(line):
    line = line.strip()
    subs = line.split()
    assert len(subs) == 2, f"illegal command: {line}"
    name = subs[1]
    return name

def _find_endif(lines, name, start=0):
    for line_num in range(start, len(lines)):
        line = lines[line_num]
        if line.lstrip().startswith(ENDIF):
            endif_name = _get_name(line)
            if name == endif_name:
                return line_num
    raise RuntimeError(f"could not find {ENDIF} for {lines[start]}")

def _parse_file(filename, outdir=None, defines=None, header=None):
    assert os.path.isfile(filename), f"{filename} does not exist"

    if defines is None:
        defines = []

    lines = []
    s = ""
    if header is not None:
        s += misc._read_file(header)
    s += misc._read_file(filename)
    orig_lines = s.split("\n")

    remove_lines = []
    for line_num, line in enumerate(orig_lines):
        if line_num in remove_lines:
            continue
        lstrip_line = line.lstrip()
        is_ifdef = lstrip_line.startswith(IFDEF)
        is_ifndef = lstrip_line.startswith(IFNDEF)
        is_endif = lstrip_line.startswith(ENDIF)
        assert not is_endif, f"unexpected {lstrip_line} in {filename}@{line_num}"
        if is_ifdef or is_ifndef:
            name = _get_name(lstrip_line)
            endif_line_num = _find_endif(orig_lines, name=name, start=line_num)
            keep_block = (is_ifdef and name in defines) or (is_ifndef and name not in defines)
            if keep_block:
                remove_lines.append(endif_line_num)
            else:
                for n in range(line_num, endif_line_num+1):
                    remove_lines.append(n)
        else:
            lines.append(line.rstrip())

    if outdir is None:
        outfile = None
    else:
        outfile = os.path.join(outdir, os.path.basename(filename))
    _write_file(outfile, "\n".join(lines))

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
        _parse_file(filename, outdir=args.outdir, defines=args.defines, header=args.header)


if __name__ == '__main__':
    _main()
