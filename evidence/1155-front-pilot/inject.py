#!/usr/bin/env python3
"""Inject the front-end probe into a copy of a Lean file after its import block."""
import re, sys, pathlib
src, dst, probe = sys.argv[1], sys.argv[2], sys.argv[3]
lines = pathlib.Path(src).read_text().splitlines(keepends=True)
probe_text = pathlib.Path(probe).read_text()
src_text = ''.join(lines)
if not re.search(r'(by|^|[;(·>])\s*ppt\b', src_text, re.M):
    a = probe_text.index('-- PPT BEGIN'); b = probe_text.index('-- PPT END')
    probe_text = probe_text[:a] + probe_text[b:]
is_module = any(l.strip() == 'module' or l.startswith('module ') for l in lines[:20])
# find last import line (imports precede everything else after header/module)
last = -1
in_comment = False
for i, l in enumerate(lines):
    s = l.strip()
    if s.startswith('/-') and not s.startswith('/-!'):
        in_comment = '-/' not in s
        continue
    if in_comment:
        if '-/' in s: in_comment = False
        continue
    if re.match(r'^(public\s+)?(meta\s+)?import\s', s) or s.startswith('import all') :
        last = i
    elif s.startswith('/-!') or (s and not s.startswith('--') and s != 'module' and not s.startswith('module') and last >= 0):
        break
out = lines[:last + 1]
if is_module:
    out.append('public import Lean\npublic import Aesop\npublic meta import Lean\npublic meta import Aesop\npublic meta import CslibFrontier.Tactic.PolyTime\n')
    if '-- PPT BEGIN' in probe_text:
        out.append('public meta import CslibFrontier.Tactic.PPT\n')
out.append(probe_text if not is_module else probe_text.replace('section FrontProbe', 'meta section FrontProbe', 1).replace('] def FrontProbe.p', '] public def FrontProbe.p'))
out += lines[last + 1:]
pathlib.Path(dst).write_text(''.join(out))
print('module' if is_module else 'plain')
