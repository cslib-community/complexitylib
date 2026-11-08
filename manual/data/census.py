#!/usr/bin/env python3
"""Validates: the recorded module census describes exactly the pinned Git tree.

Counts are physical source lines and lexical declaration headers, not elaborated
declarations, independent theorems, proof complexity or development effort.
"""
import argparse
import hashlib
import io
import json
import os
import re
import subprocess
import tarfile
from collections import Counter
from pathlib import Path

REVISION = '13e6a31951bf1c89a1a6258c44f9444aecbbefd8'
DEFAULT_OUTPUT = Path(__file__).resolve().parents[1] / '_generated/data'

def owner(path):
    p = path.removeprefix('Complexity/')
    if p.startswith(('Algorithms/', 'DataStructure/', 'Computability/WordRAM/',
                     'Computability/GenericRAM/', 'Computability/RAM/')):
        return 'algorithms-and-memory'
    if p.startswith(('Crypto/', 'Languages/', 'Probability/', 'Computability/Probabilistic/')):
        return 'programs-crypto-and-probability'
    if p.startswith(('Logics/', 'MachineLearning/', 'Computability/Circuit/',
                     'Computability/BranchingProgram/', 'Computability/DecisionTree/',
                     'Computability/QueryComplexity/', 'Computability/Communication/',
                     'Computability/TreeEval/', 'Computability/MCSP/',
                     'Computability/PropertyTesting/', 'Computability/Geometry/')):
        return 'circuits-logic-and-other-models'
    if p.startswith(('Foundations/', 'Tactic/', 'Computability/PolyTime/')) or p == 'Init.lean':
        return 'design-and-assurance'
    return 'machines-and-classes'

def erase_comments(text):
    # Preserve line offsets, including nested Lean comments; strings are blanked too.
    out = []; i = 0; depth = 0; string = False
    while i < len(text):
        c = text[i]; pair = text[i:i+2]
        if depth:
            if pair == '/-': depth += 1; out.extend('  '); i += 2; continue
            if pair == '-/': depth -= 1; out.extend('  '); i += 2; continue
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if string:
            if c == '\\' and i+1 < len(text): out.extend('  '); i += 2; continue
            if c == '"': string = False
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if pair == '/-': depth = 1; out.extend('  '); i += 2; continue
        if pair == '--':
            j = text.find('\n', i)
            if j < 0: j = len(text)
            out.extend(' ' * (j-i)); i = j; continue
        if c == '"': string = True; out.append(' '); i += 1; continue
        out.append(c); i += 1
    return ''.join(out)

def main():
    ap=argparse.ArgumentParser(description=__doc__); ap.add_argument('repository', help='Repository containing the fixed historical revision'); ap.add_argument('--output', type=Path, default=DEFAULT_OUTPUT)
    args=ap.parse_args(); out=Path(args.output); out.mkdir(parents=True,exist_ok=True)
    env={**os.environ, 'GIT_NO_LAZY_FETCH':'1', 'GIT_NO_REPLACE_OBJECTS':'1', 'GIT_OPTIONAL_LOCKS':'0'}
    raw=subprocess.run(['git','-C',args.repository,'archive',REVISION],capture_output=True,check=True,env=env).stdout
    modules=[]; groups=Counter(); all_files=[]; selected={}
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        for m in archive:
            if not m.isfile():continue
            path=m.name; b=archive.extractfile(m).read(); all_files.append(path)
            if path in ['lean-toolchain','lakefile.toml','lake-manifest.json','abstracts/catalogue.json']:
                selected[path]={'sha256':hashlib.sha256(b).hexdigest(),'text':b.decode()}
            if not path.endswith('.lean'):continue
            text=b.decode(); stripped=erase_comments(text); headers=[]
            pattern=r'(?m)^\s*(?:(?:public|private|protected|noncomputable|unsafe|partial)\s+)*(def|abbrev|structure|inductive|class|theorem|lemma)\s+([^\s:(\[{]+)'
            for match in re.finditer(pattern,stripped):
                headers.append({'kind':match.group(1),'name':match.group(2),'line':stripped.count('\n',0,match.start(1))+1})
            upstream=re.search(r'(?m)^-- upstream:\s*(.*)$',text)
            authors=re.search(r'(?m)^Authors:\s*(.*)$',text)
            imports=[{'public':bool(x.group(1)), 'all':bool(x.group(2)), 'module':x.group(3)} for x in re.finditer(r'(?m)^\s*(public\s+)?import\s+(all\s+)?([A-Za-z0-9_.]+)',stripped)]
            group=('library' if path.startswith('Complexity/') else 'tests' if path.startswith('ComplexityTests/') else 'abstracts' if path.startswith('abstracts/') else 'other')
            groups[group]+=1
            modules.append({'path':path,'sha256':hashlib.sha256(b).hexdigest(),'lines':len(text.splitlines()),'group':group,'coverage_owner':owner(path) if group=='library' else None,'upstream':upstream.group(1) if upstream else None,'authors':authors.group(1) if authors else None,'imports':imports,'lexical_declaration_headers':headers})
    modules.sort(key=lambda x:x['path']); library=[m for m in modules if m['group']=='library']
    summary={'revision':REVISION,'tracked_files':len(all_files),'lean_files_by_group':dict(groups),'library_physical_lines':sum(m['lines'] for m in library),'library_lexical_headers':dict(Counter(d['kind'] for m in library for d in m['lexical_declaration_headers'])),'library_coverage_owners':dict(Counter(m['coverage_owner'] for m in library)),'upstream_status_counts':dict(Counter((m['upstream'] or 'MISSING').split(' ')[0] for m in library)),'toolchain':selected['lean-toolchain']['text'].strip(),'dependency_pins':json.loads(selected['lake-manifest.json']['text']),'catalogue':json.loads(selected['abstracts/catalogue.json']['text']),'method':'Exact Git tree; physical lines; lexical declarations; coverage owner is assignment, not semantic audit.'}
    (out/'module_inventory.json').write_text(json.dumps(modules,indent=2)+'\n')
    (out/'source_census.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k not in ('dependency_pins','catalogue')},indent=2))

if __name__=='__main__':main()
