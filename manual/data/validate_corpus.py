#!/usr/bin/env python3
"""Check maintained manual links, contextual excerpts and canonical citation keys.

Does not require generated exports, fetch external URLs, inspect historical
dependency copies, elaborate Lean or certify semantic correctness.
"""
import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT.parent / 'scripts'))
from check_operator_manual import EXCLUDED, check, prose


def check_citations(root):
    excluded = EXCLUDED | {'_generated'}
    documents = sorted(path for path in root.rglob('*.md')
                       if not excluded.intersection(path.relative_to(root).parts))
    source = root / 'sources.md'
    keys = re.findall(r'<a id="([a-z0-9-]+)"></a>', source.read_text())
    anchors, used, errors = set(keys), set(), []
    if len(keys) != len(anchors):
        errors.append('Duplicate bibliography key in sources.md')
    for path in documents:
        active = prose(path.read_text())
        definitions = dict(re.findall(r'^\[([a-z0-9-]+)\]:\s*(\S+)', active, re.M))
        for display, key in re.findall(r'\[([^\]]+)\]\[([a-z0-9-]+)\]', active):
            used.add(key)
            if display != key:
                errors.append(f'{path.name}: display drift {display}/{key}')
            if key not in anchors or key not in definitions:
                errors.append(f'{path.name}: undefined citation key {key}')
            else:
                target, _, fragment = definitions[key].partition('#')
                if (path.parent / target).resolve() != source.resolve() or fragment != key:
                    errors.append(f'{path.name}: noncanonical citation definition {key}')
    errors.extend('Unused source ' + key for key in sorted(anchors - used))
    return {'canonical_sources': len(anchors), 'errors': errors}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manual', type=Path, default=ROOT)
    args = parser.parse_args()
    manual = args.manual.resolve()
    result = check(manual.parent, manual)
    citations = check_citations(manual)
    result['canonical_sources'] = citations['canonical_sources']
    result['errors'].extend(citations['errors'])
    result['status'] = 'fail' if result['errors'] else 'pass'
    print(json.dumps(result, indent=2))
    return bool(result['errors'])


if __name__ == '__main__':
    raise SystemExit(main())
