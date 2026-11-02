#!/usr/bin/env python3
"""Export a small navigation index from the maintained model-map.md tables.

Rows contain only the ID, display name, family, document link and section. They
do not reconstruct the retired semantic ledgers or establish model completeness,
source identity, proof correctness or mathematical independence.
"""
import argparse
import collections
import hashlib
import json
import re
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
ROW = re.compile(r'^\|\s*`([^`]+)`\s*\|\s*\[(.+)\]\(([^)]+)\)\s*\|\s*([^|]+)\s*\|$')


def read_index(path):
    rows, ids, section = [], set(), None
    for number, line in enumerate(path.read_text().splitlines(), 1):
        if line.startswith('## '):
            section = line[3:].strip()
        if not line.startswith('|') or line.startswith('| ID |') or re.fullmatch(r'\|[\s|:-]+', line):
            continue
        match = ROW.fullmatch(line)
        if not match or not section:
            raise ValueError(f'{path.name}:{number}: expected an ID/name-link/family row under a section')
        key, name, document, family = (value.strip() for value in match.groups())
        if key in ids:
            raise ValueError(f'{path.name}:{number}: duplicate model-map ID {key}')
        target = urlsplit(document)
        resolved = (path.parent / unquote(target.path)).resolve()
        if (target.scheme or target.netloc or target.query or not target.path.endswith('.md')
                or not resolved.is_relative_to(path.parent.resolve()) or not resolved.is_file()):
            raise ValueError(f'{path.name}:{number}: document must name an existing manual page: {document}')
        ids.add(key)
        rows.append({'id': key, 'name': name, 'family': family, 'document': document, 'section': section})
    if not rows:
        raise ValueError('No model-map rows found')
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--model-map', type=Path, default=ROOT / 'model-map.md')
    parser.add_argument('--output-dir', type=Path, default=ROOT / '_generated/data')
    args = parser.parse_args()
    rows = read_index(args.model_map)
    summary = {'entries': len(rows), 'by_section': dict(collections.Counter(row['section'] for row in rows)),
               'meaning': 'Navigation rows in the maintained model map; not a semantic coverage or source audit.'}
    output = {'source': args.model_map.name, 'source_sha256': hashlib.sha256(args.model_map.read_bytes()).hexdigest(),
              'summary': summary, 'models': rows}
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / 'model_index.json').write_text(json.dumps(output, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
