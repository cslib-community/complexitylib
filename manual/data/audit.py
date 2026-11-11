#!/usr/bin/env python3
"""Reconcile the fixed public Git census/history and check the maintained manual.

Reads historical Git objects without fetching or building Lean. Outputs go to
an ignored directory; no tracked export is required or compared. The current
model map is a navigation index, not a reconstruction of retired model ledgers.
Private logs, old API responses and mathematical completeness are not audited.
"""
import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

from census import REVISION

ROOT = Path(__file__).resolve().parents[1]


def reconcile(census, history, daily):
    if census['revision'] != REVISION or history['revision'] != REVISION:
        raise ValueError('Census and history must describe the fixed historical revision')
    net = sum(day['library_added'] - day['library_deleted'] for day in daily.values())
    if net != census['library_physical_lines']:
        raise ValueError('First-parent net library lines do not equal the snapshot census')
    commits = sum(day['first_parent_commits'] for day in daily.values())
    if commits != history['first_parent_commits']:
        raise ValueError('Daily commit count does not equal the first-parent history')
    return {'revision': REVISION, 'library_physical_lines': net, 'first_parent_commits': commits}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', help='Repository containing complete history through the fixed revision')
    parser.add_argument('--output-dir', type=Path, default=ROOT / '_generated')
    args = parser.parse_args()
    repository = str(Path(args.repository).resolve())
    output = args.output_dir.resolve()
    census_dir, history_dir = output / 'data', output / 'history/data'
    env = {**os.environ, 'GIT_NO_LAZY_FETCH': '1', 'GIT_OPTIONAL_LOCKS': '0', 'PYTHONDONTWRITEBYTECODE': '1'}
    checks = []

    def run(script, *arguments):
        result = subprocess.run([sys.executable, '-B', str(ROOT / script), *map(str, arguments)],
                                cwd=ROOT, env=env, text=True, capture_output=True)
        if result.returncode:
            print(result.stdout + result.stderr, file=sys.stderr)
            raise SystemExit(result.returncode)
        checks.append(script)

    run('data/census.py', repository, '--output', census_dir)
    run('history/data/git_history.py', repository, '--output', history_dir)
    read = lambda path: json.loads(path.read_text())
    totals = reconcile(read(census_dir / 'source_census.json'), read(history_dir / 'git_summary.json'),
                       read(history_dir / 'git_daily.json'))
    run('data/coverage.py', '--output-dir', census_dir)
    run('data/validate_corpus.py')
    result = {'status': 'pass', 'checks': checks, 'reconciliation': totals,
              'model_map_entries': read(census_dir / 'model_index.json')['summary']['entries'],
              'private_sources_reextracted': False, 'github_records_refetched': False,
              'historical_model_ledgers_checked': False, 'lean_compilation': False}
    (output / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
