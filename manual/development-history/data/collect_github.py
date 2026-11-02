#!/usr/bin/env python3
"""Collect current public GitHub responses for the historical study's selected IDs.

Requires an installed, authenticated gh CLI and makes read-only GET requests.
Responses are observations at collection time: comments, PR state, reruns and CI
retention can change. This cannot recreate the study's original API responses.
No private conversation records are fetched. Outputs are optional and ignored.
"""
import argparse
import datetime as dt
import hashlib
import json
import subprocess
from pathlib import Path

from git_history import REVISION, DEFAULT_OUTPUT

REPOSITORY = 'cslib-community/complexitylib'
PREFIX = 'repos/' + REPOSITORY
ISSUES = [372, 392, 507, 569, 587, 862, 1197, 1764, 2205]
PRS = [520, 1852, 2228]
REQUESTS = {f'issue_{number}': (f'{PREFIX}/issues/{number}', None, None) for number in ISSUES}
REQUESTS.update({f'pr_{number}': (f'{PREFIX}/pulls/{number}', None, None) for number in PRS})
REQUESTS.update({
    'snapshot_ci_runs': (f'{PREFIX}/actions/runs?head_sha={REVISION}&per_page=100', 'workflow_runs', 'runs'),
    'snapshot_ci_jobs': (f'{PREFIX}/actions/runs/41384852164/jobs?filter=all&per_page=100', 'jobs', 'jobs'),
    'ci_cohort_2026-10-31': (f'{PREFIX}/actions/runs?event=merge_group&created=2026-10-31&per_page=100',
                             'workflow_runs', 'runs'),
})


def fetch_pages(endpoint):
    result = subprocess.run(['gh', 'api', '--hostname', 'github.com', '--method', 'GET',
                             '--paginate', '--slurp', endpoint], check=True, capture_output=True, text=True)
    return json.loads(result.stdout)


def combine_pages(pages, source_key, output_key):
    if not isinstance(pages, list) or not pages or not all(isinstance(page, dict) for page in pages):
        raise ValueError('Expected gh --slurp to return a nonempty list of response objects')
    if source_key is None:
        if len(pages) != 1:
            raise ValueError('Unexpected pagination of a single issue or PR')
        return dict(pages[0])
    totals = {page['total_count'] for page in pages}
    rows = [row for page in pages for row in page[source_key]]
    ids = [row['id'] for row in rows]
    if len(totals) != 1 or len(rows) != next(iter(totals)) or len(ids) != len(set(ids)):
        raise ValueError('Incomplete, duplicated or changing GitHub pagination; no complete export produced')
    return {'total_count': len(rows), output_key: rows}


def collect(name, fetch=fetch_pages):
    endpoint, source_key, output_key = REQUESTS[name]
    started = dt.datetime.now(dt.timezone.utc).isoformat()
    pages = fetch(endpoint)
    result = combine_pages(pages, source_key, output_key)
    result['_retrieval'] = {
        'started_at': started, 'completed_at': dt.datetime.now(dt.timezone.utc).isoformat(),
        'method': 'GET', 'url': 'https://api.github.com/' + endpoint, 'page_count': len(pages),
        'meaning': 'Current API response at retrieval time; not a reconstruction of the original historical response.',
    }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument('--select', choices=sorted(REQUESTS), action='append',
                        help='Collect only this record (repeatable); default: all selected records')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    records = {}
    for name in dict.fromkeys(args.select or REQUESTS):
        result = collect(name)
        encoded = (json.dumps(result, indent=2, ensure_ascii=False) + '\n').encode()
        filename = name + '.json'
        (args.output / filename).write_bytes(encoded)
        records[filename] = {'sha256': hashlib.sha256(encoded).hexdigest(), **result['_retrieval']}
    print(json.dumps({'records': records, 'historical_revision': REVISION,
                      'original_responses_reconstructed': False}, indent=2))


if __name__ == '__main__':
    main()
