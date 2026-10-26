#!/usr/bin/env python3
"""Independent source/static/runtime join. Reads immutable Git objects; never runs Lean."""
import collections
import functools
import hashlib
import json
import pathlib
import statistics
import subprocess

DATA = 'c41194730ceb87aeb52641c7a5f90846a140187d'
STATIC = '5bc08fe7a82eb89dc744d443f190612f5d06e091'
SOURCE = '5bffdf2f248bbbfddea6039ee25a953616dff15b'
ROOT = 'evidence/1155/current-5bff/survey-default/'
INDEX = 'evidence/1155/current-5bffdf/index/'
KINDS = {
    'Cslib.Tactic.PolyTime.tacticPolytime': 'polytime',
    'Mathlib.Meta.FunProp.funPropTacStx': 'fun_prop',
    'Cslib.Tactic.PPT.tacticPpt': 'ppt',
}


@functools.lru_cache(maxsize=None)
def blob(revision, path):
    return subprocess.run(['git', 'show', f'{revision}:{path}'], check=True,
                          capture_output=True).stdout


def read(revision, path):
    return json.loads(blob(revision, path))


def original_offset(offset, insertions):
    shifts = []
    added = 0
    for item in insertions:
        shifts.append((item['original_byte'] + added, item['bytes']))
        added += item['bytes']
    for start, length in reversed(shifts):
        if offset >= start + length:
            offset -= length
        else:
            assert offset <= start, 'Source position inside diagnostic insertion'
    return offset


def main():
    tokens = read(STATIC, INDEX + 'all-target-tokens.json')
    authored = {t['call_id']: t for t in tokens
                if t['classification'] == 'authored_tactic_candidate'}
    plan = read(DATA, ROOT + 'plan.json')
    assert plan['pin'] == SOURCE and plan['static_source'] == STATIC
    files = {f['path']: f for f in plan['files']}
    selected = {h for f in files.values() for h in f['candidate_head_ids']}
    assert selected == set(authored)
    assert set(files) == {t['path'] for t in authored.values()}
    for path, f in files.items():
        raw = blob(SOURCE, path)
        assert raw == blob(DATA, ROOT + 'originals/' + path)
        assert len(raw) == f['bytes']
        assert hashlib.sha256(raw).hexdigest() == f['sha256']
        for head in f['candidate_head_ids']:
            token = authored[head]
            assert token['path'] == path and token['source_sha256'] == f['sha256']
            assert raw[token['byte_start']:token['byte_end']].decode() == token['tactic']

    commands = read(DATA, ROOT + 'commands.json')
    grid = {(c['path'], c['mode']): c for c in commands}
    assert len(grid) == len(commands) == len(files) * 4
    assert set(grid) == {(path, mode) for path in files
                         for mode in ('baseline', 'import-only', 'measured', 'traced')}

    def accepted(path, mode):
        c = grid[path, mode]
        return (c['returncode'] == 0 and c.get('external_warning_acceptance') is True
                and c['context_error'] is None and c['actual_context'] is not None)

    attempts = read(DATA, ROOT + 'attempts.json')
    observed = set()
    measured_mappings = collections.Counter()
    eligible = collections.defaultdict(list)
    mapped = 0
    for attempt in attempts:
        head = attempt['static_head_id']
        if attempt['mode'] == 'measured':
            measured_mappings[attempt['mapping']] += 1
        if head is None:
            continue  # Generated/synthetic/local-source attempts are not authored static joins.
        mapped += 1
        token = authored[head]
        path, mode = attempt['path'], attempt['mode']
        command = grid[path, mode]
        event = attempt['begin']
        assert event['original_source_info'] and event['filemap_equals_input_file']
        assert event['kind'] in KINDS and KINDS[event['kind']] == token['tactic']
        assert token['path'] == path
        assert event['module'] == files[path]['expected_native_module']
        variant = blob(DATA, ROOT + f"variants/{command['file_id']}/{mode}/{path}")
        assert variant[event['start']:event['end']].decode() == event['text']
        start = original_offset(event['start'], command['insertions'])
        end = original_offset(event['end'], command['insertions'])
        assert start == token['byte_start'] and end >= token['byte_end']
        assert blob(SOURCE, path)[start:end].decode() == event['text']
        assert attempt['runtime_full_syntax_id'] == (
            f"{token['source_sha256']}:{path}:{start}-{end}:{token['tactic']}")
        if mode != 'measured':
            continue
        observed.add(head)
        ending = attempt.get('end') or {}
        good_cost = (accepted(path, 'baseline') and accepted(path, 'import-only')
                     and accepted(path, mode) and attempt['status'] == 'returned'
                     and ending.get('goals_after') == 0
                     and attempt['raw_body_thread_heartbeats'] is not None)
        if good_cost:
            eligible[token['tactic']].append((head, attempt['body_user_heartbeat_units']))
    assert observed == set(authored)
    metrics = {}
    for tactic in KINDS.values():
        rows = eligible[tactic]
        costs = [cost for _, cost in rows]
        metrics[tactic] = {
            'returned_closed_goal_attempts': len(rows),
            'distinct_authored_heads': len({head for head, _ in rows}),
            'median_instrumented_body_user_hb': statistics.median(costs),
            'max_instrumented_body_user_hb': max(costs),
        }
    synthesis = read(DATA, ROOT + 'coverage-synthesis.json')
    assert metrics == synthesis['primary_returned_closed_goal_costs']
    assert mapped == read(DATA, ROOT + 'summary.json')['mapped_attempts']
    assert synthesis['static_authored_candidates'] == len(authored)
    assert synthesis['measured_observed_distinct_authored_heads'] == len(observed)
    assert synthesis['measured_mapping_counts'] == dict(measured_mappings)
    report = {
        'data_revision': DATA, 'source_revision': SOURCE, 'static_revision': STATIC,
        'source_files': len(files), 'authored_heads_selected_and_observed': len(observed),
        'explicit_argument_heads_observed': sum(
            authored[h]['source_form'] == 'explicit-arguments' for h in observed),
        'mapped_attempts_both_modes': mapped,
        'measured_mapping_counts': dict(measured_mappings),
        'primary_returned_closed_goal_costs': metrics,
        'scope': ('Static selection, original Git bytes, native-kind/full-span joins and derived '
                  'cost table only. Runtime method/options/provenance acceptance has separate '
                  'independent review. All inventoried authored heads were observed; no claim '
                  'about aliases/generated calls in other files or final proof dependencies. '
                  'Exceptions are attempts, including negative/fallback controls, not a bug rate. '
                  'Inclusive current-thread diagnostic costs are not minima or program runtime.'),
    }
    out = pathlib.Path(__file__).with_name('result.json')
    out.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
