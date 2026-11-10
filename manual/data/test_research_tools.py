#!/usr/bin/env python3
"""Isolated controls for optional research exports; no network or Lean build."""
import contextlib
import importlib.util
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

MANUAL = Path(__file__).resolve().parents[1]
HISTORY = MANUAL / 'development-history/data'
sys.path[:0] = [str(MANUAL / 'data'), str(HISTORY)]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


index = load('manual_index', MANUAL / 'data/coverage.py')
audit = load('manual_audit', MANUAL / 'data/audit.py')
citations = load('manual_citations', MANUAL / 'data/validate_corpus.py')
collector = load('manual_collector', HISTORY / 'collect_github.py')
history = load('manual_history', HISTORY / 'git_history.py')


class ModelIndexTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='cslib-frontier-index-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'topic.md').write_text('# Topic\n')
        self.map = self.root / 'model-map.md'
        self.header = '# Model map\n\n## Machines\n\n| ID | Model or interface | Family |\n|---|---|---|\n'
        self.row = '| `machine` | [Machine](topic.md#topic) | native |\n'

    def test_only_authored_navigation_fields_are_exported(self):
        self.map.write_text(self.header + self.row)
        self.assertEqual(index.read_index(self.map), [{'id': 'machine', 'name': 'Machine',
                         'family': 'native', 'document': 'topic.md#topic', 'section': 'Machines'}])

    def test_duplicate_id_is_rejected(self):
        self.map.write_text(self.header + self.row + self.row)
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            index.read_index(self.map)

    def test_brackets_inside_a_model_name_are_preserved(self):
        self.map.write_text(self.header + self.row.replace('[Machine]', '[AC0[q] circuits]'))
        self.assertEqual(index.read_index(self.map)[0]['name'], 'AC0[q] circuits')

    def test_missing_target_and_external_target_are_rejected(self):
        for target in ['missing.md', 'https://example.org/topic.md', '../outside.md']:
            with self.subTest(target=target):
                self.map.write_text(self.header + self.row.replace('topic.md#topic', target))
                with self.assertRaisesRegex(ValueError, 'existing manual page'):
                    index.read_index(self.map)

    def test_malformed_row_is_not_silently_omitted(self):
        self.map.write_text(self.header + '| machine | Broken | native |\n')
        with self.assertRaisesRegex(ValueError, 'expected'):
            index.read_index(self.map)

    def test_empty_index_is_rejected(self):
        self.map.write_text(self.header)
        with self.assertRaisesRegex(ValueError, 'No model-map rows'):
            index.read_index(self.map)


class PublicDataTests(unittest.TestCase):
    def test_reconciliation_and_changed_count_controls(self):
        census = {'revision': audit.REVISION, 'library_physical_lines': 7}
        summary = {'revision': audit.REVISION, 'first_parent_commits': 2}
        daily = {'day': {'library_added': 10, 'library_deleted': 3, 'first_parent_commits': 2}}
        self.assertEqual(audit.reconcile(census, summary, daily)['library_physical_lines'], 7)
        for changed, message in [({'library_physical_lines': 8}, 'net library'),
                                 ({'revision': 'another revision'}, 'fixed historical')]:
            with self.subTest(changed=changed), self.assertRaisesRegex(ValueError, message):
                audit.reconcile({**census, **changed}, summary, daily)
        with self.assertRaisesRegex(ValueError, 'Daily commit'):
            audit.reconcile(census, {**summary, 'first_parent_commits': 3}, daily)

    def test_shallow_history_is_rejected_without_fetching(self):
        with tempfile.TemporaryDirectory(prefix='cslib-frontier-history-test-') as temp:
            response = subprocess.CompletedProcess([], 0, stdout='true\n')
            with patch.object(sys, 'argv', ['git_history.py', temp, '--output', temp]), \
                    patch.object(history.subprocess, 'run', return_value=response) as run, \
                    contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                history.main()
            self.assertEqual(run.call_count, 1)
            self.assertEqual(run.call_args.args[0][-2:], ['rev-parse', '--is-shallow-repository'])
            self.assertEqual(run.call_args.kwargs['env']['GIT_NO_LAZY_FETCH'], '1')

    def test_github_pagination_control(self):
        pages = [{'total_count': 2, 'workflow_runs': [{'id': 1}]},
                 {'total_count': 2, 'workflow_runs': [{'id': 2}]}]
        self.assertEqual(collector.combine_pages(pages, 'workflow_runs', 'runs')['total_count'], 2)
        for bad in [pages[:1], [pages[0], pages[0]],
                    [pages[0], {'total_count': 3, 'workflow_runs': [{'id': 2}]}]]:
            with self.subTest(bad=bad), self.assertRaisesRegex(ValueError, 'pagination'):
                collector.combine_pages(bad, 'workflow_runs', 'runs')

    def test_github_request_is_read_only_and_provenance_is_explicit(self):
        response = subprocess.CompletedProcess([], 0, stdout='[{"number": 569}]')
        with patch.object(collector.subprocess, 'run', return_value=response) as run:
            record = collector.collect('issue_569')
        command = run.call_args.args[0]
        self.assertEqual(command[command.index('--method') + 1], 'GET')
        self.assertEqual(command[-1], 'repos/cslib-community/complexitylib/issues/569')
        self.assertEqual(record['number'], 569)
        self.assertIn('not a reconstruction', record['_retrieval']['meaning'])
        self.assertLessEqual(record['_retrieval']['started_at'], record['_retrieval']['completed_at'])

    def test_all_script_help_works_without_optional_packages(self):
        files = [MANUAL / 'data' / (name + '.py') for name in ['census', 'coverage', 'audit', 'validate_corpus']]
        files += [HISTORY / (name + '.py') for name in ['git_history', 'analyze', 'plot_history',
                   'session_census', 'claude_census', 'transcript_excerpts', 'collect_github']]
        for script in files:
            with self.subTest(script=script.name):
                result = subprocess.run([sys.executable, '-B', '-S', str(script), '--help'],
                                        cwd='/tmp', capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('usage:', result.stdout)


class ExtractionTests(unittest.TestCase):
    def run_script(self, script, *arguments):
        result = subprocess.run([sys.executable, '-B', '-S', str(HISTORY / script), *map(str, arguments)],
                                cwd='/tmp', capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result

    def test_analysis_and_plot_read_only_the_selected_input_directories(self):
        with tempfile.TemporaryDirectory(prefix='cslib-frontier-analysis-test-') as temp:
            root = Path(temp)
            data, census, figures = root / 'inputs', root / 'census', root / 'figures'
            data.mkdir()
            census.mkdir()
            start, end = '2026-10-31T00:00:00Z', '2026-10-31T00:00:02Z'
            cohort = 'current_checkout_identity'
            values = {
                'completed_turns': [{'cohort': cohort, 'source_kind': 'cli', 'duration_ms': 1000}],
                'claude_turn_durations': [{'cohort': cohort, 'duration_ms': 2000}],
                'git_daily': {'2026-10-31': {'library_added': 7, 'library_deleted': 0, 'first_parent_commits': 1}},
                'git_summary': {'revision': audit.REVISION, 'first_committer_time': start,
                                'snapshot_committer_time': end, 'first_parent_commits': 1},
                'ci_cohort_2026-10-31': {'runs': [], 'total_count': 0, '_retrieval': {'meaning': 'fixture'}},
                'snapshot_ci_jobs': {'jobs': []},
                'transcript_excerpts': [{'excerpt_id': 'e02', 'record_timestamp': start}],
                'session_summary': {'cohorts': {cohort: {'earliest_start': start, 'latest_observed': end}}},
                'claude_summary': {'cohorts': {cohort: {'earliest_record': start, 'latest_record': end}}},
            }
            values.update({f'pr_{number}': {'created_at': start, 'merged_at': end} for number in [520, 1852, 2228]})
            for name, value in values.items():
                (data / (name + '.json')).write_text(json.dumps(value))
            census_file = census / 'source_census.json'
            census_file.write_text(json.dumps({'revision': audit.REVISION, 'library_physical_lines': 7}))
            self.run_script('analyze.py', '--data-dir', data)
            result = json.loads((data / 'analysis.json').read_text())
            self.assertEqual(result['codex'][cohort]['cli']['sum_seconds'], 1)
            self.assertEqual(result['github_retrieval']['ci_cohort_2026-10-31'], {'meaning': 'fixture'})
            self.run_script('plot_history.py', '--data-dir', data, '--census-dir', census,
                            '--output', figures, '--data-only')
            plotted = json.loads((figures / 'history-data.json').read_text())
            self.assertEqual(plotted['daily'][0]['library_lines'], 7)
            self.assertFalse((figures / 'history.svg').exists())
            census_file.write_text(json.dumps({'revision': audit.REVISION, 'library_physical_lines': 8}))
            failed = subprocess.run([sys.executable, '-B', '-S', str(HISTORY / 'plot_history.py'),
                                     '--data-dir', str(data), '--census-dir', str(census),
                                     '--output', str(figures), '--data-only'], capture_output=True)
            self.assertNotEqual(failed.returncode, 0)

    def test_codex_plain_logs_obey_cutoff_and_omit_private_content(self):
        with tempfile.TemporaryDirectory(prefix='cslib-frontier-session-test-') as temp:
            root = Path(temp)
            logs, out, private = root / 'logs', root / 'public', root / 'private'
            logs.mkdir()
            records = [
                {'type': 'session_meta', 'timestamp': '2026-10-20T00:00:00Z', 'payload': {
                    'id': 'sample', 'timestamp': '2026-10-20T00:00:00Z',
                    'cwd': '/private-person/cslib-community/complexitylib', 'source': 'cli'}},
                {'type': 'event_msg', 'timestamp': '2026-10-20T00:00:01Z', 'payload': {
                    'type': 'user_message', 'message': 'PRIVATE PROMPT TEXT'}},
                {'type': 'event_msg', 'timestamp': '2026-10-20T00:00:02Z', 'payload': {
                    'type': 'task_complete', 'turn_id': 'one', 'duration_ms': 1000}},
                {'type': 'event_msg', 'timestamp': '2026-11-03T00:00:02Z', 'payload': {
                    'type': 'task_complete', 'turn_id': 'later', 'duration_ms': 9999}},
            ]
            (logs / 'sample.jsonl').write_text(''.join(json.dumps(row) + '\n' for row in records))
            self.run_script('session_census.py', logs, '--output', out, '--private-output', private)
            turns = json.loads((out / 'completed_turns.json').read_text())
            self.assertEqual([row['turn_id'] for row in turns], ['one'])
            public = ''.join(path.read_text() for path in out.glob('*.json'))
            self.assertNotIn('PRIVATE PROMPT TEXT', public)
            self.assertNotIn('/private-person/', public)
            self.assertIn('PRIVATE PROMPT TEXT', (private / 'session_provenance.json').read_text())

    def test_claude_plain_logs_deduplicate_and_omit_private_content(self):
        with tempfile.TemporaryDirectory(prefix='cslib-frontier-claude-test-') as temp:
            root = Path(temp)
            logs, out, private = root / 'logs', root / 'public', root / 'private'
            project = logs / '-private-cslib-community-complexitylib'
            project.mkdir(parents=True)
            records = [
                {'type': 'user', 'uuid': 'prompt', 'timestamp': '2026-10-20T00:00:00Z',
                 'cwd': '/private-person/complexitylib', 'message': {'content': 'PRIVATE PROMPT TEXT'}},
                {'type': 'system', 'subtype': 'turn_duration', 'uuid': 'turn',
                 'timestamp': '2026-10-20T00:00:01Z', 'durationMs': 2000},
            ]
            records.append(records[-1])
            (project / 'sample.jsonl').write_text(''.join(json.dumps(row) + '\n' for row in records))
            self.run_script('claude_census.py', logs, '--output', out, '--private-output', private)
            self.assertEqual(len(json.loads((out / 'claude_turn_durations.json').read_text())), 1)
            public = ''.join(path.read_text() for path in out.glob('*.json'))
            self.assertNotIn('PRIVATE PROMPT TEXT', public)
            self.assertNotIn('/private-person/', public)
            self.assertIn('PRIVATE PROMPT TEXT', (private / 'claude_provenance.json').read_text())


class CitationTests(unittest.TestCase):
    def test_canonical_citation_and_missing_key_control(self):
        with tempfile.TemporaryDirectory(prefix='cslib-frontier-citation-test-') as temp:
            root = Path(temp)
            (root / 'sources.md').write_text('<a id="example"></a>\n## example\nAuthored citation.\n')
            (root / 'chapter.md').write_text('[example][example]\n\n[example]: sources.md#example\n')
            self.assertEqual(citations.check_citations(root)['errors'], [])
            (root / 'chapter.md').write_text('[missing][missing]\n\n[missing]: sources.md#missing\n')
            self.assertTrue(any('undefined citation' in error for error in citations.check_citations(root)['errors']))


if __name__ == '__main__':
    unittest.main()
