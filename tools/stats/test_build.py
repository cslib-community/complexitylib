# Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Christian Reitwiessner
"""Integration tests use real Git snapshots and the pinned Tokei when available."""
import datetime as dt
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch
import build


class HistoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / 'repo'
        self.repo.mkdir()
        self.git('init', '-q')
        self.git('config', 'user.email', 'test@example.invalid')
        self.git('config', 'user.name', 'Stats Test')

    def git(self, *args, env=None):
        return subprocess.check_output(['git','-C',str(self.repo),*args], env=env).decode().strip()

    def commit(self, date):
        self.git('add', '.')
        env = {**os.environ, 'GIT_AUTHOR_DATE':date, 'GIT_COMMITTER_DATE':date}
        self.git('commit', '-qm', date, env=env)
        return self.git('rev-parse', 'HEAD')

    def test_rename_quiet_days_and_clock_skew(self):
        (self.repo / 'Complexity').mkdir()
        (self.repo / 'Complexity/A.lean').write_text('-- comment\ndef x := 1\n\n')
        first = self.commit('2026-01-01T12:00:00Z')
        self.git('mv','Complexity','CslibFrontier')
        second = self.commit('2026-01-03T12:00:00Z')
        rows = build.daily_snapshots(self.repo,'HEAD',dt.date(2026,1,4))
        self.assertEqual([sha for _,sha in rows], [first,first,second,second])
        (self.repo / 'z.lean').write_text('def z := 2\n')
        third = self.commit('2026-01-02T18:00:00Z')
        # Ancestry order, not sorted commit clocks, determines each day's last ancestor.
        self.assertEqual(build.daily_snapshots(self.repo,'HEAD',dt.date(2026,1,3))[-1][1],third)

    def test_category_rename_and_fallback(self):
        config = json.loads((build.HERE / 'config.json').read_text())['categories']
        for path in ['Complexity/A.lean','CslibFrontier/A.lean','CslibFrontier.lean']:
            self.assertEqual(build.category(path,config),'library')
        self.assertEqual(build.category('guide/Main.lean',config),'other')
        self.assertEqual(build.category('abstracts/Test.lean',config),'results')

    def test_real_counts_cache_and_exports(self):
        tokei = os.environ.get('TOKEI') or shutil.which('tokei')
        if not tokei:
            self.skipTest('Set TOKEI to the pinned Tokei 12.1.2 executable')
        (self.repo / 'Complexity').mkdir()
        (self.repo / 'Complexity/A.lean').write_text('-- comment\ndef x := 1\n\n/- block\n   comment -/\n')
        sha = self.commit('2026-01-01T12:00:00Z')
        # Untracked source and symlinks must never be counted.
        (self.repo / 'untracked.lean').write_text('def ignored := 0\n')
        (self.repo / 'link.lean').symlink_to('Complexity/A.lean')
        sha = self.commit('2026-01-02T12:00:00Z')
        (self.repo / 'untracked2.lean').write_text('def ignored := 0\n')
        config = json.loads((build.HERE / 'config.json').read_text())
        output, cache = self.root / 'site', self.root / 'cache'
        build.build(self.repo,'HEAD',dt.date(2026,1,3),tokei,config,cache,output)
        data = json.loads((output/'data.json').read_text())
        counts = data['snapshots'][0]['categories']['library']
        self.assertEqual(counts,dict(code=1,comments=3,blanks=1,files=1))
        self.assertEqual(data['snapshots'][-1]['categories']['other']['files'],1)
        self.assertEqual(data['head'],sha)
        self.assertIn('date,commit,category,code,comments,blanks,files', (output/'data.csv').read_text())
        with patch.object(build,'count_snapshot',side_effect=AssertionError('Cache missed')):
            build.build(self.repo,'HEAD',dt.date(2026,1,3),tokei,config,cache,output)
        changed = {**config,'extra':'invalidate-cache'}
        with patch.object(build,'count_snapshot',side_effect=RuntimeError('New fingerprint')):
            with self.assertRaisesRegex(RuntimeError,'New fingerprint'):
                build.build(self.repo,'HEAD',dt.date(2026,1,3),tokei,changed,cache,output)


if __name__ == '__main__':
    unittest.main()
