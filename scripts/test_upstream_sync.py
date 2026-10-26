#!/usr/bin/env python3
"""Regression tests for upstream status reports, without network access."""

from __future__ import annotations

import contextlib
import io
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import upstream_sync  # noqa: E402


class UpstreamSyncTests(unittest.TestCase):
    def setUp(self) -> None:
        temp = tempfile.TemporaryDirectory(prefix="test-upstream-sync-")
        self.addCleanup(temp.cleanup)
        self.repo = Path(temp.name)
        (self.repo / "Complexity").mkdir()
        root = patch.object(upstream_sync, "ROOT", self.repo)
        root.start()
        self.addCleanup(root.stop)

    def report(self, lakefile: str, head: str) -> str:
        (self.repo / "lakefile.toml").write_text(lakefile)
        out = io.StringIO()
        with patch.object(sys, "argv", ["upstream_sync.py"]), \
                patch.object(upstream_sync, "run", return_value=f"{head}\trefs/heads/main\n"), \
                contextlib.redirect_stdout(out):
            upstream_sync.main()
        return out.getvalue()

    def test_only_actual_line_comments_are_markers(self) -> None:
        path = Path("Complexity/Markers.lean")
        (self.repo / path).write_text(
            "module\n/- Example with /- nesting -/:\n-- upstream: submitted #1\n-/\n"
            'def exampleText := r#"\n-- upstream: submitted #2\n"#\n'
            "-- upstream: submitted #3 @abcdef0\n"
            "  -- upstream: vendored owner:feature/branch @1234567\n"
        )
        self.assertEqual(upstream_sync.markers(), [
            (path, "submitted #3 @abcdef0"),
            (path, "vendored owner:feature/branch @1234567"),
        ])

    def test_pin_is_read_from_its_toml_table_regardless_of_key_order(self) -> None:
        head = "b" * 40
        report = self.report(
            '# name = "cslib"\n# rev = "aaaaaaaa"\n'
            "[[require]]\nrev = 'bbbbbbbb'\nname = 'cslib'\n"
            '[[require]]\nname = "other"\nrev = "cccccccc"\n', head)
        self.assertIn("cslib pin bbbbbbbb, upstream main bbbbbbbb: CURRENT", report)

    def test_offline_classifies_the_status_not_its_explanation(self) -> None:
        (self.repo / "Complexity/Markers.lean").write_text(
            "module\n-- upstream: candidate (not submitted #1)\n"
            "-- upstream: candidate (related to vendored owner:feature/branch)\n"
            "-- upstream: submitted #3 @abcdef0\n"
        )
        out = io.StringIO()
        with patch.object(sys, "argv", ["upstream_sync.py", "--offline"]), \
                patch.object(upstream_sync, "run") as run, contextlib.redirect_stdout(out):
            upstream_sync.main()
        run.assert_not_called()
        self.assertEqual(out.getvalue(), "#3: 1 file(s)\n")

    def test_missing_pin_does_not_borrow_another_dependency_revision(self) -> None:
        report = self.report(
            '[[require]]\nname = "cslib"\npath = "../cslib"\n'
            '[[require]]\nname = "other"\nrev = "aaaaaaaa"\n', "a" * 40)
        self.assertIn("cslib pin ?, upstream main aaaaaaaa: UNTRACKED", report)

    def test_different_hash_does_not_imply_ancestry(self) -> None:
        report = self.report('[[require]]\nname = "cslib"\nrev = "aaaaaaaa"\n', "b" * 40)
        self.assertIn("cslib pin aaaaaaaa, upstream main bbbbbbbb: DIFFERS", report)


if __name__ == "__main__":
    unittest.main()
