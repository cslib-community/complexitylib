"""Temporary-repository tests for scripts/check_restack.py."""

from __future__ import annotations

import contextlib
import io
import os
import pathlib
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_restack  # noqa: E402

GIT_ENV = {
    **os.environ,
    "GIT_AUTHOR_NAME": "Test",
    "GIT_AUTHOR_EMAIL": "test@example.com",
    "GIT_COMMITTER_NAME": "Test",
    "GIT_COMMITTER_EMAIL": "test@example.com",
    "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_CONFIG_NOSYSTEM": "1",
}

IMPORTS = "import A\nimport C\nimport E\n"


@unittest.skipUnless(shutil.which("git"), "git is required")
class RestackTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.git("init", "-q", "-b", "main")
        self.commit("base", {"All.lean": IMPORTS, "Lib.lean": "def x := 1\ndef y := 2\n"})

    def git(self, *args: str) -> str:
        return subprocess.run(["git", "-C", str(self.root), *args], capture_output=True,
                              text=True, check=True, env=GIT_ENV).stdout.strip()

    def commit(self, message: str, files: dict[str, str | None]) -> str:
        for name, text in files.items():
            path = self.root / name
            if text is None:
                path.unlink()
            else:
                path.write_text(text)
        self.git("add", "-A")
        self.git("commit", "-q", "-m", message)
        return self.git("rev-parse", "HEAD")

    def check(self, approved: str, new: str, *extra: str) -> tuple[int, str]:
        out = io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            code = check_restack.main([approved, new, "--base", "main", "--root", str(self.root),
                                       *extra])
        return code, out.getvalue()

    def branch_with_feature(self) -> str:
        """A PR branch adding `import B` and a new module; returns its approved head."""
        self.git("checkout", "-q", "-b", "feature", "main")
        return self.commit("feature", {"All.lean": "import A\nimport B\nimport C\nimport E\n",
                                       "B.lean": "theorem b : True := trivial\n"})

    def merge_main(self, resolution: dict[str, str] | None = None) -> str:
        """Merge `main` into `feature`, resolving conflicts with `resolution`."""
        self.git("checkout", "-q", "feature")
        result = subprocess.run(["git", "-C", str(self.root), "merge", "-q", "--no-edit", "main"],
                                capture_output=True, text=True, env=GIT_ENV)
        if result.returncode != 0:
            for name, text in (resolution or {}).items():
                (self.root / name).write_text(text)
            self.git("add", "-A")
            self.git("commit", "-q", "--no-edit")
        return self.git("rev-parse", "HEAD")

    def test_merge_with_resolved_neighbouring_import_is_identical(self) -> None:
        approved = self.branch_with_feature()
        self.git("checkout", "-q", "main")
        self.commit("other PR", {"All.lean": "import A\nimport Bb\nimport C\nimport E\n",
                                 "Bb.lean": "def bb := 0\n"})
        new = self.merge_main({"All.lean": "import A\nimport B\nimport Bb\nimport C\nimport E\n"})
        code, out = self.check(approved, new)
        self.assertEqual(code, 0, out)
        self.assertIn("identical", out)
        self.assertIn("2 files, +2 -0 lines", out)

    def test_rebase_onto_newer_main_is_identical(self) -> None:
        approved = self.branch_with_feature()
        self.git("checkout", "-q", "main")
        self.commit("unrelated", {"Lib.lean": "def x := 1\ndef y := 3\n"})
        self.git("checkout", "-q", "-b", "rebased", approved)
        self.git("rebase", "-q", "main")
        code, out = self.check(approved, self.git("rev-parse", "HEAD"))
        self.assertEqual(code, 0, out)

    def test_changed_pr_line_is_reported(self) -> None:
        approved = self.branch_with_feature()
        self.commit("touch-up", {"B.lean": "theorem b : True := by trivial\n"})
        code, out = self.check(approved, self.git("rev-parse", "HEAD"))
        self.assertEqual(code, 1, out)
        self.assertIn("B.lean: the PR's change to this file differs", out)
        self.assertIn("-theorem b : True := trivial", out)
        self.assertIn("+theorem b : True := by trivial", out)
        self.assertNotIn("All.lean", out)

    def test_conflict_resolution_that_drops_mains_line_is_reported(self) -> None:
        approved = self.branch_with_feature()
        self.git("checkout", "-q", "main")
        self.commit("other PR", {"All.lean": "import A\nimport Bb\nimport C\nimport E\n"})
        # Resolving by taking the PR's side removes main's `import Bb`.
        new = self.merge_main({"All.lean": "import A\nimport B\nimport C\nimport E\n"})
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("All.lean: the PR's change to this file differs", out)
        self.assertIn("+import Bb", out)

    def test_pr_removing_a_line_main_changed_is_reported(self) -> None:
        self.git("checkout", "-q", "-b", "feature", "main")
        approved = self.commit("drop y", {"Lib.lean": "def x := 1\n"})
        self.git("checkout", "-q", "main")
        self.commit("change y", {"Lib.lean": "def x := 1\ndef y := 3\n"})
        new = self.merge_main({"Lib.lean": "def x := 1\n"})
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("approved removed lines", out)

    def test_dropped_and_added_files_are_reported(self) -> None:
        approved = self.branch_with_feature()
        self.commit("swap", {"B.lean": None, "D.lean": "def d := 0\n"})
        code, out = self.check(approved, self.git("rev-parse", "HEAD"))
        self.assertEqual(code, 1, out)
        self.assertIn("B.lean: changed only at the approved head", out)
        self.assertIn("D.lean: changed only at the new head", out)

    def test_mode_change_is_reported(self) -> None:
        approved = self.branch_with_feature()
        self.git("update-index", "--chmod=+x", "B.lean")
        self.git("commit", "-q", "-m", "chmod")
        code, out = self.check(approved, self.git("rev-parse", "HEAD"))
        self.assertEqual(code, 1, out)
        self.assertIn("file mode or status", out)

    def test_missing_final_newline_is_reported(self) -> None:
        approved = self.branch_with_feature()
        self.commit("strip newline", {"B.lean": "theorem b : True := trivial"})
        code, out = self.check(approved, self.git("rev-parse", "HEAD"))
        self.assertEqual(code, 1, out)
        self.assertIn("No newline at end of file", out)

    def test_binary_files_compare_by_blob(self) -> None:
        self.git("checkout", "-q", "-b", "feature", "main")
        (self.root / "img.bin").write_bytes(b"\x00\x01\x02")
        self.git("add", "-A")
        self.git("commit", "-q", "-m", "binary")
        approved = self.git("rev-parse", "HEAD")
        self.git("checkout", "-q", "main")
        self.commit("unrelated", {"Lib.lean": "def x := 1\ndef y := 3\n"})
        same = self.merge_main()
        self.assertEqual(self.check(approved, same)[0], 0)
        (self.root / "img.bin").write_bytes(b"\x00\x01\x03")
        self.git("commit", "-qam", "change binary")
        code, out = self.check(approved, self.git("rev-parse", "HEAD"))
        self.assertEqual(code, 1, out)
        self.assertIn("binary blobs", out)

    def test_stacked_pr_after_lower_pr_squash_lands(self) -> None:
        self.git("checkout", "-q", "-b", "lower", "main")
        lower = self.commit("lower", {"Lib.lean": "def x := 1\ndef y := 2\ndef z := 3\n"})
        self.git("checkout", "-q", "-b", "feature", "lower")
        approved = self.commit("upper", {"B.lean": "def b := z\n"})
        # The lower PR lands as a squash commit; the upper PR then merges main.
        self.git("checkout", "-q", "main")
        self.git("merge", "-q", "--squash", "lower")
        self.git("commit", "-q", "-m", "lower (#1)")
        new = self.merge_main()
        code, out = self.check(approved, new, "--approved-base", lower)
        self.assertEqual(code, 0, out)
        # Against `main`, the approved delta still contains the lower PR's change.
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("Lib.lean: changed only at the approved head", out)

    def test_unknown_revision_is_an_error(self) -> None:
        code, out = self.check("0" * 40, "HEAD")
        self.assertEqual(code, 2, out)
        self.assertIn("could not be fetched", out)


if __name__ == "__main__":
    unittest.main()
