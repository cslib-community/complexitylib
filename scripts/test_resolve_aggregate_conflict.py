"""Tests for scripts/resolve_aggregate_conflict.py."""

from __future__ import annotations

import io
import os
import pathlib
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import resolve_aggregate_conflict as rac  # noqa: E402

SCRIPT = pathlib.Path(rac.__file__).resolve()
PREAMBLE = "module  -- shake: keep-all --deprecated_module: ignore\n\n"


def aggregate(*names: str, preamble: str = PREAMBLE, keyword: str = "public import") -> str:
    """An aggregate importing `Complexity.<name>` for each name, in the order given."""
    return preamble + "".join(f"{keyword} CslibFrontier.{name}\n" for name in names)


class MergeAggregateTests(unittest.TestCase):
    def test_same_gap_insertions_are_kept_in_order(self) -> None:
        base = aggregate("A", "Z")
        merged = rac.merge_aggregate(base, aggregate("A", "K", "Z"), aggregate("A", "B", "Z"))
        self.assertEqual(merged, aggregate("A", "B", "K", "Z"))

    def test_a_deletion_is_not_resurrected(self) -> None:
        # One side moves `C` to `D`; the other adds `B` next to it, where union would keep `C`.
        base = aggregate("A", "C", "E")
        for ours, theirs in ((aggregate("A", "D", "E"), aggregate("A", "B", "C", "E")),
                             (aggregate("A", "B", "C", "E"), aggregate("A", "D", "E"))):
            with self.subTest(ours=ours):
                self.assertEqual(rac.merge_aggregate(base, ours, theirs),
                                 aggregate("A", "B", "D", "E"))

    def test_shared_changes_agree(self) -> None:
        base = aggregate("A", "C", "E")
        both = aggregate("A", "B", "E")
        self.assertEqual(rac.merge_aggregate(base, both, both), both)

    def test_output_is_sorted_by_module_name(self) -> None:
        base = aggregate("A", "C")
        merged = rac.merge_aggregate(base, aggregate("C", "A", "B"), aggregate("A", "C", "B.X"))
        self.assertEqual(merged, aggregate("A", "B", "B.X", "C"))

    def test_plain_imports(self) -> None:
        plain = {"preamble": "", "keyword": "import"}
        merged = rac.merge_aggregate(aggregate("A", **plain), aggregate("A", "C", **plain),
                                     aggregate("A", "B", **plain))
        self.assertEqual(merged, aggregate("A", "B", "C", **plain))

    def test_different_headers_are_refused(self) -> None:
        base = aggregate("A")
        for ours in (aggregate("A", "B", preamble="module\n\n"),
                     aggregate("A", "B", preamble="", keyword="import")):
            with self.subTest(ours=ours), self.assertRaisesRegex(rac.Refusal, "headers"):
                rac.merge_aggregate(base, ours, aggregate("A", "C"))

    def test_a_line_that_is_not_an_import_is_refused(self) -> None:
        base = aggregate("A")
        for extra in ("set_option linter.style.longLine false\n", "\n", "import A B\n",
                      "public import CslibFrontier.B\r\n", "<<<<<<< ours\n"):
            with self.subTest(extra=extra), self.assertRaisesRegex(rac.Refusal, "not an import"):
                rac.merge_aggregate(base, aggregate("A", "B") + extra, aggregate("A", "C"))

    def test_a_missing_final_newline_is_refused(self) -> None:
        with self.assertRaisesRegex(rac.Refusal, "newline"):
            rac.merge_aggregate(aggregate("A"), aggregate("A", "B")[:-1], aggregate("A", "C"))


@unittest.skipUnless(shutil.which("git"), "git is required")
class DriverTests(unittest.TestCase):
    """The driver under `git merge`, in a scratch repository."""

    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        env = {"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
               "GIT_AUTHOR_NAME": "Fixture", "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
               "GIT_COMMITTER_NAME": "Fixture", "GIT_COMMITTER_EMAIL": "fixture@example.invalid"}
        patcher = patch.dict(os.environ, env)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.git("init", "-q", "-b", "main")
        self.write(".gitattributes", "CslibFrontier.lean merge=leanagg\n")
        self.write("CslibFrontier.lean", aggregate("A", "C", "E"))
        self.git("add", ".")
        self.git("commit", "-qm", "base")

    def git(self, *args: str, check: bool = True) -> subprocess.CompletedProcess:
        return subprocess.run(["git", *args], cwd=self.root, capture_output=True, text=True,
                              check=check)

    def write(self, name: str, text: str) -> None:
        (self.root / name).write_text(text, encoding="utf-8")

    def configure(self) -> None:
        command = f"{shlex.quote(sys.executable)} {shlex.quote(str(SCRIPT))} %O %A %B"
        self.git("config", "merge.leanagg.driver", command)

    def merge(self, ours: str, theirs: str) -> subprocess.CompletedProcess:
        """Merge a branch writing `theirs` into one writing `ours`, both from `main`."""
        for branch, text in (("theirs", theirs), ("ours", ours)):
            self.git("checkout", "-q", "-b", branch, "main")
            self.write("CslibFrontier.lean", text)
            self.git("commit", "-qam", branch)
        return self.git("merge", "--no-edit", "theirs", check=False)

    def result(self) -> str:
        return (self.root / "CslibFrontier.lean").read_text(encoding="utf-8")

    def test_driver_merges_import_sets(self) -> None:
        self.configure()
        merged = self.merge(aggregate("A", "D", "E"), aggregate("A", "B", "C", "E"))
        self.assertEqual(merged.returncode, 0, merged.stderr)
        self.assertEqual(self.result(), aggregate("A", "B", "D", "E"))

    def test_driver_refusal_leaves_a_conflict(self) -> None:
        self.configure()
        merged = self.merge(aggregate("A", "B", "C", "E", preamble=""), aggregate("A", "Bb", "C", "E"))
        self.assertNotEqual(merged.returncode, 0)
        self.assertIn("headers before the imports differ", merged.stderr)
        self.assertIn("<<<<<<< ours", self.result())
        unmerged = self.git("diff", "--name-only", "--diff-filter=U").stdout.split()
        self.assertEqual(unmerged, ["CslibFrontier.lean"])

    def test_driver_failure_leaves_a_conflict(self) -> None:
        paths = [self.root / name for name in ("base", "ours", "theirs")]
        texts = (aggregate("A", "Z"), aggregate("A", "K", "Z"), aggregate("A", "B", "Z"))
        for path, text in zip(paths, texts):
            path.write_text(text, encoding="utf-8")
        with patch.object(rac, "merge_aggregate", side_effect=RuntimeError("unexpected")), \
                patch("sys.stderr", new_callable=io.StringIO) as stderr:
            status = rac.main(list(map(str, paths)))
        self.assertEqual(status, 1)
        self.assertIn("unexpected; leaving a text merge as a conflict", stderr.getvalue())
        self.assertIn("<<<<<<< ours", paths[1].read_text(encoding="utf-8"))

    def test_unconfigured_git_uses_a_text_merge(self) -> None:
        merged = self.merge(aggregate("A", "B", "C", "E"), aggregate("A", "Bb", "C", "E"))
        self.assertNotEqual(merged.returncode, 0)
        self.assertIn("<<<<<<< HEAD", self.result())


if __name__ == "__main__":
    unittest.main()
