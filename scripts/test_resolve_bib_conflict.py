"""Tests for scripts/resolve_bib_conflict.py."""

from __future__ import annotations

import io
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import resolve_bib_conflict as rbc  # noqa: E402

SCRIPT = pathlib.Path(rbc.__file__).resolve()


def entry(key: str, title: str = "T", kind: str = "article") -> str:
    return f"@{kind}{{{key},\n  author = {{A}},\n  title  = {{{title}}}\n}}"


def bib(*entries: str) -> str:
    return "\n\n".join(entries) + "\n"


# Entries of #2940 (congestion games) and #2948 (mechanism design), which conflicted in the
# merge queue on 2026-11-07 because both inserted between `Rompel1990` and `Rubinstein1995`.
ROMPEL = """@inproceedings{Rompel1990,
  author    = {Rompel, John},
  title     = {One-Way Functions are Necessary and Sufficient for Secure Signatures},
  booktitle = {Proceedings of the Twenty-Second Annual ACM Symposium on Theory of Computing},
  series    = {STOC '90},
  pages     = {387--394},
  publisher = {ACM},
  year      = {1990},
  doi       = {10.1145/100216.100269},
  url       = {https://doi.org/10.1145/100216.100269}
}"""
RUBINSTEIN = """@article{Rubinstein1995,
  author    = {Rubinstein, David},
  title     = {Sensitivity vs. Block Sensitivity of {Boolean} Functions},
  journal   = {Combinatorica},
  volume    = {15},
  number    = {2},
  pages     = {297--299},
  year      = {1995},
  doi       = {10.1007/BF01200762}
}"""
ROSENTHAL = """@article{Rosenthal1973,
  author    = {Rosenthal, Robert W.},
  title     = {A Class of Games Possessing Pure-Strategy {Nash} Equilibria},
  journal   = {International Journal of Game Theory},
  volume    = {2},
  number    = {1},
  pages     = {65--67},
  year      = {1973},
  doi       = {10.1007/BF01737559}
}"""
ROUGHGARDEN2015 = """@article{Roughgarden2015,
  author    = {Roughgarden, Tim},
  title     = {Intrinsic Robustness of the Price of Anarchy},
  journal   = {Journal of the ACM},
  volume    = {62},
  number    = {5},
  pages     = {32:1--32:42},
  year      = {2015},
  doi       = {10.1145/2806883}
}"""
ROUGHGARDEN_TARDOS = """@article{RoughgardenTardos2002,
  author    = {Roughgarden, Tim and Tardos, {\\'E}va},
  title     = {How Bad Is Selfish Routing?},
  journal   = {Journal of the ACM},
  volume    = {49},
  number    = {2},
  pages     = {236--259},
  year      = {2002},
  doi       = {10.1145/506147.506153}
}"""
ROUGHGARDEN_CS364A = """@misc{Roughgarden2013CS364A,
  author       = {Roughgarden, Tim},
  title        = {{CS364A}: Algorithmic Game Theory, Lecture Notes},
  howpublished = {Stanford University, Fall 2013},
  year         = {2013},
  url          = {https://theory.stanford.edu/~tim/f13/f13.html}
}"""
ROUGHGARDEN2016 = """@book{Roughgarden2016,
  author    = {Roughgarden, Tim},
  title     = {Twenty Lectures on Algorithmic Game Theory},
  publisher = {Cambridge University Press},
  year      = {2016},
  doi       = {10.1017/CBO9781316779309}
}"""


class MergeBibTests(unittest.TestCase):
    def test_same_gap_insertions_are_kept_in_key_order(self) -> None:
        base = bib(entry("Alpha2000"), entry("Zeta2000"))
        ours = bib(entry("Alpha2000"), entry("Kappa2001"), entry("Zeta2000"))
        theirs = bib(entry("Alpha2000"), entry("Beta2001"), entry("Mu2001"), entry("Zeta2000"))
        self.assertEqual(rbc.merge_bib(base, ours, theirs), bib(
            entry("Alpha2000"), entry("Beta2001"), entry("Kappa2001"), entry("Mu2001"),
            entry("Zeta2000")))

    def test_replay_of_the_2940_and_2948_queue_conflict(self) -> None:
        base = bib(ROMPEL, RUBINSTEIN)
        ours = bib(ROMPEL, ROSENTHAL, ROUGHGARDEN2015, ROUGHGARDEN_TARDOS, RUBINSTEIN)
        theirs = bib(ROMPEL, ROUGHGARDEN_CS364A, ROUGHGARDEN2016, RUBINSTEIN)
        with tempfile.TemporaryDirectory() as tmp:
            paths = [pathlib.Path(tmp, name) for name in ("base", "ours", "theirs")]
            for path, text in zip(paths, (base, ours, theirs)):
                path.write_text(text, encoding="utf-8")
            base_path, ours_path, theirs_path = map(str, paths)
            text_merge = subprocess.run(["git", "merge-file", "-p", ours_path, base_path,
                                         theirs_path], capture_output=True)
        self.assertEqual(text_merge.returncode, 1, "git's text merge conflicts here")
        # The two sides interleave in key order, which no concatenation of the sides gives.
        self.assertEqual(rbc.merge_bib(base, ours, theirs), bib(
            ROMPEL, ROSENTHAL, ROUGHGARDEN_CS364A, ROUGHGARDEN2015, ROUGHGARDEN2016,
            ROUGHGARDEN_TARDOS, RUBINSTEIN))

    def test_one_sided_edit_and_removal_are_taken(self) -> None:
        base = bib(entry("Alpha2000"), entry("Beta2000"), entry("Zeta2000"))
        ours = bib(entry("Alpha2000", "Corrected"), entry("Beta2000"), entry("Zeta2000"))
        theirs = bib(entry("Alpha2000"), entry("Gamma2001"), entry("Zeta2000"))
        self.assertEqual(rbc.merge_bib(base, ours, theirs), bib(
            entry("Alpha2000", "Corrected"), entry("Gamma2001"), entry("Zeta2000")))

    def test_identical_additions_agree(self) -> None:
        base = bib(entry("Alpha2000"))
        both = bib(entry("Alpha2000"), entry("Beta2001"))
        self.assertEqual(rbc.merge_bib(base, both, both), both)

    def test_conflicting_changes_are_refused(self) -> None:
        base = bib(entry("Alpha2000"))
        cases = {
            "different additions of one key": (bib(entry("Alpha2000"), entry("Beta2001", "X")),
                                               bib(entry("Alpha2000"), entry("Beta2001", "Y"))),
            "different edits": (bib(entry("Alpha2000", "X")), bib(entry("Alpha2000", "Y"))),
            "edit against removal": (bib(entry("Alpha2000", "X")), ""),
            "case-variant additions": (bib(entry("Alpha2000"), entry("Beta2001")),
                                       bib(entry("Alpha2000"), entry("BETA2001"))),
        }
        for name, (ours, theirs) in cases.items():
            with self.subTest(name):
                with self.assertRaisesRegex(rbc.Refusal, "both sides changed"):
                    rbc.merge_bib(base, ours, theirs)

    def test_unsorted_or_duplicate_input_is_refused(self) -> None:
        base = bib(entry("Alpha2000"), entry("Zeta2000"))
        for bad in (bib(entry("Zeta2000"), entry("Alpha2000")),
                    bib(entry("Alpha2000"), entry("alpha2000"), entry("Zeta2000"))):
            with self.subTest(bad=bad[:40]):
                with self.assertRaisesRegex(rbc.Refusal, r"references\.bib \(ours\)"):
                    rbc.merge_bib(base, bad, base)

    def test_repository_bibliography_round_trips(self) -> None:
        text = (rbc.ROOT / "references.bib").read_text(encoding="utf-8")
        self.assertEqual(rbc.merge_bib(text, text, text), text)


class MergeReportTests(unittest.TestCase):
    STAGES = b"".join(b"100644 %s %d\treferences.bib\0" % (b"0" * 40, s) for s in (1, 2, 3))
    MESSAGES = (b"1\0references.bib\0Auto-merging\0Auto-merging references.bib\n\0"
                b"1\0references.bib\0CONFLICT (contents)\0CONFLICT (content): Merge conflict in "
                b"references.bib\n\0")

    def test_parses_stages_and_messages(self) -> None:
        tree, stages, messages = rbc.merge_report(b"t" * 40 + b"\0" + self.STAGES + b"\0"
                                                  + self.MESSAGES)
        self.assertEqual(tree, "t" * 40)
        self.assertEqual([stage for _, _, stage, _ in stages], ["1", "2", "3"])
        self.assertEqual(messages, [([b"references.bib"], "Auto-merging"),
                                    ([b"references.bib"], "CONFLICT (contents)")])

    def test_malformed_output_is_refused(self) -> None:
        good = b"t" * 40 + b"\0" + self.STAGES + b"\0" + self.MESSAGES
        for bad in (good[:-1], good + b"x\0", good.replace(b"\t", b" ", 1),
                    good.replace(b"\x001\0references.bib", b"\0x\0references.bib", 1),
                    good.replace(b"\x001\0references.bib", b"\x000\0references.bib", 1),
                    b"t" * 40 + b"\0" + self.STAGES):
            with self.subTest(bad=bad[-40:]):
                with self.assertRaisesRegex(rbc.Refusal, "unexpected `git merge-tree` output"):
                    rbc.merge_report(bad)


class GitTests(unittest.TestCase):
    """Commit and driver modes in a scratch repository."""

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
        self.write(".gitattributes", "references.bib merge=bibkeys\n")
        self.write("references.bib", bib(entry("Alpha2000"), entry("Zeta2000")))
        self.write("notes.md", "one\n\ntwo\n\nthree\n")
        self.commit("base")
        self.base = self.git("rev-parse", "HEAD")

    def git(self, *args: str, check: bool = True) -> str:
        return subprocess.run(["git", *args], cwd=self.root, capture_output=True, text=True,
                              check=check).stdout.strip()

    def write(self, name: str, text: str) -> None:
        (self.root / name).write_text(text, encoding="utf-8")

    def commit(self, message: str) -> None:
        self.git("add", ".")
        self.git("commit", "-qm", message)

    def branch(self, name: str, files: dict[str, str], start: str | None = None) -> str:
        self.git("checkout", "-q", "-b", name, start or self.base)
        for path, text in files.items():
            (self.root / path).parent.mkdir(parents=True, exist_ok=True)
            self.write(path, text)
        self.commit(name)
        return self.git("rev-parse", "HEAD")

    def bib_branches(self, start: str | None = None, ours: dict[str, str] | None = None,
                     theirs: dict[str, str] | None = None) -> None:
        """`feature` and `upstream` add different entries between the same neighbours."""
        self.branch("feature", {
            "references.bib": bib(entry("Alpha2000"), entry("Kappa2001"), entry("Zeta2000")),
            **(ours or {})}, start)
        self.branch("upstream", {
            "references.bib": bib(entry("Alpha2000"), entry("Beta2001"), entry("Zeta2000")),
            **(theirs or {})}, start)

    def refs(self) -> str:
        return self.git("for-each-ref")

    def commits(self) -> set[str]:
        objects = self.git("cat-file", "--batch-all-objects", "--batch-check").splitlines()
        return {line.split()[0] for line in objects if line.split()[1] == "commit"}

    def assert_refused(self, pattern: str) -> None:
        """`resolve` refuses with `pattern` and writes no commit and no ref."""
        commits, refs = self.commits(), self.refs()
        with self.assertRaisesRegex(rbc.Refusal, pattern):
            rbc.resolve("feature", "upstream", cwd=self.root)
        self.assertEqual((self.commits(), self.refs()), (commits, refs))

    def test_bib_only_conflict_writes_a_merge_commit(self) -> None:
        head = self.branch("feature", {
            "references.bib": bib(entry("Alpha2000"), entry("Kappa2001"), entry("Zeta2000")),
            "notes.md": "one\n\ntwo\n\nthree\n\nfeature\n"})
        main = self.branch("upstream", {
            "references.bib": bib(entry("Alpha2000"), entry("Beta2001"), entry("Zeta2000")),
            "notes.md": "upstream\n\none\n\ntwo\n\nthree\n"})
        refs = self.refs()
        sha = rbc.resolve("feature", "upstream", cwd=self.root)
        self.assertIsNotNone(sha)
        self.assertEqual(self.refs(), refs, "no ref is updated")
        self.assertEqual(self.git("rev-list", "--parents", "-n1", sha).split()[1:], [head, main])
        self.assertEqual(self.git("show", f"{sha}:references.bib") + "\n", bib(
            entry("Alpha2000"), entry("Beta2001"), entry("Kappa2001"), entry("Zeta2000")))
        self.assertEqual(self.git("show", f"{sha}:notes.md"),
                         "upstream\n\none\n\ntwo\n\nthree\n\nfeature")

    def test_other_conflicts_are_refused_without_a_commit(self) -> None:
        self.bib_branches(ours={"notes.md": "one\n\nfeature\n\nthree\n"},
                          theirs={"notes.md": "one\n\nupstream\n\nthree\n"})
        self.assert_refused(r"CONFLICT \(contents\): notes\.md; CONFLICT \(contents\): "
                            r"references\.bib")

    def test_a_directory_rename_split_is_refused(self) -> None:
        # The split leaves no conflicted stage: only git's messages report it.
        start = self.branch("dirs", {"dir/a": "a\n", "dir/b": "b\n"})
        self.bib_branches(start, theirs={"dir/c": "c\n"})
        self.git("checkout", "-q", "feature")
        for src, dst in (("dir/a", "x/a"), ("dir/b", "y/b")):
            (self.root / dst).parent.mkdir()
            self.git("mv", src, dst)
        self.commit("split dir")
        names = self.git("merge-tree", "--write-tree", "--name-only", "--no-messages",
                         "feature", "upstream", check=False)
        self.assertEqual(names.splitlines()[1:], ["references.bib"], "the only conflicted path")
        self.assert_refused(r"directory rename unclear split\): dir")

    def test_tracked_union_attributes_are_not_applied(self) -> None:
        # Tracked `merge=union` merges same-gap imports into an unsorted list without reporting
        # a conflict; the plain text merge reports it, so the merge is refused.
        start = self.branch("union", {
            ".gitattributes": "Complexity.lean merge=union\nreferences.bib merge=bibkeys\n",
            "Complexity.lean": "import A.W\nimport A.Z\n"})
        self.bib_branches(start, ours={"Complexity.lean": "import A.W\nimport A.Y\nimport A.Z\n"},
                          theirs={"Complexity.lean": "import A.W\nimport A.X\nimport A.Z\n"})
        names = self.git("merge-tree", "--write-tree", "--name-only", "--no-messages",
                         "feature", "upstream", check=False)
        self.assertEqual(names.splitlines()[1:], ["references.bib"], "git applies the union")
        for source in (None, "HEAD"):
            with self.subTest(GIT_ATTR_SOURCE=source):
                with patch.dict(os.environ, {"GIT_ATTR_SOURCE": source} if source else {}):
                    self.assert_refused(r"CONFLICT \(contents\): Complexity\.lean")

    def test_local_info_attributes_are_refused(self) -> None:
        self.bib_branches()
        info = pathlib.Path(self.git("rev-parse", "--path-format=absolute", "--git-path",
                                     "info/attributes"))
        info.parent.mkdir(exist_ok=True)
        info.write_text("# comments only\n\n", encoding="utf-8")
        self.assertIsNotNone(rbc.resolve("feature", "upstream", cwd=self.root))
        info.write_text("notes.md merge=union\n", encoding="utf-8")
        self.assert_refused(r"info/attributes sets attributes")

    def test_conflicting_entry_edits_are_refused(self) -> None:
        self.branch("feature", {"references.bib": bib(entry("Alpha2000", "X"), entry("Zeta2000"))})
        self.branch("upstream", {"references.bib": bib(entry("Alpha2000", "Y"), entry("Zeta2000"))})
        self.assert_refused("both sides changed entry `alpha2000`")

    def test_clean_merge_writes_nothing(self) -> None:
        self.branch("feature", {"notes.md": "one\n\ntwo\n\nthree\n\nfeature\n"})
        self.branch("upstream", {
            "references.bib": bib(entry("Alpha2000"), entry("Beta2001"), entry("Zeta2000"))})
        self.assertIsNone(rbc.resolve("feature", "upstream", cwd=self.root))

    def test_commit_mode_ignores_a_configured_driver(self) -> None:
        # A configured driver would hide the conflict that GitHub reports (here by reporting a
        # clean merge, which writes nothing); commit mode must still see and resolve it.
        self.git("config", "merge.bibkeys.driver", "true")
        self.bib_branches()
        sha = rbc.resolve("feature", "upstream", cwd=self.root)
        self.assertIsNotNone(sha)
        self.assertEqual(self.git("show", f"{sha}:references.bib") + "\n", bib(
            entry("Alpha2000"), entry("Beta2001"), entry("Kappa2001"), entry("Zeta2000")))

    def test_driver_falls_back_to_markers_on_any_failure(self) -> None:
        paths = [self.root / name for name in ("base", "ours", "theirs")]
        texts = (bib(entry("Alpha2000"), entry("Zeta2000")),
                 bib(entry("Alpha2000"), entry("Kappa2001"), entry("Zeta2000")),
                 bib(entry("Alpha2000"), entry("Beta2001"), entry("Zeta2000")))
        for path, text in zip(paths, texts):
            path.write_text(text, encoding="utf-8")
        with patch.object(rbc, "merge_bib", side_effect=RuntimeError("unexpected")), \
                patch("sys.stderr", new_callable=io.StringIO) as stderr:
            status = rbc.driver(*map(str, paths))
        self.assertEqual(status, 1)
        self.assertIn("unexpected; falling back to a text merge", stderr.getvalue())
        self.assertIn("<<<<<<< ours", paths[1].read_text(encoding="utf-8"))

    def test_driver_resolves_git_merge_and_falls_back_to_markers(self) -> None:
        self.git("config", "merge.bibkeys.driver",
                 f"'{sys.executable}' '{SCRIPT}' --driver %O %A %B")
        self.branch("upstream", {
            "references.bib": bib(entry("Alpha2000"), entry("Beta2001"), entry("Zeta2000"))})
        self.branch("feature", {
            "references.bib": bib(entry("Alpha2000"), entry("Kappa2001"), entry("Zeta2000"))})
        self.git("merge", "-q", "--no-edit", "upstream")
        self.assertEqual((self.root / "references.bib").read_text(encoding="utf-8"), bib(
            entry("Alpha2000"), entry("Beta2001"), entry("Kappa2001"), entry("Zeta2000")))

        self.branch("left", {"references.bib": bib(entry("Alpha2000", "X"), entry("Zeta2000"))})
        self.branch("right", {"references.bib": bib(entry("Alpha2000", "Y"), entry("Zeta2000"))})
        result = subprocess.run(["git", "merge", "-q", "--no-edit", "left"], cwd=self.root,
                                capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("falling back to a text merge", result.stderr)
        self.assertIn("<<<<<<< ours", (self.root / "references.bib").read_text(encoding="utf-8"))

    def test_cli_prints_the_commit_and_refuses_with_status_1(self) -> None:
        self.branch("feature", {
            "references.bib": bib(entry("Alpha2000"), entry("Kappa2001"), entry("Zeta2000"))})
        self.branch("upstream", {
            "references.bib": bib(entry("Alpha2000"), entry("Beta2001"), entry("Zeta2000"))})
        ok = subprocess.run([sys.executable, "-B", str(SCRIPT), "feature", "upstream"],
                            cwd=self.root, capture_output=True, text=True)
        self.assertEqual(ok.returncode, 0, ok.stderr)
        sha = ok.stdout.strip()
        self.assertEqual(self.git("rev-parse", f"{sha}^1"), self.git("rev-parse", "feature"))
        self.assertIn("nothing pushed", ok.stderr)
        self.write("notes.md", "changed\n")
        self.commit("upstream edit")
        self.git("checkout", "-q", "feature")
        self.write("notes.md", "other\n")
        self.commit("feature edit")
        refused = subprocess.run([sys.executable, "-B", str(SCRIPT), "feature", "upstream"],
                                 cwd=self.root, capture_output=True, text=True)
        self.assertEqual((refused.returncode, refused.stdout), (1, ""))
        self.assertIn("refused: conflicts other than", refused.stderr)


if __name__ == "__main__":
    unittest.main()
