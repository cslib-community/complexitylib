"""Temporary-repository tests for scripts/check_restack.py, including attempts to pass a changed
restack off as identical."""

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

ROOT = pathlib.Path(__file__).resolve().parents[1]

GIT_ENV = {
    **os.environ,
    "GIT_AUTHOR_NAME": "Test",
    "GIT_AUTHOR_EMAIL": "test@example.com",
    "GIT_COMMITTER_NAME": "Test",
    "GIT_COMMITTER_EMAIL": "test@example.com",
    "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_CONFIG_NOSYSTEM": "1",
}

def entry(key: str) -> str:
    return f"@article{{{key},\n  author = {{A}},\n  title  = {{T}}\n}}"


def bib(*entries: str) -> str:
    return "\n\n".join(entries) + "\n"


AGGREGATE = "-- generated\n\nimport A\nimport C\nimport E\n"
LIB = "namespace Foo\ndef x := 1\nend Foo\n\nnamespace Bar\ndef y := 2\nend Bar\n"


@unittest.skipUnless(shutil.which("git"), "git is required")
class RestackTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.git("init", "-q", "-b", "main")
        self.commit("base", {"Complexity.lean": AGGREGATE, "Lib.lean": LIB,
                             ".gitattributes": "Complexity.lean merge=union\n"})

    def git(self, *args: str) -> str:
        return subprocess.run(["git", "-C", str(self.root), *args], capture_output=True,
                              text=True, check=True, env=GIT_ENV).stdout.strip()

    def write(self, files: dict[str, str | bytes | None]) -> None:
        for name, content in files.items():
            path = self.root / name
            if content is None:
                path.unlink()
            elif isinstance(content, bytes):
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(content)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(content)

    def commit(self, message: str, files: dict[str, str | bytes | None]) -> str:
        self.write(files)
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD")

    def check(self, approved: str, new: str, *extra: str) -> tuple[int, str]:
        output = io.StringIO()
        with contextlib.redirect_stdout(output), contextlib.redirect_stderr(output):
            code = check_restack.main([approved, new, "--base", "main", "--root", str(self.root),
                                       *extra])
        return code, output.getvalue()

    def feature(self, files: dict[str, str | bytes | None] | None = None) -> str:
        """A PR branch adding `import B` and a module; returns its approved head."""
        self.git("checkout", "-q", "-b", "feature", "main")
        return self.commit("feature", files or {
            "Complexity.lean": "-- generated\n\nimport A\nimport B\nimport C\nimport E\n",
            "B.lean": "theorem b : True := trivial\n"})

    def on_main(self, files: dict[str, str | bytes | None]) -> str:
        self.git("checkout", "-q", "main")
        return self.commit("main moves", files)

    def merge_main(self, resolution: dict[str, str | bytes | None] | None = None) -> str:
        """Merge `main` into `feature`, writing `resolution` over the result."""
        self.git("checkout", "-q", "feature")
        subprocess.run(["git", "-C", str(self.root), "merge", "-q", "--no-commit", "--no-ff",
                        "main"], capture_output=True, env=GIT_ENV)
        self.write(resolution or {})
        self.git("add", "-A")
        self.git("commit", "-q", "--no-edit")
        return self.git("rev-parse", "HEAD")

    # Honest restacks pass.

    def test_clean_merge_of_main_passes(self) -> None:
        approved = self.feature()
        self.on_main({"Lib.lean": LIB.replace("def y := 2", "def y := 3")})
        code, out = self.check(approved, self.merge_main())
        self.assertEqual(code, 0, out)
        self.assertIn("identical to the approved change", out)

    def test_rebase_onto_newer_main_passes(self) -> None:
        approved = self.feature()
        self.on_main({"Other.lean": "def o := 0\n"})
        self.git("checkout", "-q", "-b", "rebased", approved)
        self.git("rebase", "-q", "main")
        code, out = self.check(approved, self.git("rev-parse", "HEAD"))
        self.assertEqual(code, 0, out)

    def test_aggregate_in_sorted_order_passes(self) -> None:
        approved = self.feature()
        self.on_main({"Complexity.lean": "-- generated\n\nimport A\nimport Bb\nimport C\nimport E\n",
                      "Bb.lean": "def bb := 0\n"})
        sorted_imports = "-- generated\n\nimport A\nimport B\nimport Bb\nimport C\nimport E\n"
        code, out = self.check(approved, self.merge_main({"Complexity.lean": sorted_imports}))
        self.assertEqual(code, 0, out)
        self.assertIn("aggregates differing only in line order: Complexity.lean", out)

    def stack(self, lower_final: str) -> tuple[str, str, str]:
        """An upper PR approved on a lower PR that then lands, squashed, as `lower_final`.

        Returns the lower head at approval, the approved upper head and the restacked upper head.
        """
        self.git("checkout", "-q", "-b", "lower", "main")
        lower = self.commit("lower", {"Lower.lean": "def z := 3\n"})
        self.git("checkout", "-q", "-b", "feature", "lower")
        approved = self.commit("upper", {"B.lean": "def b := z\n"})
        self.git("checkout", "-q", "lower")
        self.commit("lower revised", {"Lower.lean": lower_final})
        self.git("checkout", "-q", "main")
        self.git("merge", "-q", "--squash", "lower")
        self.git("commit", "-q", "-m", "lower (#1)")
        return lower, approved, self.merge_main({"Lower.lean": lower_final})

    def test_stacked_pr_whose_lower_pr_landed_unchanged_passes(self) -> None:
        _, approved, new = self.stack("def z := 3\n")
        self.assertEqual(self.check(approved, new)[0], 0)

    def test_stacked_pr_whose_lower_pr_changed_needs_its_base(self) -> None:
        lower, approved, new = self.stack("def z := 4\n")
        # Replayed from `main`, the approved change would restore the lower PR's first version.
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("Lower.lean", out)
        code, out = self.check(approved, new, "--approved-base", lower)
        self.assertEqual(code, 0, out)
        self.assertIn(f"--approved-base {lower}", out)

    # Changed restacks are reported.

    def test_edited_pr_line_is_reported(self) -> None:
        approved = self.feature()
        code, out = self.check(approved, self.commit("edit", {"B.lean": "theorem b : True := by trivial\n"}))
        self.assertEqual(code, 1, out)
        self.assertIn("B.lean: the new head differs", out)
        self.assertIn("+theorem b : True := by trivial", out)

    def test_carriage_return_cannot_hide_content(self) -> None:
        approved = self.feature({"s.py": "y = 1\n"})
        new = self.commit("hide", {"s.py": "y = 1\rimport os; print('PWNED')\n"})
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("\\r", out)

    def test_crlf_line_endings_are_reported(self) -> None:
        approved = self.feature({"s.py": "y = 1\n"})
        self.assertEqual(self.check(approved, self.commit("crlf", {"s.py": b"y = 1\r\n"}))[0], 1)

    def test_paths_that_git_quotes_are_reported(self) -> None:
        approved = self.feature()
        new = self.commit("quoted", {".github/workflows/é.yml": "on: push\n",
                                     'Z"q.lean': "", "p b/q": "x\n"})
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        for path in (".github/workflows/é.yml", 'Z"q.lean', "p b/q"):
            self.assertIn(path, out)

    def test_diff_configuration_cannot_hide_changes(self) -> None:
        approved = self.feature()
        new = self.commit("axiom", {"Evil.lean": "axiom bad : False\n"})
        self.git("config", "diff.noprefix", "true")
        self.git("config", "diff.external", "true")
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("Evil.lean", out)

    def test_moving_a_pr_line_to_another_namespace_is_reported(self) -> None:
        approved = self.feature({"Lib.lean": LIB.replace("def x := 1\n", "def x := 1\ntheorem t : True := trivial\n")})
        moved = self.commit("move", {"Lib.lean": LIB.replace("def y := 2\n", "def y := 2\ntheorem t : True := trivial\n")})
        code, out = self.check(approved, moved)
        self.assertEqual(code, 1, out)
        self.assertIn("Lib.lean", out)

    def test_conflict_resolution_is_reported_even_if_it_keeps_the_pr_side(self) -> None:
        approved = self.feature({"Lib.lean": LIB.replace("def y := 2", "def y := 20")})
        self.on_main({"Lib.lean": LIB.replace("def y := 2", "def y := 3")})
        new = self.merge_main({"Lib.lean": LIB.replace("def y := 2", "def y := 20")})
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("Lib.lean: the replay conflicted here", out)

    def test_keeping_a_file_main_deleted_is_reported(self) -> None:
        approved = self.feature({"Lib.lean": LIB + "-- touched\n"})
        self.on_main({"Lib.lean": None})
        new = self.merge_main({"Lib.lean": LIB + "-- touched\n"})
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("Lib.lean", out)

    def test_aggregate_with_an_extra_import_is_reported(self) -> None:
        approved = self.feature()
        new = self.commit("sneak", {
            "Complexity.lean": "-- generated\n\nimport A\nimport B\nimport C\nimport D\nimport E\n"})
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("+import D", out)

    def test_mode_change_is_reported(self) -> None:
        approved = self.feature()
        self.git("update-index", "--chmod=+x", "B.lean")
        self.git("commit", "-q", "-m", "chmod")
        code, out = self.check(approved, self.git("rev-parse", "HEAD"))
        self.assertEqual(code, 1, out)
        self.assertIn("new mode", out)

    def test_binary_change_is_reported(self) -> None:
        approved = self.feature({"img.bin": b"\x00\x01\x02"})
        code, out = self.check(approved, self.commit("bin", {"img.bin": b"\x00\x01\x03"}))
        self.assertEqual(code, 1, out)
        self.assertIn("img.bin", out)

    def test_user_merge_driver_cannot_hide_a_conflict_resolution(self) -> None:
        approved = self.feature({"Lib.lean": LIB.replace("def y := 2", "def y := 20")})
        self.on_main({"Lib.lean": LIB.replace("def y := 2", "def y := 3")})
        new = self.merge_main({"Lib.lean": LIB.replace("def y := 2", "def y := 20")})
        attributes = self.root.parent / f"{self.root.name}-attributes"
        attributes.write_text("*.lean merge=theirs\n")
        self.addCleanup(attributes.unlink)
        self.git("config", "core.attributesFile", str(attributes))
        self.git("config", "merge.theirs.driver", "cp %B %A")
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)

    def test_attributes_in_info_are_refused(self) -> None:
        approved = self.feature()
        self.on_main({"Other.lean": "def o := 0\n"})
        new = self.merge_main()
        info = self.root / ".git" / "info"
        info.mkdir(exist_ok=True)
        for line in ("*.lean merge=union\n", "*.lean binary\n"):
            (info / "attributes").write_text(f"# local\n{line}")
            code, out = self.check(approved, new)
            self.assertEqual(code, 2, out)
            self.assertIn("sets attributes", out)

    def test_configured_driver_named_by_tracked_attributes_cannot_hide_a_resolution(self) -> None:
        self.on_main({".gitattributes": "Complexity.lean merge=union\n*.txt merge=keep\n",
                      "notes.txt": "a\nb\nc\n"})
        approved = self.feature({"notes.txt": "a\nB\nc\n"})
        self.on_main({"notes.txt": "a\nb\nc\nd\n"})
        # The author keeps `main`'s version, dropping the approved edit; a driver that keeps the
        # current side would replay to the same tree.
        new = self.merge_main({"notes.txt": "a\nb\nc\nd\n"})
        self.git("config", "merge.keep.driver", "true")
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("notes.txt", out)

    def test_merge_default_cannot_select_a_union_merge(self) -> None:
        approved = self.feature({"Lib.lean": LIB.replace("def y := 2", "def y := 20")})
        self.on_main({"Lib.lean": LIB.replace("def y := 2", "def y := 3")})
        both = LIB.replace("def y := 2", "def y := 3\ndef y := 20")
        new = self.merge_main({"Lib.lean": both})
        self.git("config", "merge.default", "union")
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("Lib.lean", out)

    def test_replace_objects_cannot_substitute_the_new_head(self) -> None:
        approved = self.feature()
        self.on_main({"Other.lean": "def o := 0\n"})
        honest = self.merge_main()
        self.git("checkout", "-q", "-b", "dishonest", "main")
        self.git("merge", "-q", "--no-ff", "--no-edit", "feature")
        dishonest = self.commit("edit", {"B.lean": "theorem b : True := by sorry\n"})
        self.git("replace", dishonest, honest)
        code, out = self.check(approved, dishonest)
        self.assertEqual(code, 1, out)
        self.assertIn("B.lean", out)

    # The bibliography merges entry by entry, as `scripts/resolve_bib_conflict.py` does.

    def bib_conflict(self) -> str:
        """A PR adding `Kappa2001` approved, and `main` adding `Beta2001` in the same gap."""
        self.on_main({".gitattributes": "Complexity.lean merge=union\nreferences.bib merge=bibkeys\n",
                      "references.bib": bib(entry("Alpha2000"), entry("Zeta2000"))})
        approved = self.feature({"references.bib": bib(entry("Alpha2000"), entry("Kappa2001"),
                                                       entry("Zeta2000"))})
        self.on_main({"references.bib": bib(entry("Alpha2000"), entry("Beta2001"),
                                            entry("Zeta2000"))})
        return approved

    def test_bib_merge_written_by_the_resolver_passes(self) -> None:
        approved = self.bib_conflict()
        resolver = subprocess.run([sys.executable, str(ROOT / "scripts" / "resolve_bib_conflict.py"),
                                   "feature", "main"], cwd=self.root, capture_output=True,
                                  text=True, env=GIT_ENV)
        self.assertEqual(resolver.returncode, 0, resolver.stderr)
        code, out = self.check(approved, resolver.stdout.strip())
        self.assertEqual(code, 0, out)

    def test_bib_merge_dropping_a_pr_entry_is_reported(self) -> None:
        approved = self.bib_conflict()
        new = self.merge_main({"references.bib": bib(entry("Alpha2000"), entry("Beta2001"),
                                                     entry("Zeta2000"))})
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("references.bib", out)

    def test_configured_bib_driver_cannot_change_the_replay(self) -> None:
        approved = self.bib_conflict()
        new = self.merge_main({"references.bib": bib(entry("Alpha2000"), entry("Beta2001"),
                                                     entry("Zeta2000"))})
        self.git("config", "merge.bibkeys.driver", "true")
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("references.bib", out)

    def test_hidden_submodule_pointer_change_is_reported(self) -> None:
        self.git("checkout", "-q", "-b", "feature", "main")
        self.git("update-index", "--add", "--cacheinfo", f"160000,{'1' * 40},sub")
        self.git("commit", "-q", "-m", "add submodule")
        approved = self.git("rev-parse", "HEAD")
        self.git("update-index", "--cacheinfo", f"160000,{'2' * 40},sub")
        self.git("commit", "-q", "-m", "move submodule")
        self.git("config", "diff.ignoreSubmodules", "all")
        code, out = self.check(approved, self.git("rev-parse", "HEAD"))
        self.assertEqual(code, 1, out)
        self.assertIn("sub", out)

    def test_unlanded_lower_branch_needs_approved_base(self) -> None:
        self.git("checkout", "-q", "-b", "lower", "main")
        lower = self.commit("lower", {"Lower.lean": "axiom unreviewed : False\n"})
        self.git("checkout", "-q", "-b", "feature", "lower")
        approved = self.commit("upper", {"B.lean": "def b := 0\n"})
        self.on_main({"Other.lean": "def o := 0\n"})
        new = self.merge_main()
        # Replayed from `main`, the lower branch's unreviewed lines look approved; the base given
        # by the approval exposes them.
        self.assertEqual(self.check(approved, new)[0], 0)
        code, out = self.check(approved, new, "--approved-base", lower)
        self.assertEqual(code, 1, out)
        self.assertIn("Lower.lean", out)

    # Errors.

    def test_empty_approved_change_is_an_error(self) -> None:
        self.feature()
        main = self.git("rev-parse", "main")
        code, out = self.check(main, "feature")
        self.assertEqual(code, 2, out)
        self.assertIn("makes no change", out)

    def test_unknown_revision_is_an_error(self) -> None:
        code, out = self.check("0" * 40, "HEAD")
        self.assertEqual(code, 2, out)
        self.assertIn("could not be fetched", out)


class AggregateListTests(unittest.TestCase):
    def test_listed_aggregates_exist(self) -> None:
        for path in check_restack.AGGREGATES:
            self.assertTrue((ROOT / path).is_file(), path)


if __name__ == "__main__":
    unittest.main()
