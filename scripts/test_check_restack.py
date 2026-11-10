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
from unittest import mock

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


LAKEFILE = 'name = "fixture"\n\n[[lean_lib]]\nname = "CslibFrontier"\n'
PREAMBLE = "module  -- shake: keep-all --deprecated_module: ignore\n\n"
# The style of `CslibFrontierResults.lean`.
PLAIN = {"preamble": "", "keyword": "import"}


def aggregate(*names: str, preamble: str = PREAMBLE, keyword: str = "public import") -> str:
    """`CslibFrontier.lean` importing `Complexity.<name>` for each name, in the order given."""
    return preamble + "".join(f"{keyword} CslibFrontier.{name}\n" for name in names)


def modules(*names: str) -> dict[str, str]:
    return {f"CslibFrontier/{name}.lean": f"theorem {name.lower()}_holds : True := trivial\n"
            for name in names}


LIB = "namespace Foo\ndef x := 1\nend Foo\n\nnamespace Bar\ndef y := 2\nend Bar\n"


@unittest.skipUnless(shutil.which("git"), "git is required")
class RestackTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.git("init", "-q", "-b", "main")
        # `merge=union` is what `main` used before #3601; the replay must not depend on it.
        self.commit("base", {"lakefile.toml": LAKEFILE, "CslibFrontier.lean": aggregate("A", "C", "E"),
                             **modules("A", "C", "E"), "Lib.lean": LIB,
                             ".gitattributes": "CslibFrontier.lean merge=union\n"})

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
        """A PR branch adding the module `CslibFrontier.B`; returns its approved head."""
        self.git("checkout", "-q", "-b", "feature", "main")
        return self.commit("feature", files or {"CslibFrontier.lean": aggregate("A", "B", "C", "E"),
                                                **modules("B")})

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

    def test_aggregate_as_mk_all_writes_it_passes(self) -> None:
        approved = self.feature()
        self.on_main({"CslibFrontier.lean": aggregate("A", "Bb", "C", "E"), **modules("Bb")})
        # The union replay puts `main`'s line first, out of order.
        regenerated = aggregate("A", "B", "Bb", "C", "E")
        code, out = self.check(approved, self.merge_main({"CslibFrontier.lean": regenerated}))
        self.assertEqual(code, 0, out)
        self.assertIn("unlike the replay: CslibFrontier.lean", out)

    def test_aggregate_conflict_resolved_as_mk_all_writes_it_passes(self) -> None:
        # Without a merge attribute, the replay conflicts in the aggregate, as on GitHub.
        self.on_main({".gitattributes": "# no aggregate merge driver\n"})
        approved = self.feature()
        self.on_main({"CslibFrontier.lean": aggregate("A", "Bb", "C", "E"), **modules("Bb")})
        new = self.merge_main({"CslibFrontier.lean": aggregate("A", "B", "Bb", "C", "E")})
        code, out = self.check(approved, new)
        self.assertEqual(code, 0, out)
        self.assertIn("unlike the replay: CslibFrontier.lean", out)

    def test_import_resurrected_by_a_union_merge_is_reported(self) -> None:
        # The PR moves `CslibFrontier.C` to `CslibFrontier.D`; `main` adds `CslibFrontier.B` next to it.
        approved = self.feature({"CslibFrontier.lean": aggregate("A", "D", "E"),
                                 "CslibFrontier/C.lean": None, **modules("D")})
        self.on_main({"CslibFrontier.lean": aggregate("A", "B", "C", "E"), **modules("B")})
        union = self.merge_main()
        self.assertIn("import CslibFrontier.C\n", (self.root / "CslibFrontier.lean").read_text())
        code, out = self.check(approved, union)
        self.assertEqual(code, 1, out)
        self.assertIn("CslibFrontier.lean: not what `lake exe mk_all` writes", out)
        self.assertIn("+public import CslibFrontier.C", out)
        regenerated = self.commit("mk_all", {"CslibFrontier.lean": aggregate("A", "B", "D", "E")})
        code, out = self.check(approved, regenerated)
        self.assertEqual(code, 0, out)
        self.assertIn("unlike the replay: CslibFrontier.lean", out)

    def test_plain_aggregate_conflicting_on_its_first_line_passes(self) -> None:
        # Like `CslibFrontierResults.lean`: plain style and no merge attribute. Both sides insert an
        # import before the first one, so the replay conflicts on line 1 and shows no style.
        self.on_main({".gitattributes": "# no aggregate merge driver\n", "CslibFrontier/A.lean": None,
                      "CslibFrontier.lean": aggregate("C", "E", **PLAIN)})
        approved = self.feature({"CslibFrontier.lean": aggregate("B", "C", "E", **PLAIN),
                                 **modules("B")})
        self.on_main({"CslibFrontier.lean": aggregate("Bb", "C", "E", **PLAIN), **modules("Bb")})
        new = self.merge_main({"CslibFrontier.lean": aggregate("B", "Bb", "C", "E", **PLAIN)})
        replayed, conflicts = check_restack.replay(
            self.root, self.git("merge-base", "main", approved), approved, self.git("rev-parse", "main"))
        self.assertIn("CslibFrontier.lean", conflicts)
        self.assertTrue(self.git("cat-file", "blob", f"{replayed}:CslibFrontier.lean").startswith("<<<<<<<"))
        code, out = self.check(approved, new)
        self.assertEqual(code, 0, out)
        self.assertIn("unlike the replay: CslibFrontier.lean", out)
        # The style still comes from the other versions, so switching it is reported.
        module = self.commit("module", {"CslibFrontier.lean": aggregate("B", "Bb", "C", "E")})
        code, out = self.check(approved, module)
        self.assertEqual(code, 1, out)
        self.assertIn("CslibFrontier.lean: not what `lake exe mk_all` writes", out)

    def test_style_switched_by_the_approved_change_passes(self) -> None:
        # The PR switches the aggregate to plain imports while `main` adds a module. The headers
        # differ, so the driver leaves a text merge, which conflicts from line 1 on.
        self.on_main({".gitattributes": "CslibFrontier.lean merge=leanagg\n"})
        approved = self.feature({"CslibFrontier.lean": aggregate("A", "C", "E", **PLAIN)})
        self.on_main({"CslibFrontier.lean": aggregate("A", "Bb", "C", "E"), **modules("Bb")})
        new = self.merge_main({"CslibFrontier.lean": aggregate("A", "Bb", "C", "E", **PLAIN)})
        code, out = self.check(approved, new)
        self.assertEqual(code, 0, out)
        self.assertIn("the approved change switches CslibFrontier.lean to plain style", out)
        # Regenerating in `main`'s module style would undo the reviewed switch.
        module = self.commit("module", {"CslibFrontier.lean": aggregate("A", "Bb", "C", "E")})
        code, out = self.check(approved, module)
        self.assertEqual(code, 1, out)
        self.assertIn("in plain style, which the approved change switches it to", out)

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
        edit = {"CslibFrontier/B.lean": "theorem b_holds : True := by trivial\n"}
        code, out = self.check(approved, self.commit("edit", edit))
        self.assertEqual(code, 1, out)
        self.assertIn("CslibFrontier/B.lean: the new head differs", out)
        self.assertIn("+theorem b_holds : True := by trivial", out)

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
        new = self.commit("sneak", {"CslibFrontier.lean": aggregate("A", "B", "C", "D", "E")})
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("+public import CslibFrontier.D", out)

    def test_unsorted_aggregate_is_reported(self) -> None:
        approved = self.feature()
        self.on_main({"CslibFrontier.lean": aggregate("A", "Bb", "C", "E"), **modules("Bb")})
        # This is also what the union replay holds, so the trees are identical.
        new = self.merge_main({"CslibFrontier.lean": aggregate("A", "Bb", "B", "C", "E")})
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("CslibFrontier.lean: not what `lake exe mk_all` writes", out)

    def test_aggregate_switching_style_is_reported(self) -> None:
        approved = self.feature()
        self.on_main({"Other.lean": "def o := 0\n"})
        plain = aggregate("A", "B", "C", "E", preamble="", keyword="import")
        code, out = self.check(approved, self.merge_main({"CslibFrontier.lean": plain}))
        self.assertEqual(code, 1, out)
        self.assertIn("CslibFrontier.lean: not what `lake exe mk_all` writes", out)

    def test_aggregate_of_an_unknown_layout_is_compared_with_the_replay(self) -> None:
        self.on_main({"lakefile.lean": "-- Lake prefers this file\n"})
        approved = self.feature()
        self.on_main({"Other.lean": "def o := 0\n"})
        code, out = self.check(approved, self.merge_main())
        self.assertEqual(code, 0, out)
        self.assertIn("CslibFrontier.lean compared with the replay only", out)
        reordered = self.commit("reorder", {"CslibFrontier.lean": aggregate("A", "C", "B", "E")})
        code, out = self.check(approved, reordered)
        self.assertEqual(code, 1, out)
        self.assertIn("its `mk_all` content could not be derived: Lake reads `lakefile.lean`", out)

    def test_unusual_module_paths_are_not_derived(self) -> None:
        for path, mode in (("CslibFrontier/Odd-name.lean", "100644"), ("CslibFrontier/Link", "120000"),
                           ("CslibFrontier/Sub.lean/X.lean", "100644")):
            entries = {"CslibFrontier": "040000", "CslibFrontier/A.lean": "100644", path: mode}
            with self.subTest(path=path), self.assertRaises(check_restack.Underivable):
                check_restack.canonical_aggregate(entries, "", "CslibFrontier", True)

    def test_mode_change_is_reported(self) -> None:
        approved = self.feature()
        self.git("update-index", "--chmod=+x", "CslibFrontier/B.lean")
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
        self.on_main({".gitattributes": "CslibFrontier.lean merge=union\n*.txt merge=keep\n",
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
        dishonest = self.commit("edit", {"CslibFrontier/B.lean": "theorem b : True := by sorry\n"})
        self.git("replace", dishonest, honest)
        code, out = self.check(approved, dishonest)
        self.assertEqual(code, 1, out)
        self.assertIn("B.lean", out)

    def test_git_config_variable_cannot_hide_a_configured_driver(self) -> None:
        # `GIT_CONFIG` redirects only `git config`, so the driver listing would miss `keep`.
        self.on_main({".gitattributes": "CslibFrontier.lean merge=union\n*.txt merge=keep\n",
                      "notes.txt": "a\nb\nc\n"})
        approved = self.feature({"notes.txt": "a\nB\nc\n"})
        self.on_main({"notes.txt": "a\nb\nc\nd\n"})
        new = self.merge_main({"notes.txt": "a\nb\nc\nd\n"})
        self.git("config", "merge.keep.driver", "true")
        with mock.patch.dict(os.environ, {"GIT_CONFIG": os.devnull}):
            code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("notes.txt", out)

    def test_configured_aggregate_driver_is_replaced_by_this_checkout(self) -> None:
        self.git("config", "merge.leanagg.driver", "true")
        options = check_restack.driver_config(self.root)
        drivers = [option for option in options if option.startswith("merge.leanagg.driver=")]
        self.assertEqual(len(drivers), 1, options)
        self.assertTrue(drivers[0].endswith("resolve_aggregate_conflict.py %O %A %B"), drivers)

    def test_configured_driver_shadowing_a_builtin_is_refused(self) -> None:
        approved = self.feature()
        self.on_main({"Other.lean": "def o := 0\n"})
        new = self.merge_main()
        for name in ("union", "text"):
            self.git("config", f"merge.{name}.driver", "true")
            code, out = self.check(approved, new)
            self.assertEqual(code, 2, out)
            self.assertIn("built-in", out)
            self.git("config", "--unset", f"merge.{name}.driver")

    def grafted_history(self) -> tuple[str, str, str, str]:
        """An approved PR, `main`'s tip M, a sibling Y of M that also weakens `Lib.lean`, and a new
        head merging Y. Grafting Y under M makes Y the merge base, so its edit looks like `main`'s."""
        approved = self.feature({"B.lean": "theorem b : True := trivial\n"})
        main = self.on_main({"Other.lean": "def o := 0\n"})
        self.git("checkout", "-q", "-b", "evil", "main^")
        sibling = self.commit("evil", {"Other.lean": "def o := 0\n",
                                       "Lib.lean": "theorem weakened : True := by sorry\n"})
        self.git("checkout", "-q", "feature")
        self.git("merge", "-q", "--no-edit", "evil")
        return approved, main, sibling, self.git("rev-parse", "HEAD")

    def test_grafts_cannot_move_the_merge_base(self) -> None:
        approved, main, sibling, new = self.grafted_history()
        self.assertEqual(self.check(approved, new)[0], 1)
        grafts = self.root / ".git" / "info" / "grafts"
        grafts.parent.mkdir(exist_ok=True)
        grafts.write_text(f"{main} {sibling}\n")
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("Lib.lean", out)
        grafts.rename(self.root / ".git" / "grafts-elsewhere")
        with mock.patch.dict(os.environ, {"GIT_GRAFT_FILE": str(self.root / ".git" / "grafts-elsewhere")}):
            code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)

    def test_shallow_repository_is_refused(self) -> None:
        approved = self.feature()
        self.on_main({"Other.lean": "def o := 0\n"})
        self.git("checkout", "-q", "-b", "evil", "main")
        sibling = self.commit("revert main", {"Other.lean": None})
        self.git("checkout", "-q", "feature")
        self.git("merge", "-q", "--no-edit", "evil")
        new = self.git("rev-parse", "HEAD")
        self.assertEqual(self.check(approved, new)[0], 1)
        shallow = self.root / ".git" / "elsewhere-shallow"
        shallow.write_text(f"{sibling}\n")
        # A `GIT_SHALLOW_FILE` is ignored, so the true history decides.
        with mock.patch.dict(os.environ, {"GIT_SHALLOW_FILE": str(shallow)}):
            code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        shallow.rename(self.root / ".git" / "shallow")
        code, out = self.check(approved, new)
        self.assertEqual(code, 2, out)
        self.assertIn("shallow", out)

    def test_rename_limit_cannot_hide_a_rename_delete_conflict(self) -> None:
        axiom = "".join(f"theorem t{i} : {i} = {i} := rfl\n" for i in range(40))
        self.on_main({"Axiom.lean": axiom})
        approved = self.feature({"Axiom.lean": None})
        self.on_main({"Axiom.lean": None, "Core/Kept.lean": axiom + "theorem extra : True := trivial\n",
                      "Unrelated.lean": "def u := 0\n"})
        # The restack keeps the renamed file, dropping the PR's deletion.
        new = self.merge_main({"Core/Kept.lean": axiom + "theorem extra : True := trivial\n"})
        self.git("config", "merge.renameLimit", "1")
        code, out = self.check(approved, new)
        self.assertEqual(code, 1, out)
        self.assertIn("Core/Kept.lean", out)

    # The bibliography merges entry by entry, as `scripts/resolve_bib_conflict.py` does.

    def bib_conflict(self) -> str:
        """A PR adding `Kappa2001` approved, and `main` adding `Beta2001` in the same gap."""
        self.on_main({".gitattributes": "CslibFrontier.lean merge=union\nreferences.bib merge=bibkeys\n",
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


class EnvironmentTests(unittest.TestCase):
    def test_history_and_config_redirections_are_removed(self) -> None:
        hostile = {"GIT_TEST_COMMIT_GRAPH": "1", "GIT_TEST_ANYTHING": "x", "GIT_CONFIG": "f",
                   "GIT_SHALLOW_FILE": "s", "GIT_ATTR_SOURCE": "t", "GIT_GRAFT_FILE": "g"}
        with mock.patch.dict(os.environ, hostile):
            env = check_restack.environment()
        self.assertFalse(any(key.startswith("GIT_TEST_") for key in env))
        for key in ("GIT_CONFIG", "GIT_SHALLOW_FILE", "GIT_ATTR_SOURCE"):
            self.assertNotIn(key, env)
        self.assertEqual(env["GIT_GRAFT_FILE"], os.devnull)
        self.assertEqual(env["GIT_NO_REPLACE_OBJECTS"], "1")


class AggregateStyleTests(unittest.TestCase):
    MODULE = (PREAMBLE + "public import X\n").encode()
    PLAIN = b"import X\n"
    CONFLICT = b"<<<<<<< ours\nimport A\n=======\nimport B\n>>>>>>> theirs\n"

    def style(self, base: bytes | None, onto: bytes | None, approved: bytes | None,
              replayed: bytes) -> tuple[bool, bool]:
        return check_restack.aggregate_style((base, onto, approved), replayed)

    def test_agreeing_versions_settle_the_style(self) -> None:
        self.assertEqual(self.style(self.PLAIN, self.PLAIN, self.PLAIN, self.CONFLICT), (False, False))
        self.assertEqual(self.style(None, None, self.MODULE, self.CONFLICT), (True, False))

    def test_the_approved_change_switching_the_style_wins(self) -> None:
        self.assertEqual(self.style(self.MODULE, self.MODULE, self.PLAIN, self.MODULE), (False, True))
        self.assertEqual(self.style(self.PLAIN, self.MODULE, self.MODULE, self.CONFLICT), (True, True))

    def test_otherwise_the_replay_decides(self) -> None:
        # Only `main` switches the style, the base is missing, or a version itself has markers.
        for versions in ((self.MODULE, self.PLAIN, self.MODULE), (None, self.PLAIN, self.MODULE),
                         (self.CONFLICT, self.PLAIN, self.PLAIN)):
            with self.subTest(versions=versions):
                self.assertEqual(self.style(*versions, self.PLAIN), (False, False))
                with self.assertRaises(check_restack.Underivable):
                    self.style(*versions, self.CONFLICT)


class AggregateListTests(unittest.TestCase):
    def test_listed_aggregates_exist(self) -> None:
        for path in check_restack.AGGREGATES:
            self.assertTrue((ROOT / path).is_file(), path)

    @unittest.skipUnless(shutil.which("git") and (ROOT / ".git").exists(), "needs a git checkout")
    def test_committed_aggregates_are_what_mk_all_writes(self) -> None:
        # Keeps the derivation in step with `scripts/MkAll.lean` and the Lake layout.
        head = check_restack.out(ROOT, "rev-parse", "HEAD")
        canonical, wrong, underivable, switched = check_restack.check_aggregates(
            ROOT, (head, head, head), head, head)
        self.assertEqual(sorted(canonical), sorted(check_restack.AGGREGATES), (wrong, underivable))
        self.assertEqual(switched, {})


if __name__ == "__main__":
    unittest.main()
