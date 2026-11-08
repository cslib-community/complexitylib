"""Tests for scripts/rename_module_root.py: the rewriting rules, apply mode and restack mode."""

from __future__ import annotations

import os
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import rename_module_root as r  # noqa: E402

PATHS = [
    "Complexity.lean",
    "Complexity/Init.lean",
    "Complexity/Computability/Complexity/Classes/NP.lean",
    "Complexity/Foundations/Data/Encoding.lean",
    "Complexity/Algorithms/Sort.lean",
    "ComplexityTests/HousingMarket.lean",
    "ComplexityResults/Registry.lean",
    "guide/ComplexityGuide.lean",
    "guide/ComplexityGuide/FirstSteps.lean",
    "guide/ComplexityGuideMain.lean",
]
SHA = "13e6a31951bf1c89a1a6258c44f9444aecbbefd8"


def rewrite(path: str, text: str) -> str:
    return r.Rewriter(r.Inventory.from_paths(PATHS)).rewrite(path, text)


class LeanRules(unittest.TestCase):
    def test_imports_including_multiline_ones(self) -> None:
        text = textwrap.dedent("""\
            module
            -- upstream: candidate

            public import Complexity.Init
            public import
              Complexity.Computability.Complexity.Classes.NP
            meta import all ComplexityTests.HousingMarket
            import Cslib.Computability.Complexity

            public section
            """)
        out = rewrite("Complexity/X.lean", text)
        self.assertIn("public import CslibFrontier.Init\n", out)
        self.assertIn("  CslibFrontier.Computability.Complexity.Classes.NP\n", out)
        self.assertIn("meta import all CslibFrontierTests.HousingMarket\n", out)
        self.assertIn("import Cslib.Computability.Complexity\n", out)

    def test_declarations_and_namespaces_keep_their_names(self) -> None:
        text = textwrap.dedent("""\
            module
            public import Complexity.Init
            namespace Cslib
            open Complexity
            namespace ComplexityTests.HousingMarket
            theorem t : Complexity.P = Cslib.Complexity.P := rfl
            example := ComplexityResults.Registry.entries
            end ComplexityTests.HousingMarket
            """)
        out = rewrite("ComplexityTests/X.lean", text)
        self.assertEqual(out.split("\n", 2)[2], text.split("\n", 2)[2])

    def test_module_name_literals(self) -> None:
        text = textwrap.dedent("""\
            import Lean
            def a := (`Complexity).isPrefixOf `ComplexityTests
            def b := `Complexity.Foundations.Data.Encoding
            def c := ``Complexity.P
            def d := `ComplexityTests.HousingMarket.decl
            def e := [Complexity.Init]
            def f := [ComplexityTests.HousingMarket]
            """)
        out = rewrite("scripts/X.lean", text)
        self.assertIn("(`CslibFrontier).isPrefixOf `CslibFrontierTests", out)
        self.assertIn("`CslibFrontier.Foundations.Data.Encoding", out)
        self.assertIn("``Complexity.P", out)
        self.assertIn("`ComplexityTests.HousingMarket.decl", out)
        # A module of the main root named in code (an audit allow-list) is renamed; the other
        # roots are also namespaces and are not.
        self.assertIn("[CslibFrontier.Init]", out)
        self.assertIn("[ComplexityTests.HousingMarket]", out)

    def test_docstrings_rename_modules_not_declarations(self) -> None:
        text = textwrap.dedent("""\
            import Mathlib
            /-! See `Complexity.Foundations.Data.Encoding`, the `Complexity.Computability` area,
            the stale `Complexity.Algorithms.Gone`, the class `Complexity.NP`, the decl
            `ComplexityTests.HousingMarket.example1`, the imported `Complexity` modules, the
            `Complexity.` prefix, `Complexity.*`, and *Computational Complexity*. A link:
            [encoding](Complexity/Foundations/Data/Encoding.lean). -/
            """)
        out = rewrite("Complexity/X.lean", text)
        for expected in ("`CslibFrontier.Foundations.Data.Encoding`",
                         "`CslibFrontier.Computability` area", "`CslibFrontier.Algorithms.Gone`",
                         "`Complexity.NP`", "`ComplexityTests.HousingMarket.example1`",
                         "imported `CslibFrontier` modules", "`CslibFrontier.` prefix",
                         "`CslibFrontier.*`", "*Computational Complexity*",
                         "(CslibFrontier/Foundations/Data/Encoding.lean)"):
            self.assertIn(expected, out)

    def test_lengthened_lines_are_rewrapped(self) -> None:
        doc = ("The proof is in `Complexity.Foundations.Data.Encoding`, and the client in "
               "`Complexity.Init` uses it.")
        long_import = "Complexity.Computability.Complexity.Classes.NP" + "X" * 51
        text = (f"module\npublic import\n  {long_import}\n\n/-! {doc} -/\n"
                f"/-- info: {doc} -/\n#guard_msgs in\n#eval 0\n"
                f"-- {doc}\n")
        inventory = r.Inventory.from_paths(PATHS + [long_import.replace(".", "/") + ".lean"])
        out = r.Rewriter(inventory).rewrite("Complexity/X.lean", text)
        lines = out.split("\n")
        self.assertEqual(lines[1], "public import CslibFrontier" + long_import[10:])
        self.assertEqual(lines[3:5], [
            "/-! The proof is in `CslibFrontier.Foundations.Data.Encoding`, and the client in",
            "`CslibFrontier.Init` uses it. -/"])
        self.assertTrue(lines[5].startswith("/-- info:") and len(lines[5]) > r.MAX_LINE)
        self.assertEqual(lines[8:10], [
            "-- The proof is in `CslibFrontier.Foundations.Data.Encoding`, and the client in "
            "`CslibFrontier.Init`", "-- uses it."])
        self.assertEqual(r.Rewriter(inventory).rewrite("Complexity/X.lean", out), out)

    def test_verso_module_references(self) -> None:
        text = textwrap.dedent("""\
            import ComplexityGuide.FirstSteps
            open ComplexityGuide.ApiDocs
            #doc (Manual) "Guide" =>
            {include 1 ComplexityGuide.FirstSteps}
            `import Complexity` imports everything; see {module}`Complexity.Init`.
            """)
        out = rewrite("guide/ComplexityGuide.lean", text)
        self.assertIn("import CslibFrontierGuide.FirstSteps", out)
        self.assertIn("open ComplexityGuide.ApiDocs", out)
        self.assertIn("{include 1 CslibFrontierGuide.FirstSteps}", out)
        self.assertIn("`import CslibFrontier` imports", out)
        self.assertIn("{module}`CslibFrontier.Init`", out)
        main = "def main := manualMain (%doc ComplexityGuide) (importEnv `ComplexityGuide)\n"
        self.assertEqual(rewrite("guide/ComplexityGuideMain.lean", main),
                         "def main := manualMain (%doc CslibFrontierGuide) "
                         "(importEnv `CslibFrontierGuide)\n")


class TextRules(unittest.TestCase):
    def test_paths(self) -> None:
        text = textwrap.dedent(f"""\
            [a](../../Complexity/Computability/Complexity/Classes/NP.lean)
            [b](../ComplexityTests/HousingMarket.lean) [c](abstracts/ComplexityAbstracts/X.lean)
            [d](https://github.com/cslib-community/complexitylib/blob/main/ComplexityTests/X.lean)
            [e](https://github.com/cslib-community/complexitylib/blob/{SHA}/Complexity/Init.lean)
            [f](https://www.cslib.io/complexitylib/Complexity/Init.html) Complexity.lean
            under `Complexity/`; nested Computability/Complexity/Classes stays.
            """)
        out = rewrite("manual/x.md", text)
        self.assertIn("(../../CslibFrontier/Computability/Complexity/Classes/NP.lean)", out)
        self.assertIn("(../CslibFrontierTests/HousingMarket.lean)", out)
        self.assertIn("(abstracts/CslibFrontierAbstracts/X.lean)", out)
        self.assertIn("cslib-frontier/blob/main/CslibFrontierTests/X.lean", out)
        self.assertIn(f"cslib-frontier/blob/{SHA}/Complexity/Init.lean", out)
        self.assertIn("www.cslib.io/cslib-frontier/CslibFrontier/Init.html) CslibFrontier.lean", out)
        self.assertIn("`CslibFrontier/`; nested Computability/Complexity/Classes", out)

    def test_urls_package_and_commands(self) -> None:
        text = textwrap.dedent("""\
            name = "complexitylib"
            git = "https://github.com/cslib-community/complexitylib"
            See https://github.com/SamuelSchlesinger/complexitylib-v1 and the complexitylib port.
            lake build @complexitylib Complexity:docs ComplexityTests
            lake -d docbuild update complexitylib
            rg -n 'x' Complexity ComplexityTests
            "name": "complexitylib",
            """)
        out = rewrite("README.md", text)
        self.assertEqual(out, textwrap.dedent("""\
            name = "cslib-frontier"
            git = "https://github.com/cslib-community/cslib-frontier"
            See https://github.com/SamuelSchlesinger/complexitylib-v1 and the complexitylib port.
            lake build @cslib-frontier CslibFrontier:docs CslibFrontierTests
            lake -d docbuild update cslib-frontier
            rg -n 'x' CslibFrontier CslibFrontierTests
            "name": "«cslib-frontier»",
            """))

    def test_excluded_strings_stay(self) -> None:
        bib = "title = {Algebraic circuit formalizations in Complexitylib, Complexity/X.lean}"
        self.assertEqual(rewrite("references.bib", bib), bib)
        scope = 'SCOPE = "cslib-community/complexitylib"\nCOMPLEXITYLIB_CACHE_URL = 1\n'
        self.assertEqual(rewrite("scripts/cache/publish.py", scope), scope)
        history = ("path.startswith('Complexity/') "
                   "# https://github.com/cslib-community/complexitylib/pull/1\n")
        self.assertEqual(rewrite("manual/development-history/data/x.py", history),
                         "path.startswith('Complexity/') "
                         "# https://github.com/cslib-community/cslib-frontier/pull/1\n")
        kept = f'x = "Complexity/"  # {r.PRAGMA}\ny = "Complexity/"\n'
        self.assertEqual(rewrite("scripts/x.py", kept),
                         f'x = "Complexity/"  # {r.PRAGMA}\ny = "CslibFrontier/"\n')

    def test_catalogue_entries_keep_their_namespaces(self) -> None:
        import json
        catalogue = {"entries": [
            {"id": "a", "module": "ComplexityAbstracts.AAbstract", "foundations": ["ComplexityAbstracts.F"]},
            {"id": "b", "module": "ComplexityAbstracts.BAbstract",
             "namespace": "ComplexityTests.Abstracts.BAbstract"}]}
        text = json.dumps(catalogue, indent=2, ensure_ascii=False) + "\n"
        paths = PATHS + ["abstracts/ComplexityAbstracts/AAbstract.lean",
                         "abstracts/ComplexityAbstracts/BAbstract.lean",
                         "abstracts/ComplexityAbstracts/F.lean"]
        rewriter = r.Rewriter(r.Inventory.from_paths(paths))
        out = rewriter.rewrite("abstracts/catalogue.json", text)
        self.assertEqual(json.loads(out)["entries"], [
            {"id": "a", "module": "CslibFrontierAbstracts.AAbstract",
             "namespace": "ComplexityAbstracts.AAbstract",
             "foundations": ["CslibFrontierAbstracts.F"]},
            {"id": "b", "module": "CslibFrontierAbstracts.BAbstract",
             "namespace": "ComplexityTests.Abstracts.BAbstract"}])
        self.assertEqual(rewriter.rewrite("abstracts/catalogue.json", out), out)

    def test_fixups_apply_once(self) -> None:
        text = "x\n/-- The free monad the program layer is built on. -/\nexample := @PFunctor.FreeM\n"
        once = rewrite("CslibFrontierTests/Smoke.lean", text)
        self.assertIn("A two-step program", once)
        self.assertEqual(rewrite("CslibFrontierTests/Smoke.lean", once), once)

    def test_tooling(self) -> None:
        text = textwrap.dedent(r"""
            ROOTS = ("Complexity", 'ComplexityTests')
            fixture = "public import Complexity.Fake\n"
            prefix = f"Complexity.{name}" + "Complexity\.lean" + r"\bComplexityAbstracts\b"
            ok = re.fullmatch(r"(?:Complexity|ComplexityAbstracts)(?:\.\w+)+", module)
            namespace = "ComplexityTests.Abstracts.Example"
            text = "# raw\nComplexity/Machines/Raw.lean\n"
            """)
        out = rewrite("scripts/x.py", text)
        self.assertEqual(out, textwrap.dedent(r"""
            ROOTS = ("CslibFrontier", 'CslibFrontierTests')
            fixture = "public import CslibFrontier.Fake\n"
            prefix = f"CslibFrontier.{name}" + "CslibFrontier\.lean" + r"\bCslibFrontierAbstracts\b"
            ok = re.fullmatch(r"(?:CslibFrontier|CslibFrontierAbstracts)(?:\.\w+)+", module)
            namespace = "ComplexityTests.Abstracts.Example"
            text = "# raw\nCslibFrontier/Machines/Raw.lean\n"
            """))

    def test_rewriting_is_idempotent(self) -> None:
        corpus = "\n".join(
            (LeanRules.test_imports_including_multiline_ones.__doc__ or "",
             "public import Complexity.Init", "`Complexity` modules", "Complexity/Init.lean",
             "https://github.com/cslib-community/complexitylib", "name = \"complexitylib\""))
        once = rewrite("AGENTS.md", corpus)
        self.assertEqual(rewrite("AGENTS.md", once), once)


def run(cwd: Path, *args: str) -> str:
    return subprocess.run(args, cwd=cwd, check=True, capture_output=True, text=True).stdout


LAKEFILE = textwrap.dedent("""\
    name = "complexitylib"
    defaultTargets = ["Complexity"]
    testDriver = "ComplexityTests"

    [[lean_lib]]
    name = "Complexity"

    [[lean_lib]]
    name = "ComplexityTests"
    roots = []
    globs = ["ComplexityTests.+"]
    """)


def lean(*imports: str, body: str = "") -> str:
    return "module\n\n" + "".join(f"public import {m}\n" for m in imports) + body


def aggregate(*modules: str) -> str:
    return r.MODULE_PREAMBLE + "".join(f"public import {m}\n" for m in modules)


class GitRepo(unittest.TestCase):
    """A temporary repository with an identity, so commits work anywhere."""

    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.repo = Path(self.tmp.name) / "repo"
        self.repo.mkdir()
        env = {"GIT_AUTHOR_NAME": "t", "GIT_AUTHOR_EMAIL": "t@example.invalid",
               "GIT_COMMITTER_NAME": "t", "GIT_COMMITTER_EMAIL": "t@example.invalid",
               "GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull}
        patcher = mock.patch.dict(os.environ, env)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.addCleanup(self.tmp.cleanup)
        self.git("init", "-q", "-b", "main")

    def git(self, *args: str) -> str:
        return run(self.repo, "git", *args).strip()

    def write(self, files: dict[str, str | None]) -> None:
        for path, text in files.items():
            target = self.repo / path
            if text is None:
                self.git("rm", "-q", path)
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
            self.git("add", path)

    def commit(self, message: str, files: dict[str, str | None] | None = None) -> str:
        self.write(files or {})
        self.git("commit", "-q", "--allow-empty", "-m", message)
        return self.git("rev-parse", "HEAD")

    def show(self, rev: str, path: str) -> str:
        return self.git("show", f"{rev}:{path}") + "\n"

    def base_files(self) -> dict[str, str]:
        return {
            "lakefile.toml": LAKEFILE,
            "AGENTS.md": "Rewrite `Complexity.` to `Cslib.` when upstreaming.\nOther line.\n",
            "Complexity.lean": aggregate("Complexity.A", "Complexity.B.C"),
            "Complexity/A.lean": lean("Cslib.Init", body="namespace Cslib\ndef a := 1\n"),
            "Complexity/B/C.lean": lean("Complexity.A", "Mathlib.Logic.Basic",
                                        body="/-! Uses `Complexity.A`. -/\n"),
            "ComplexityTests/T.lean": "import Complexity.A\n\nnamespace ComplexityTests.T\n",
        }


class ApplyMode(GitRepo):
    def test_apply_renames_rewrites_and_is_idempotent(self) -> None:
        self.commit("base", self.base_files())
        r.apply(self.repo, quiet=True)
        files = set(self.git("ls-files").split("\n"))
        self.assertEqual(files, {"lakefile.toml", "AGENTS.md", "CslibFrontier.lean",
                                 "CslibFrontier/A.lean", "CslibFrontier/B/C.lean",
                                 "CslibFrontierTests/T.lean"})
        self.assertEqual((self.repo / "CslibFrontier.lean").read_text(),
                         aggregate("CslibFrontier.A", "CslibFrontier.B.C"))
        self.assertEqual((self.repo / "CslibFrontier/B/C.lean").read_text(),
                         lean("CslibFrontier.A", "Mathlib.Logic.Basic",
                              body="/-! Uses `CslibFrontier.A`. -/\n"))
        self.assertEqual((self.repo / "CslibFrontierTests/T.lean").read_text(),
                         "import CslibFrontier.A\n\nnamespace ComplexityTests.T\n")
        self.assertIn('name = "cslib-frontier"', (self.repo / "lakefile.toml").read_text())
        self.assertIn('globs = ["CslibFrontierTests.+"]', (self.repo / "lakefile.toml").read_text())
        self.assertFalse((self.repo / "Complexity").exists())
        tree = self.git("write-tree")
        self.assertEqual(r.apply(self.repo, quiet=True), [])
        self.assertEqual(self.git("write-tree"), tree)

    def test_apply_merges_stragglers_into_an_existing_root(self) -> None:
        self.commit("base", self.base_files())
        r.apply(self.repo, quiet=True)
        self.commit("renamed")
        # A branch merge brought back a file at an old path.
        self.commit("straggler", {"Complexity/New.lean": lean("Complexity.A"),
                                  "Complexity.lean": aggregate("Complexity.New")})
        r.apply(self.repo, quiet=True)
        self.assertEqual((self.repo / "CslibFrontier/New.lean").read_text(),
                         lean("CslibFrontier.A"))
        self.assertEqual((self.repo / "CslibFrontier.lean").read_text(),
                         aggregate("CslibFrontier.A", "CslibFrontier.B.C", "CslibFrontier.New"))
        self.assertFalse((self.repo / "Complexity").exists())
        self.assertFalse((self.repo / "Complexity.lean").exists())


class RestackMode(GitRepo):
    def flag_day(self) -> tuple[str, str, str]:
        """Return (fork point, main before the rename, rename commit)."""
        fork = self.commit("base", self.base_files())
        pre = self.commit("main adds D", {
            "Complexity/D.lean": lean("Complexity.A"),
            "Complexity.lean": aggregate("Complexity.A", "Complexity.B.C", "Complexity.D")})
        r.apply(self.repo, quiet=True)
        # The rename commit also carries hand edits.
        self.write({"AGENTS.md": "Rewrite `CslibFrontier.` to `Cslib.` when upstreaming code.\n"
                                 "Other line.\n"})
        rename = self.commit("chore!: rename the module root")
        return fork, pre, rename

    def restack(self, branch: str, onto: str) -> int:
        self.git("checkout", "-q", branch)
        with mock.patch("sys.stdout"):
            return r.restack(self.repo, onto, "main", mk_all=False)

    def test_branch_edits_import_blocks_and_adds_modules(self) -> None:
        fork, pre, rename = self.flag_day()
        self.git("checkout", "-q", "-b", "pr", fork)
        self.commit("pr work", {
            "Complexity/B/C.lean": lean("Complexity.A", "Complexity.E", "Mathlib.Logic.Basic",
                                        body="/-! Uses `Complexity.A` and `Complexity.E`. -/\n"),
            "Complexity/E.lean": lean("Complexity.A", body="-- see Complexity/B/C.lean\n"),
            "Complexity.lean": aggregate("Complexity.A", "Complexity.B.C", "Complexity.E"),
            "ComplexityTests/E.lean": "import Complexity.E\n"})
        old = self.git("rev-parse", "HEAD")
        self.assertEqual(self.restack("pr", rename), 0)
        head = self.git("rev-parse", "HEAD")
        self.assertEqual(r.verify_carry(self.repo, old, head, None, "main"), (True, []))
        parents = self.git("rev-list", "--parents", "-n", "1", head).split()[1:]
        self.assertEqual(parents[1], rename)
        self.assertEqual(self.git("rev-list", "--parents", "-n", "1", parents[0]).split()[2], pre)
        self.assertEqual(self.show(head, "CslibFrontier/B/C.lean"), lean(
            "CslibFrontier.A", "CslibFrontier.E", "Mathlib.Logic.Basic",
            body="/-! Uses `CslibFrontier.A` and `CslibFrontier.E`. -/\n"))
        self.assertEqual(self.show(head, "CslibFrontier/E.lean"),
                         lean("CslibFrontier.A", body="-- see CslibFrontier/B/C.lean\n"))
        self.assertEqual(self.show(head, "CslibFrontierTests/E.lean"), "import CslibFrontier.E\n")
        self.assertEqual(self.show(head, "CslibFrontier.lean"), aggregate(
            "CslibFrontier.A", "CslibFrontier.B.C", "CslibFrontier.D", "CslibFrontier.E"))
        self.assertIn("`CslibFrontier.` to `Cslib.`", self.show(head, "AGENTS.md"))
        self.assertEqual(self.git("ls-files", "Complexity", "Complexity.lean"), "")
        self.assertEqual(self.git("status", "--porcelain", "--untracked-files=no"), "")
        # Running it again is a no-op.
        self.assertEqual(self.restack("pr", rename), 0)
        self.assertEqual(self.git("rev-parse", "HEAD"), head)
        # A change made while restacking is reported.
        edited = self.show(head, "CslibFrontier/E.lean").replace("-- see", "-- now see")
        changed = self.commit("edit", {"CslibFrontier/E.lean": edited})
        ok, report = r.verify_carry(self.repo, old, changed, None, "main")
        self.assertFalse(ok)
        self.assertIn("--- CslibFrontier/E.lean", report)
        self.assertIn("    +-- now see CslibFrontier/B/C.lean", report)

    def test_conflict_with_a_hand_edit_is_left_for_a_person(self) -> None:
        fork, _, rename = self.flag_day()
        self.git("checkout", "-q", "-b", "pr", fork)
        self.commit("pr edits AGENTS.md", {
            "AGENTS.md": "Rewrite `Complexity.` into `Cslib.` when upstreaming.\nOther line.\n"})
        self.assertEqual(self.restack("pr", rename), 4)
        self.assertEqual(r.unmerged(self.repo), ["AGENTS.md"])
        self.assertIn("<<<<<<<", (self.repo / "AGENTS.md").read_text())
        gitdir = Path(self.git("rev-parse", "--absolute-git-dir"))
        self.assertTrue((gitdir / "MERGE_HEAD").exists())

    def test_stacked_branch_onto_the_restacked_lower_branch(self) -> None:
        fork, _, rename = self.flag_day()
        self.git("checkout", "-q", "-b", "lower", fork)
        self.commit("lower adds E", {
            "Complexity/E.lean": lean("Complexity.A"),
            "Complexity.lean": aggregate("Complexity.A", "Complexity.B.C", "Complexity.E")})
        self.git("checkout", "-q", "-b", "upper")
        self.commit("upper adds F", {
            "Complexity/F.lean": lean("Complexity.E"),
            "Complexity.lean": aggregate("Complexity.A", "Complexity.B.C", "Complexity.E",
                                         "Complexity.F")})
        self.assertEqual(self.restack("lower", rename), 0)
        lower = self.git("rev-parse", "HEAD")
        upper = self.git("rev-parse", "upper")
        self.assertEqual(self.restack("upper", lower), 0)
        head = self.git("rev-parse", "HEAD")
        self.assertEqual(r.verify_carry(self.repo, upper, head, lower, "main"), (True, []))
        self.assertEqual(self.git("rev-list", "--parents", "-n", "1", head).split()[2], lower)
        self.assertEqual(self.show(head, "CslibFrontier/F.lean"), lean("CslibFrontier.E"))
        self.assertEqual(self.show(head, "CslibFrontier.lean"), aggregate(
            "CslibFrontier.A", "CslibFrontier.B.C", "CslibFrontier.D", "CslibFrontier.E",
            "CslibFrontier.F"))
        self.assertEqual(self.git("diff", "--name-only", lower, head), "CslibFrontier.lean\n"
                         "CslibFrontier/F.lean".strip())


class Batch(unittest.TestCase):
    def test_stacked_pull_requests_follow_their_base(self) -> None:
        import flagday_restack as fr
        infos = [{"number": n, "headRefName": head, "baseRefName": base, "isCrossRepository": False}
                 for n, head, base in ((3, "c", "b"), (1, "a", "main"), (2, "b", "a"),
                                       (4, "d", "main"))]
        self.assertEqual([i["number"] for i in fr.stack_order(infos)], [1, 2, 3, 4])
        fork = {"isCrossRepository": True, "maintainerCanModify": False}
        self.assertIsNone(fr.push_url("o/r", fork))
        self.assertEqual(fr.push_url("o/r", {"isCrossRepository": False}),
                         "https://github.com/o/r.git")

if __name__ == "__main__":
    unittest.main()
