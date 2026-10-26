"""Unit tests for scripts/parallel_defs.py: the changed lines on a scratch repository, the selection
and reports on rows shaped like the output of `scripts/ParallelDefs.lean`, the driver's advisory
exits, and, when Lean is available, the reader on a compiled fixture module
(`CompiledFixtureTests`)."""

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
import parallel_defs as p  # noqa: E402

TIERS = p.parse_tiers("200:0.3,120:0.6")


def pair(a: str, b: str, size: int, sizes: tuple[int, int], am: str = "Complexity.New",
         bm: str = "Complexity.Old", private: bool = False, constants: tuple[str, ...] = ()
         ) -> dict:
    return {"pair": size, "a": a, "am": am, "al": 10, "b": b, "bm": bm, "bl": 20, "bp": private,
            "bx": False, "as": sizes[0], "bs": sizes[1], "c": list(constants)}


ALIAS = {"alias": "Cslib.MCSP.MCSPAt", "am": "Complexity.MCSP.Magnification", "al": 86,
         "b": "Cslib.GapMCSP.yesSet", "bm": "Complexity.MCSP.Basic", "bl": 40, "bp": False}


class ChangedLinesTests(unittest.TestCase):
    def test_added_ranges(self) -> None:
        diff = ("diff --git a/X.lean b/X.lean\n@@ -1,2 +0,0 @@\n-x\n-y\n@@ -3 +3 @@\n-a\n+b\n"
                "@@ -10,0 +11,2 @@\n+c\n+d\n@@ -20,2 +22,0 @@\n-e\n-f\n@@ -30,2 +31 @@\n")
        # A pure deletion (`+22,0`, `+0,0`) marks the lines around the place of the deleted text.
        self.assertEqual(p.added_ranges(diff), [(1, 1), (3, 3), (11, 12), (22, 23), (31, 31)])

    def test_requests(self) -> None:
        stdin = p.requests(["Complexity.A", "Complexity.B", "Complexity.C"],
                           {"Complexity/B.lean": None, "Complexity/C.lean": [(3, 4), (9, 9)]},
                           ["Cslib.thing"])
        self.assertEqual(stdin.splitlines(), ["env Complexity.A", "lines Complexity.B *",
                                              "lines Complexity.C 3-4,9-9", "decl Cslib.thing"])

    def test_changed_ranges_on_a_repository(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)

            def git(*args: str) -> None:
                subprocess.run(["git", *args], cwd=root, check=True, capture_output=True)

            def write(rel: str, text: str) -> None:
                (root / rel).parent.mkdir(parents=True, exist_ok=True)
                (root / rel).write_text(text)

            git("init", "-q")
            git("config", "user.name", "Fixture")
            git("config", "user.email", "fixture@example.invalid")
            # Review 6400055370: forced colour must not hide the hunk headers.
            git("config", "color.ui", "always")
            write("Complexity/Old.lean", "".join(f"line {i}\n" for i in range(1, 11)))
            write("Complexity/Gone.lean", "x\n")
            write("Complexity/Deleted.lean", "a\nb\nc\n")
            git("add", ".")
            git("commit", "-qm", "base")
            git("update-ref", "refs/remotes/origin/main", "HEAD")
            git("checkout", "-q", "-b", "side")
            lines = (root / "Complexity/Old.lean").read_text().splitlines(keepends=True)
            lines[3] = "changed 4\n"
            lines.insert(7, "inserted\n")
            write("Complexity/Old.lean", "".join(lines))
            write("Complexity/Deleted.lean", "a\nc\n")
            write("Complexity/New.lean", "def x := 1\n")
            write("ComplexityTests/New.lean", "example : True := trivial\n")
            (root / "Complexity/Gone.lean").unlink()
            # Untracked files count as added; deleted files and files outside `Complexity/` are
            # not examined, and a pure deletion marks the lines around it.
            self.assertEqual(p.changed_ranges(root, "origin/main"),
                             {"Complexity/New.lean": None,
                              "Complexity/Deleted.lean": [(1, 2)],
                              "Complexity/Old.lean": [(4, 4), (8, 8)]})

    def test_reader_output_ignores_other_lines(self) -> None:
        # Review 6400055370: an elaboration message from `lean --run` must not break parsing.
        stdout = ("ParallelDefs.lean:1:0: warning: something new in this toolchain\n"
                  '{"examined": 0, "modules": 1, "missing": []}\n')
        done = subprocess.CompletedProcess([], 0, stdout=stdout, stderr="")
        with mock.patch.object(p.subprocess, "run", return_value=done):
            self.assertEqual(p.run_reader(pathlib.Path("build"), "env A\n", 120, 4),
                             [{"examined": 0, "modules": 1, "missing": []}])


class SelectionTests(unittest.TestCase):
    def test_tiers(self) -> None:
        self.assertEqual(TIERS, [(200, 0.3), (120, 0.6)])
        for spec in ("", "200:2", "0:0.5", "x:0.3"):
            with self.assertRaises(ValueError, msg=spec):
                p.parse_tiers(spec)

    def test_pairs_reach_a_tier(self) -> None:
        rows = [ALIAS,
                pair("New.big", "Old.big", 549, (1147, 1155)),       # 48% of 1147: tier 1
                pair("New.copy", "Old.copy", 149, (230, 559)),       # 65% of 230: tier 2
                pair("New.diluted", "Old.diluted", 450, (2000, 1600)),   # 28%: no tier
                pair("New.small", "Old.small", 119, (119, 119)),     # below both sizes
                {"examined": 5, "modules": 3, "missing": []}]
        found = p.select(rows, TIERS, same_module=False)
        self.assertEqual([f.name for f in found],
                         ["Cslib.MCSP.MCSPAt", "New.big", "New.copy"])
        self.assertEqual(found[0].size, 0)
        self.assertEqual((found[1].path, found[1].line, found[1].other_path, found[1].other_line),
                         ("Complexity/New.lean", 10, "Complexity/Old.lean", 20))
        self.assertAlmostEqual(found[2].share, 149 / 230)

    def test_same_module_candidates_are_left_out_by_default(self) -> None:
        rows = [pair("A.x", "A.y", 300, (400, 400), am="Complexity.A", bm="Complexity.A"),
                dict(ALIAS, bm=ALIAS["am"])]
        self.assertEqual(p.select(rows, TIERS, same_module=False), [])
        self.assertEqual(len(p.select(rows, TIERS, same_module=True)), 2)

    def test_summary_constants_skip_plumbing(self) -> None:
        row = pair("N.x", "O.x", 300, (400, 400), constants=(
            "Finset.card", "Nat.instSemiring", "Monoid.toNPow", "HMul.hMul", "Nat",
            "Cslib.Thing", "Finset.card", "Polynomial.eval"))
        found = p.select([row], TIERS, same_module=False)
        self.assertEqual(found[0].constants, ("Finset.card", "Cslib.Thing", "Polynomial.eval"))


class ReportTests(unittest.TestCase):
    def setUp(self) -> None:
        self.found = p.select([ALIAS, pair("New.big", "Old.big", 549, (1147, 1155),
                                           private=True, constants=("Finset.card",))],
                              TIERS, same_module=False)

    def test_texts(self) -> None:
        self.assertEqual(self.found[0].text(),
                         "`Cslib.MCSP.MCSPAt` is `Cslib.GapMCSP.yesSet` "
                         "(Complexity/MCSP/Basic.lean:40) applied to its arguments: a second name "
                         "for an existing notion.")
        self.assertEqual(self.found[1].text(),
                         "`New.big` and `Old.big` (private) (Complexity/Old.lean:20) share a "
                         "549-node subterm, 48% of the smaller body, built from `Finset.card`.")

    def test_markdown(self) -> None:
        self.assertIn("No candidate parallel definitions among the 4 examined declarations.",
                      p.markdown([], 4, 10))
        text = p.markdown(self.found, 7, 1)
        self.assertIn("2 candidate(s) among the 7 examined declarations. The first 1 are listed.",
                      text)
        self.assertIn("- Complexity/MCSP/Magnification.lean:86: `Cslib.MCSP.MCSPAt` is", text)
        self.assertNotIn("New.big", text)

    def test_annotations_are_escaped(self) -> None:
        finding = p.Finding("a", "Complexity/x,y:z.lean", 3, "b%", "Complexity/O.lean", 4, 300,
                            0.5)
        [line] = p.annotations([finding], 10)
        self.assertTrue(line.startswith("::notice file=Complexity/x%2Cy%3Az.lean,line=3,"
                                        "title=Possible parallel definition::"))
        self.assertIn("`b%25`", line)
        self.assertEqual(len(p.annotations(self.found, 1)), 1)


class DriverTests(unittest.TestCase):
    """`main` is advisory: every path exits 0."""

    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.build = self.root / "build"
        self.summary = self.root / "summary.md"
        changed = mock.patch.object(p, "changed_ranges",
                                    lambda root, ref: {"Complexity/New.lean": None})
        changed.start()
        self.addCleanup(changed.stop)
        (self.root / "Complexity").mkdir()
        (self.root / "Complexity/New.lean").write_text("def x := 1\n")

    def run_main(self, *flags: str) -> tuple[int, str]:
        out = io.StringIO()
        with mock.patch.dict(os.environ, {"GITHUB_STEP_SUMMARY": str(self.summary)}), \
                contextlib.redirect_stdout(out):
            code = p.main(["--no-build-check", *flags], root=self.root, build_dir=self.build)
        return code, out.getvalue()

    def test_missing_build_outputs_skip(self) -> None:
        code, out = self.run_main("--github")
        self.assertEqual(code, 0)
        self.assertIn("skipped: no build outputs", out)
        self.assertIn("skipped: no build outputs", self.summary.read_text())
        (self.build / "Complexity").mkdir(parents=True)
        code, out = self.run_main()
        self.assertEqual(code, 0)
        self.assertIn("skipped: 1 changed module(s) are not built", out)

    def test_reader_failure_does_not_fail(self) -> None:
        (self.build / "Complexity").mkdir(parents=True)
        (self.build / "Complexity/New.olean").write_text("")
        with mock.patch.object(p, "run_reader", side_effect=RuntimeError("boom")):
            code, out = self.run_main()
        self.assertEqual(code, 0)
        self.assertIn("skipped: the tool failed (boom)", out)

    def test_findings_go_to_the_summary_and_annotations(self) -> None:
        (self.build / "Complexity").mkdir(parents=True)
        (self.build / "Complexity/New.olean").write_text("")
        rows = [ALIAS, {"examined": 3, "modules": 2, "missing": []}]
        with mock.patch.object(p, "run_reader", return_value=rows) as reader:
            code, out = self.run_main("--github")
        self.assertEqual(code, 0)
        self.assertEqual(reader.call_args.args[1].splitlines(), ["lines Complexity.New *"])
        self.assertEqual(reader.call_args.args[2:], (120, 4))
        self.assertIn("1 candidate(s) among the 3 examined declarations.", out)
        self.assertIn("::notice file=Complexity/MCSP/Magnification.lean,line=86,", out)
        self.assertIn("`Cslib.MCSP.MCSPAt` is `Cslib.GapMCSP.yesSet`", self.summary.read_text())

    def test_nothing_changed(self) -> None:
        with mock.patch.object(p, "changed_ranges", lambda root, ref: {}):
            code, out = self.run_main("--github")
        self.assertEqual(code, 0)
        self.assertIn("no `Complexity/` definitions added or modified", out)
        self.assertFalse(self.summary.exists())


# A compiled module for `CompiledFixtureTests`. Declarations from `-- new` on are examined.
FIXTURE = """module
public import Init
public section

def oldBounded (L : Nat → Prop) (count : Nat → Nat) : Prop :=
  ∀ n, (L n → count n * 3 ≥ 2 * (n + 1) * (n + 2) * (n + 3)) ∧
    (¬ L n → count n * 3 ≤ (n + 1) * (n + 2) * (n + 3))

structure OldReceiver where
  choose : Nat → List Bool → List Bool × (Bool × Bool) × List Bool
  guess : Nat → List Bool → List Bool → Bool

-- new

/-- The same notion for a promise problem: a parallel definition. -/
def newBounded (yes no : Nat → Prop) (count : Nat → Nat) : Prop :=
  ∀ n, (yes n → count n * 3 ≥ 2 * (n + 1) * (n + 2) * (n + 3)) ∧
    (no n → count n * 3 ≤ (n + 1) * (n + 2) * (n + 3))

/-- Reuse: mentions `oldBounded`, so it is not reported against it. -/
def wrapBounded (L : Nat → Prop) (count : Nat → Nat) : Prop :=
  oldBounded L count ∧ ∀ n, (L n → count n * 3 ≥ 2 * (n + 1) * (n + 2) * (n + 3))

abbrev aliasBounded (L : Nat → Prop) (count : Nat → Nat) : Prop := oldBounded L count

structure NewReceiver where
  choose : Nat → List Bool → List Bool × (Bool × Bool) × List Bool
  guess : Nat → List Bool → List Bool → Bool

private def hiddenBounded (L : Nat → Prop) (count : Nat → Nat) : Prop :=
  ∀ n, (L n → count n * 3 ≥ 2 * (n + 1) * (n + 2) * (n + 3)) ∧ True

instance : Inhabited OldReceiver := ⟨⟨fun _ _ => ([], (true, true), []), fun _ _ _ => true⟩⟩

@[deprecated oldBounded (since := "2026-10-25")]
def oldBounded' (L : Nat → Prop) (count : Nat → Nat) : Prop :=
  ∀ n, (L n → count n * 3 ≥ 2 * (n + 1) * (n + 2) * (n + 3)) ∧ False

end
"""


@unittest.skipUnless(shutil.which("lake") and (p.ROOT / ".lake/packages").is_dir(),
                     "needs Lean and the repository's packages (CI runs this after the build)")
class CompiledFixtureTests(unittest.TestCase):
    """`scripts/ParallelDefs.lean` on a compiled module."""

    @classmethod
    def setUpClass(cls) -> None:
        tmp = tempfile.TemporaryDirectory()
        cls.addClassCleanup(tmp.cleanup)
        root = pathlib.Path(tmp.name)
        build = root / "build"
        build.mkdir()
        (root / "ParallelFixture.lean").write_text(FIXTURE)
        subprocess.run(["lake", "env", "lean", f"--root={root}", "-o",
                        str(build / "ParallelFixture.olean"), str(root / "ParallelFixture.lean")],
                       cwd=p.ROOT, check=True, capture_output=True)
        first = FIXTURE.splitlines().index("-- new") + 1
        last = len(FIXTURE.splitlines())
        cls.build = build
        cls.rows = p.run_reader(build, f"lines ParallelFixture {first}-{last}\n", 20, 4)
        cls.pairs = {(r["a"], r["b"]): r for r in cls.rows if "pair" in r}

    def test_examined_declarations(self) -> None:
        # `newBounded`, `wrapBounded`, `aliasBounded` and `NewReceiver`, but not its fields, the
        # private definition, the instance or the deprecated definition.
        self.assertEqual(self.rows[-1], {"examined": 4, "modules": 1, "missing": []})

    def test_parallel_definition_and_structure(self) -> None:
        bounded = self.pairs[("newBounded", "oldBounded")]
        self.assertGreaterEqual(bounded["pair"], 40)
        self.assertGreaterEqual(bounded["pair"] / min(bounded["as"], bounded["bs"]), 0.3)
        self.assertFalse(bounded["bp"] or bounded["bx"])
        receiver = self.pairs[("NewReceiver", "OldReceiver")]
        self.assertEqual(receiver["pair"], receiver["as"])

    def test_reuse_is_not_reported(self) -> None:
        self.assertNotIn(("wrapBounded", "oldBounded"), self.pairs)
        self.assertNotIn(("aliasBounded", "oldBounded"), self.pairs)

    def test_private_counterparts_are_compared(self) -> None:
        self.assertTrue(self.pairs[("newBounded", "hiddenBounded")]["bp"])
        self.assertFalse([b for _, b in self.pairs if b == "oldBounded'"])

    def test_docstring_edits_are_not_examined(self) -> None:
        lines = FIXTURE.splitlines()
        doc = next(i for i, text in enumerate(lines, 1)
                   if text.startswith("/-- The same notion for a promise problem"))
        build = self.build

        def examined(spec: str) -> int:
            return p.run_reader(build, f"lines ParallelFixture {spec}\n", 20, 4)[-1]["examined"]

        self.assertEqual(examined(f"{doc}-{doc}"), 0)
        self.assertEqual(examined(f"{doc + 1}-{doc + 1}"), 1)

    def test_alias(self) -> None:
        lines = FIXTURE.splitlines()
        line = next(i for i, text in enumerate(lines, 1) if text.startswith("abbrev aliasBounded"))
        aliases = [r for r in self.rows if "alias" in r]
        self.assertEqual(aliases, [{"alias": "aliasBounded", "am": "ParallelFixture", "al": line,
                                    "b": "oldBounded", "bm": "ParallelFixture", "bl": 5,
                                    "bp": False}])


if __name__ == "__main__":
    unittest.main()
