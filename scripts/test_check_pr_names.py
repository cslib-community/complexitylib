"""Unit tests for scripts/check_pr_names.py."""

from __future__ import annotations

import io
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_pr_names as cpn  # noqa: E402

LIBRARY = """\
module
-- upstream: candidate

public import Complexity.Init

/-! # Demo

* `Cslib.Demo.ghostInDocstring` is only mentioned in this docstring.
-/

@[expose] public section

namespace Cslib.Demo

/-- A structure. -/
structure Pair (α : Type) extends Inhabited α where
  {width : ℕ}
  first : α
  second second' : α
  mk' ::

inductive Color where
  | red
  | green : Color

@[simp] theorem pair_first_eq {α : Type} (p : Pair α) : p.first = p.first := rfl

theorem foo_iff : True ↔ True := Iff.rfl

theorem hasCollision_of_le (hfA : True) (h_le : True) : True := hfA

noncomputable def nonceGame (n : ℕ) : ℕ := go n
where
  go (k : ℕ) : ℕ := k

private lemma hidden_helper : True := trivial

alias ⟨foo_mp, foo_mpr⟩ := foo_iff

section Inner
variable (padFn : ℕ → ℕ)
def secureGame : ℕ := 0
end Inner

end Cslib.Demo

namespace Finset
theorem prod_swap_demo : True := trivial
end Finset

theorem _root_.Nat.demo_root : True := trivial

theorem Iff.mp : True := trivial
"""


class CheckPrNamesTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        self.write("Complexity/Demo/Basic.lean", LIBRARY)

    def write(self, rel: str, content: str) -> None:
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")

    def check(self, text: str, base: str | None = None) -> dict[str, cpn.Finding]:
        report = cpn.check(text, self.root, core=False, base=base)
        return {f.token: f for f in report.findings}

    # --- Extraction ---------------------------------------------------------------------------

    def test_extracts_backticked_spans_outside_code_blocks_and_comments(self) -> None:
        text = ("Adds `foo` and ``bar `x` baz``.\n\n```lean\ntheorem `inFence` : True\n```\n"
                "<!-- `inComment` -->\nThen `foo` again and `qux`.")
        self.assertEqual(cpn.extract_tokens(text), ["foo", "bar `x` baz", "qux"])

    def test_candidates_skip_non_names(self) -> None:
        skipped = ["h k m + padFn 𝒩", "Complexity/Demo/Basic.lean", "CarterWegman.lean",
                   "0", "c69067ba", "simp", "ε", "trace", "hx", "_leaf_le", "pull_request",
                   "GITHUB_EVENT_PATH",
                   "PRF", "lake build", "mk_all --check", "lint-style", "native_decide", "theorem",
                   "-1", "@[simp]", "x.1", "Y", ".symm", "maxHeartbeats", "linter.style.longLine"]
        for token in skipped:
            with self.subTest(token=token):
                self.assertFalse(cpn.is_candidate(token))
        kept = ["nonceSignOracle", "IsDiffUniversal", "secureNonceMAC_of_isPRF", "Nodup",
                "List.Nodup", "Cslib.Demo.Pair.first", ".Nodup", "foo_iff.mp", "Nat.succ_le'",
                "_root_.Nat.demo_root", "card_inv_le"]
        for token in kept:
            with self.subTest(token=token):
                self.assertTrue(cpn.is_candidate(token))

    # --- Resolution ---------------------------------------------------------------------------

    def test_declarations_resolve_by_full_name_and_suffix(self) -> None:
        names = ["Cslib.Demo.pair_first_eq", "Demo.pair_first_eq", "pair_first_eq", "Pair",
                 "Cslib.Demo.Pair", "Cslib.Demo", "Demo", "Nat.demo_root", "secureGame",
                 "Cslib.Demo.secureGame", "hidden_helper", "foo_mp", "Demo.foo_mpr"]
        self.assertEqual(self.check(" ".join(f"`{n}`" for n in names)), {})

    def test_members_and_generated_names_resolve(self) -> None:
        names = ["Pair.first", "Pair.width", "Pair.second", "Pair.second'", "Pair.toInhabited",
                 "Pair.mk'",
                 "Color.red", "Color.green", "Color.rec", "Pair.ext_iff", "pair_first_eq.eq_1",
                 "nonceGame.go", "foo_iff.mp", "pair_first_eq_apply"]
        self.assertEqual(self.check(" ".join(f"`{n}`" for n in names)), {})

    def test_to_additive_translation_and_modules_resolve(self) -> None:
        names = ["Finset.sum_swap_demo", "Complexity.Demo.Basic", "Demo.Basic"]
        self.assertEqual(self.check(" ".join(f"`{n}`" for n in names)), {})

    def test_missing_names_are_reported_with_context(self) -> None:
        found = self.check("`nonceSignOracle`, `ghostInDocstring`, `Cslib.Wrong.secureGame`, "
                           "`Pair.third`, `padFn` and `nonceGame`.")
        self.assertEqual(list(found), ["nonceSignOracle", "ghostInDocstring",
                                       "Cslib.Wrong.secureGame", "Pair.third", "padFn"])
        self.assertEqual(found["nonceSignOracle"].mentions, 0)
        self.assertEqual(found["ghostInDocstring"].mentions, 1)
        self.assertEqual(found["Cslib.Wrong.secureGame"].declared_as, ["Cslib.Demo.secureGame"])
        self.assertEqual(found["padFn"].mentions, 1)
        self.assertIn("not found in any source file", found["nonceSignOracle"].note(None))
        self.assertIn("did you mean `Cslib.Demo.secureGame`",
                      found["Cslib.Wrong.secureGame"].note(None))

    def test_parent_projections_resolve_from_the_structure_file(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        self.write("Complexity/Parent.lean", "class Base (α : Type) where\n  base : α\n")
        self.write("Complexity/Child.lean",
                   "structure Pair (α : Type) extends Base α where\n  first : α\n")
        self.assertEqual(self.check("`Pair.toBase`"), {})
        self.assertEqual(list(self.check("`Pair.toNotAThing`")), ["Pair.toNotAThing"])

    def test_hypothesis_shaped_names(self) -> None:
        found = self.check("`hasCollision_of_le`, `hfA`, `h_le`, `hasNothing`, `hFoo`")
        self.assertEqual(list(found), ["hasNothing", "hFoo"])

    def test_generated_names_read_the_head_only_when_needed(self) -> None:
        self.assertEqual(cpn.search_words("Nat.succ_le_of_lt"), {"succ_le_of_lt"})
        self.assertEqual(cpn.head_words("Nat.succ_le_of_lt"), set())
        self.assertEqual(cpn.head_words("Pair.mk"), {"Pair"})
        self.assertEqual(cpn.head_words("foo_iff.mp"), {"foo_iff"})

    def test_python_script_names_resolve(self) -> None:
        self.write("scripts/check_demo.py", "def changed_files():\n    pass\n")
        found = self.check("`check_demo.changed_files`, `changed_files`, `check_demo.missing_fn`")
        self.assertEqual(list(found), ["check_demo.missing_fn"])

    def test_python_search_matches_ripgrep(self) -> None:
        text = "`Cslib.Demo.Pair.first` `nonceSignOracle` `Color.red`"
        with mock.patch.object(cpn.shutil, "which", return_value=None):
            fallback = self.check(text)
        self.assertEqual(list(fallback), ["nonceSignOracle"])
        self.assertEqual(list(self.check(text)), ["nonceSignOracle"])

    def test_comments_are_not_declarations(self) -> None:
        self.write("Complexity/Demo/Commented.lean",
                   "/- theorem inBlock : True := trivial -/\n-- theorem inLine : True := trivial\n"
                   "/-- doc\ntheorem inDoc : True := trivial -/\n"
                   "theorem real_decl : True := trivial\n")
        self.assertEqual(list(self.check("`inBlock` `inLine` `inDoc` `real_decl`")),
                         ["inBlock", "inLine", "inDoc"])

    # --- Base revision and CLI ----------------------------------------------------------------

    def git(self, *args: str) -> str:
        return subprocess.run(["git", *args], cwd=self.root, check=True, capture_output=True,
                              text=True).stdout.strip()

    def commit(self, *args: str) -> None:
        self.git("-c", "user.name=t", "-c", "user.email=t@t", "-c", "commit.gpgsign=false",
                 "commit", "-q", *args)

    def test_names_removed_by_the_change_are_recognized(self) -> None:
        self.git("init", "-q")
        self.commit("--allow-empty", "-m", "root")
        self.write("Complexity/Demo/Old.lean",
                   "namespace Cslib.Old\ntheorem old_lemma : True := trivial\nend Cslib.Old\n")
        self.git("add", ".")
        self.commit("-m", "base")
        base = self.git("rev-parse", "HEAD")
        (self.root / "Complexity/Demo/Old.lean").unlink()
        found = self.check("Removes `Cslib.Old.old_lemma`; adds `brandNew`.", base=base)
        self.assertTrue(found["Cslib.Old.old_lemma"].removed)
        self.assertFalse(found["brandNew"].removed)
        report = cpn.Report(["Cslib.Old.old_lemma", "brandNew"], list(found.values()), base)
        self.assertEqual([f.token for f in report.unexplained], ["brandNew"])

    def test_cli_event_payload_strict_and_github_summary(self) -> None:
        event = self.root / "event.json"
        event.write_text(json.dumps({"pull_request": {"body": "Adds `nonceSignOracle`."}}),
                         encoding="utf-8")
        summary = self.root / "summary.md"
        out = io.StringIO()
        with mock.patch.dict(cpn.os.environ, {"GITHUB_STEP_SUMMARY": str(summary)}), \
                redirect_stdout(out):
            code = cpn.main(["--event", str(event), "--github", "--no-core", "--root",
                             str(self.root), "--base", "HEAD"], root=self.root)
        self.assertEqual(code, 0)
        self.assertIn("::notice title=PR description names::", out.getvalue())
        self.assertIn("`nonceSignOracle`: not found in any source file", summary.read_text())
        with redirect_stdout(io.StringIO()):
            self.assertEqual(cpn.main(["--event", str(event), "--strict", "--no-core", "--root",
                                       str(self.root)], root=self.root), 1)
        clean = self.root / "clean.md"
        clean.write_text("Adds `Cslib.Demo.Pair`.", encoding="utf-8")
        out = io.StringIO()
        with redirect_stdout(out):
            self.assertEqual(cpn.main(["--file", str(clean), "--strict", "--no-core", "--root",
                                       str(self.root)], root=self.root), 0)
        self.assertIn("All 1 backticked names", out.getvalue())


if __name__ == "__main__":
    unittest.main()
