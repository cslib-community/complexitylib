#!/usr/bin/env python3
"""Exercise live manual checks with isolated source/link drift and recovery cases."""
import json
import contextlib
import importlib.util
import io
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from build_operator_manual import main as build_main
from check_operator_manual import (MISNAMED_SOURCE_ANCHOR, STALE_SOURCE_ANCHOR, book_input_errors,
                                   check, comment_depths, fix_anchors, main as check_main,
                                   source_anchor_error)

DATA = Path(__file__).resolve().parents[1] / "manual/data"
with mock.patch.object(sys, "path", [str(DATA), *sys.path]):
    spec = importlib.util.spec_from_file_location("manual_book_builder", DATA / "build_manual.py")
    book = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(book)

# A Lean file whose lines exercise the source line anchor rule (#3991).
ANCHORED_SOURCE = """\
/- Copyright header. -/
module

/-! # Anchored declarations -/

namespace Anchored

/-- A documented definition. -/
def one : Nat := 1

@[simp] theorem one_eq : one = 1 := rfl

private noncomputable def two : Nat :=
  2

/-- Prose that happens to start a line with a keyword:
theorem in a docstring is not a declaration. -/
structure Pair where
  /-- A field docstring. -/
  fst : Nat
  snd : Nat

/- A commented-out block:
def hidden : Nat := 0 -/
example : "/-" = "/-" := rfl

def three : Nat := 3

end Anchored
"""


class ManualChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="cslib-frontier-manual-check-")
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.manual = self.repo / "manual"
        (self.manual / "workflows/data").mkdir(parents=True)
        (self.repo / "CslibFrontierTests").mkdir()
        self.client = self.repo / "CslibFrontierTests/Client.lean"
        self.fragment = "example : True := by\n  trivial"
        self.client.write_text("import Lean\n\n" + self.fragment + "\n")
        self.doc = self.manual / "workflows/first.md"
        self.doc.write_text(
            "# First client\n\n[Complete client](../../CslibFrontierTests/Client.lean)\n\n"
            "<!-- excerpt: first -->\n```lean\n" + self.fragment + "\n```\n")
        (self.manual / "README.md").write_text(
            "# Manual\n\n[First client](workflows/first.md#first-client)\n"
            "[Human agent driver](AGENT_OPERATORS.md)\n")
        (self.manual / "AGENT_OPERATORS.md").write_text("# Human direction of agents\n")
        self.manifest = self.manual / "workflows/data/test-excerpts.json"
        self.manifest.write_text(json.dumps([{
            "id": "first", "document": "workflows/first.md",
            "source_path": "CslibFrontierTests/Client.lean"}]))

    def errors(self):
        return check(self.repo)["errors"]

    def test_current_checkout_needs_no_git_or_historical_revision(self):
        self.assertEqual(self.errors(), [])

    def test_merge_conflicts_report_document_and_opening_line(self):
        original = self.doc.read_text()
        for body in (
                "<<<<<<< HEAD\nOld scope.\n=======\nNew scope.\n>>>>>>> feature\n",
                "<<<<<<< HEAD\n[paper]: https://example.org/old\n=======\n"
                "[paper]: https://example.org/new\n>>>>>>> feature\n",
                "<<<<<<< ours\nOurs.\n||||||| base\nOriginal.\n=======\nTheirs.\n>>>>>>> theirs\n",
                "  <<<<<<<<<\nOurs.\n=========\nTheirs.\n  >>>>>>>>>\n",
                "<<<<<<< HEAD\nUnfinished resolution.\n"):
            with self.subTest(body=body):
                self.doc.write_text(original + "\n" + body)
                line = len(original.splitlines()) + 2
                self.assertIn(f"workflows/first.md: Line {line}: unresolved Git merge conflict",
                              self.errors())

    def test_pdf_entry_point_rejects_conflicts_before_rendering(self):
        self.doc.write_text(self.doc.read_text() +
                            "\n<<<<<<< HEAD\nOld.\n=======\nNew.\n>>>>>>> feature\n")
        for option in ("--tex-only", "--agent-manual"):
            with self.subTest(option=option), mock.patch("build_operator_manual.ROOT", self.repo), \
                    mock.patch.object(sys, "argv", ["build_operator_manual.py", option]), \
                    mock.patch("build_operator_manual.subprocess.run") as render, \
                    contextlib.redirect_stderr(io.StringIO()) as diagnostics:
                self.assertEqual(build_main(), 1)
                self.assertIn("workflows/first.md: Line", diagnostics.getvalue())
                self.assertIn("unresolved Git merge conflict", diagnostics.getvalue())
                render.assert_not_called()

    def test_source_relocation_is_allowed(self):
        self.client.write_text("-- inserted before the original source\n\n" + self.client.read_text())
        result = check(self.repo)
        self.assertEqual(result["errors"], [])
        self.assertEqual(result["excerpts"][0]["start_line"], 5)

    def test_source_edit_fails_and_repair_passes(self):
        original = self.client.read_text()
        self.client.write_text(original.replace("trivial", "exact True.intro"))
        self.assertTrue(any("found 0" in e for e in self.errors()))
        self.client.write_text(original)
        self.assertEqual(self.errors(), [])

    def test_duplicate_source_match_is_ambiguous(self):
        self.client.write_text(self.client.read_text() + "\n" + self.fragment + "\n")
        self.assertTrue(any("found 2" in e for e in self.errors()))

    def test_missing_link_is_reported(self):
        self.doc.write_text(self.doc.read_text() + "\n[Missing](missing.md)\n")
        self.assertTrue(any("missing local link" in e for e in self.errors()))

    def test_missing_anchor_is_reported(self):
        readme = self.manual / "README.md"
        readme.write_text(readme.read_text().replace("#first-client", "#gone"))
        self.assertTrue(any("missing Markdown anchor" in e for e in self.errors()))

    def test_undefined_reference_is_reported(self):
        self.doc.write_text(self.doc.read_text() + "\n[Read it][undefined]\n")
        self.assertTrue(any("undefined reference" in e for e in self.errors()))

    def test_unregistered_lean_block_is_reported(self):
        self.doc.write_text(self.doc.read_text() + "\n```lean\nexample : True := .intro\n```\n")
        self.assertTrue(any("unregistered Lean block" in e for e in self.errors()))

    def test_context_requires_link_to_complete_client(self):
        self.doc.write_text(self.doc.read_text().replace(
            "[Complete client](../../CslibFrontierTests/Client.lean)", "Complete client omitted"))
        self.assertTrue(any("link the complete source client" in e for e in self.errors()))

    def test_generated_documents_are_not_inputs(self):
        for directory in ("_build", "_generated"):
            (self.manual / directory).mkdir()
            (self.manual / directory / "scratch.md").write_text("[Missing](missing.md)\n")
        self.assertEqual(self.errors(), [])

    def test_orphan_page_is_reported(self):
        (self.manual / "lost.md").write_text("# Unreachable instructions\n")
        self.assertTrue(any("Unreachable manual page" in e for e in self.errors()))

    def test_paths_cannot_escape_checkout(self):
        self.doc.write_text(self.doc.read_text() + "\n[Outside](../../../outside.md)\n")
        self.assertTrue(any("escapes repository" in e for e in self.errors()))

    def test_manual_without_builder_skips_chapter_lists(self):
        self.assertFalse(check(self.repo)["book_inputs_checked"])

    def anchor_link(self, line):
        (self.repo / "CslibFrontierTests/Anchored.lean").write_text(ANCHORED_SOURCE)
        url = f"../../CslibFrontierTests/Anchored.lean#L{line}"
        self.doc.write_text(self.doc.read_text() + f"\n[one]({url})\n")
        return url

    def test_drifted_source_line_anchor_fails_and_repoint_passes(self):
        good = ANCHORED_SOURCE.splitlines().index("def one : Nat := 1") + 1
        url = self.anchor_link(good + 1)
        self.assertEqual(self.errors(), [f"workflows/first.md: {STALE_SOURCE_ANCHOR}: {url}"])
        self.doc.write_text(self.doc.read_text().replace(f"#L{good + 1})", f"#L{good})"))
        self.assertEqual(self.errors(), [])

    def test_stale_anchor_allowlist_covers_only_listed_lines(self):
        line = ANCHORED_SOURCE.splitlines().index("  2") + 1
        self.anchor_link(line)
        entry, unused = ("CslibFrontierTests/Anchored.lean", line), ("CslibFrontierTests/Other.lean", 3)
        with mock.patch("check_operator_manual.STALE_SOURCE_ANCHORS", {entry, unused}):
            result = check(self.repo)
            self.assertEqual(result["errors"], [])
            self.assertEqual(result["allowed_stale_source_anchors"], [f"{entry[0]}#L{line}"])
            self.assertEqual(result["unused_stale_source_anchor_entries"], [f"{unused[0]}#L3"])
            self.anchor_link(line - 2)
            self.assertTrue(any(STALE_SOURCE_ANCHOR in e for e in self.errors()))
            self.anchor_link(10_000)
            self.assertTrue(any("out of bounds" in e for e in self.errors()))

    def test_link_text_must_name_the_anchored_declaration(self):
        (self.repo / "CslibFrontierTests/Anchored.lean").write_text(ANCHORED_SOURCE)
        lines = ANCHORED_SOURCE.splitlines()
        at = {text: lines.index(text) + 1 for text in (
            "/-- A documented definition. -/", "def one : Nat := 1",
            "@[simp] theorem one_eq : one = 1 := rfl", "private noncomputable def two : Nat :=",
            "/-- Prose that happens to start a line with a keyword:", "def three : Nat := 3",
            "namespace Anchored", 'example : "/-" = "/-" := rfl')}
        url = "../../CslibFrontierTests/Anchored.lean#L{}"
        passing = [
            ("one", at["/-- A documented definition. -/"]),  # docstring opener
            ("Anchored.one", at["def one : Nat := 1"]),  # text more qualified than the name
            ("`one_eq`", at["@[simp] theorem one_eq : one = 1 := rfl"]),  # attribute, code span
            ("Anchored.two", at["private noncomputable def two : Nat :="]),  # modifiers
            ("Pair", at["/-- Prose that happens to start a line with a keyword:"]),
            ("Anchored.lean", at["def one : Nat := 1"]),  # a file, not a declaration
            ("CslibFrontierTests.Anchored", at["def one : Nat := 1"]),  # the module
            ("here", at["def one : Nat := 1"]),  # prose names no declaration of the file
            ("hidden", at["def three : Nat := 3"]),  # only commented out in this file
            ("moved", at["def one : Nat := 1"]),  # declared in another file
            ("three", f"{at['namespace Anchored']}-L{at['def three : Nat := 3']}"),  # range
        ]
        self.doc.write_text(self.doc.read_text() + "".join(
            f"\n[{text}]({url.format(line)})\n" for text, line in passing))
        self.assertEqual(self.errors(), [])
        wrong = [url.format(at["@[simp] theorem one_eq : one = 1 := rfl"]),
                 url.format(at['example : "/-" = "/-" := rfl']),
                 url.format(f"{at['namespace Anchored']}-L{at['def one : Nat := 1'] - 2}")]
        self.doc.write_text(self.doc.read_text()
                            + "".join(f"\n[Anchored.one]({u})\n" for u in wrong))
        declared = f"declared at L{at['/-- A documented definition. -/']}"
        self.assertEqual(self.errors(), [
            f"workflows/first.md: {MISNAMED_SOURCE_ANCHOR} ({declared}): {u}" for u in wrong])

    def test_exact_declaration_name_takes_precedence(self):
        source = "module\n\ndef toX : Nat := 0\n\ntheorem Complete.toX : True := trivial\n"
        (self.repo / "CslibFrontierTests/Exact.lean").write_text(source)
        url = "../../CslibFrontierTests/Exact.lean#L{}"
        self.doc.write_text(self.doc.read_text()
                            + f"\n[toX]({url.format(3)}) [Ns.Complete.toX]({url.format(5)})\n")
        self.assertEqual(self.errors(), [])
        self.doc.write_text(self.doc.read_text() + f"\n[Complete.toX]({url.format(3)})\n")
        self.assertEqual(self.errors(), [
            f"workflows/first.md: {MISNAMED_SOURCE_ANCHOR} (declared at L5): {url.format(3)}"])

    def test_name_check_reads_links_as_the_link_scanner_does(self):
        (self.repo / "CslibFrontierTests/Anchored.lean").write_text(ANCHORED_SOURCE)
        line = ANCHORED_SOURCE.splitlines().index("def three : Nat := 3") + 1
        url = f"../../CslibFrontierTests/Anchored.lean#L{line}"
        # Code showing a link is not a link.
        self.doc.write_text(self.doc.read_text()
                            + f"\nWrite `[one]({url})` or ``[`one`]({url})``.\n")
        self.assertEqual(self.errors(), [])
        # A code-formatted label, an angle-bracketed URL and a titled link are links.
        wrong = [f"[`one`]({url})", f"[one](<{url}>)", f'[one]({url} "title")']
        self.doc.write_text(self.doc.read_text() + "".join(f"\n{link}\n" for link in wrong))
        declared = "declared at L{}".format(ANCHORED_SOURCE.splitlines().index(
            "/-- A documented definition. -/") + 1)
        self.assertEqual(self.errors(), [
            f"workflows/first.md: {MISNAMED_SOURCE_ANCHOR} ({declared}): {url}"] * len(wrong))

    def test_header_spans_line_comments(self):
        source = "module\n\n/-- Doc. -/\n-- A remark.\n@[simp]\ndef size : Nat := 0\n"
        (self.repo / "CslibFrontierTests/Size.lean").write_text(source)
        url = "../../CslibFrontierTests/Size.lean#L{}"
        self.doc.write_text(self.doc.read_text() + "".join(
            f"\n[size]({url.format(line)})\n" for line in (3, 5, 6)))
        self.assertEqual(self.errors(), [])

    def test_qualified_match_prefers_the_longest_declared_name(self):
        source = "module\n\ndef add : Nat := 0\n\ntheorem Valid.add : True := trivial\n"
        (self.repo / "CslibFrontierTests/Corr.lean").write_text(source)
        url = "../../CslibFrontierTests/Corr.lean#L{}"
        self.doc.write_text(self.doc.read_text()
                            + f"\n[Corr.Valid.add]({url.format(5)}) [Ns.add]({url.format(3)})\n")
        self.assertEqual(self.errors(), [])
        self.doc.write_text(self.doc.read_text() + f"\n[Corr.Valid.add]({url.format(3)})\n")
        self.assertEqual(self.errors(), [
            f"workflows/first.md: {MISNAMED_SOURCE_ANCHOR} (declared at L5): {url.format(3)}"])

    def test_declaration_named_like_its_file_is_checked(self):
        source = "module\n\ndef helper : Nat := 0\n\nstructure Foo where\n  x : Nat\n"
        (self.repo / "CslibFrontierTests/Foo.lean").write_text(source)
        url = "../../CslibFrontierTests/Foo.lean#L{}"
        # The module's full name is not a declaration, so it may link anywhere.
        self.doc.write_text(self.doc.read_text() + f"\n[Foo]({url.format(5)}) "
                            f"[CslibFrontierTests.Foo]({url.format(3)})\n")
        self.assertEqual(self.errors(), [])
        self.doc.write_text(self.doc.read_text() + f"\n[Foo]({url.format(3)})\n")
        self.assertEqual(self.errors(), [
            f"workflows/first.md: {MISNAMED_SOURCE_ANCHOR} (declared at L5): {url.format(3)}"])

    def test_misnamed_check_leaves_stale_anchors_to_the_start_check(self):
        lines = ANCHORED_SOURCE.splitlines()
        url = self.anchor_link(lines.index("theorem in a docstring is not a declaration. -/") + 1)
        self.assertEqual(self.errors(), [f"workflows/first.md: {STALE_SOURCE_ANCHOR}: {url}"])
        # A listed anchor that starts another declaration is tolerated and counts as used.
        self.doc.write_text(self.doc.read_text().replace(f"[one]({url})", ""))
        line = lines.index("def three : Nat := 3") + 1
        self.anchor_link(line)
        self.assertTrue(self.errors())
        entry = ("CslibFrontierTests/Anchored.lean", line)
        with mock.patch("check_operator_manual.STALE_SOURCE_ANCHORS", {entry}):
            result = check(self.repo)
            self.assertEqual(result["errors"], [])
            self.assertEqual(result["allowed_stale_source_anchors"], [f"{entry[0]}#L{line}"])
            self.assertEqual(result["unused_stale_source_anchor_entries"], [])

    def test_fix_anchors_repoints_drifted_named_links_and_preserves_syntax(self):
        (self.repo / "CslibFrontierTests/Anchored.lean").write_text(ANCHORED_SOURCE)
        lines = ANCHORED_SOURCE.splitlines()
        at = {text: lines.index(text) + 1 for text in (
            "/-- A documented definition. -/", "@[simp] theorem one_eq : one = 1 := rfl",
            "private noncomputable def two : Nat :=", "  2",
            "/-- Prose that happens to start a line with a keyword:",
            "theorem in a docstring is not a declaration. -/", "def three : Nat := 3")}
        url = "../../CslibFrontierTests/Anchored.lean#L{}"
        doc_lines = [
            f"[Anchored.one]({url.format(at['def three : Nat := 3'])})",
            f"[Pair]({url.format(at['theorem in a docstring is not a declaration. -/'])})",
            f"[`one_eq`]({url.format(9999)})",
            f"[one](<{url.format(at['  2'])}>) and [two]({url.format(at['  2'])} \"sec\")",
        ]
        self.doc.write_text(self.doc.read_text() + "\n" + "\n".join(doc_lines) + "\n")
        self.assertEqual(len(self.errors()), 5)
        fixes = fix_anchors(self.repo)
        self.assertEqual([f["new"] for f in fixes], [
            f"L{at['/-- A documented definition. -/']}",
            f"L{at['/-- Prose that happens to start a line with a keyword:']}",
            f"L{at['@[simp] theorem one_eq : one = 1 := rfl']}",
            f"L{at['/-- A documented definition. -/']}",
            f"L{at['private noncomputable def two : Nat :=']}",
        ])
        self.assertEqual(self.errors(), [])
        text = self.doc.read_text()
        self.assertIn(f"[one](<{url.format(at['/-- A documented definition. -/'])}>)", text)
        self.assertIn(f"[two]({url.format(at['private noncomputable def two : Nat :='])} \"sec\")",
                      text)
        self.assertEqual(fix_anchors(self.repo), [])
        # Exercise the CLI `--fix-anchors` flag end-to-end on another drifted anchor.
        self.doc.write_text(text + f"\n[three]({url.format(at['  2'])})\n")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = check_main(["--repo", str(self.repo), "--fix-anchors"])
        self.assertEqual(code, 0)
        payload = json.loads(out.getvalue())
        self.assertEqual(payload["errors"], [])
        self.assertEqual(len(payload["fixed_anchors"]), 1)
        self.assertEqual(payload["fixed_anchors"][0]["new"], f"L{at['def three : Nat := 3']}")

    def test_fix_anchors_skips_valid_special_ambiguous_and_allowlisted_links(self):
        source = (
            "module\n\n"
            "/-- Doc. -/\ndef one : Nat := 1\n\n"
            "namespace A\ndef dup : Nat := 0\nend A\n\n"
            "namespace B\ndef dup : Nat := 1\nend B\n"
        )
        (self.repo / "CslibFrontierTests/Dup.lean").write_text(source)
        url = "../../CslibFrontierTests/Dup.lean#L{}"
        body = (
            "\n"
            f"[one]({url.format(4)}) "        # valid keyword line inside (3, 4) header
            f"[one]({url.format(1)}) "        # whole-file anchor #L1
            f"[one]({url.format(4)}-L{12}) "  # range anchor
            f"`[one]({url.format(999)})`\n"   # inline code span
            "```markdown\n"
            f"[one]({url.format(999)})\n"     # fenced block
            "```\n"
            "[one](https://example.org/Dup.lean#L999)\n"
            f"[prose label]({url.format(5)})\n"  # unnamed drifted link (blank line 5)
            f"[dup]({url.format(4)})\n"          # ambiguous multiple declarations (points to one)
            f"[one]({url.format(2)})\n"          # allowlisted stale anchor below
        )
        before = self.doc.read_text() + body
        self.doc.write_text(before)
        entry = ("CslibFrontierTests/Dup.lean", 2)
        with mock.patch("check_operator_manual.STALE_SOURCE_ANCHORS", {entry}):
            self.assertEqual(fix_anchors(self.repo), [])
            self.assertEqual(self.doc.read_text(), before)
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                code = check_main(["--repo", str(self.repo), "--fix-anchors"])
            self.assertEqual(code, 1)
            payload = json.loads(out.getvalue())
            self.assertEqual(payload["fixed_anchors"], [])
            self.assertEqual(len(payload["errors"]), 2)


class SourceLineAnchors(unittest.TestCase):
    """A relative `.lean#L` link must start a declaration, attribute, docstring or section."""

    def setUp(self):
        self.lines = ANCHORED_SOURCE.splitlines()

    def problem(self, fragment):
        return source_anchor_error(fragment, self.lines)

    def line_of(self, text):
        return self.lines.index(text) + 1

    def test_declaration_attribute_and_docstring_starts_pass(self):
        for text in ("/-- A documented definition. -/", "def one : Nat := 1",
                     "@[simp] theorem one_eq : one = 1 := rfl", "private noncomputable def two : Nat :=",
                     "structure Pair where", 'example : "/-" = "/-" := rfl',
                     "def three : Nat := 3"):
            with self.subTest(text=text):
                self.assertIsNone(self.problem(f"L{self.line_of(text)}"))

    def test_drifted_anchor_fails(self):
        for text in ("  2", "", "end Anchored", "theorem in a docstring is not a declaration. -/",
                     "  /-- A field docstring. -/", "def hidden : Nat := 0 -/"):
            with self.subTest(text=text):
                self.assertEqual(self.problem(f"L{self.line_of(text)}"), STALE_SOURCE_ANCHOR)

    def test_whole_file_link_passes(self):
        self.assertIsNone(self.problem("L1"))
        self.assertIsNone(self.problem(f"L1-L{len(self.lines)}"))

    def test_range_may_start_at_a_section_but_a_single_line_may_not(self):
        for text in ("/-! # Anchored declarations -/", "namespace Anchored"):
            with self.subTest(text=text):
                start = self.line_of(text)
                self.assertIsNone(self.problem(f"L{start}-L{len(self.lines)}"))
                self.assertEqual(self.problem(f"L{start}"), STALE_SOURCE_ANCHOR)
        self.assertEqual(self.problem(f"L{self.line_of('  2')}-L{len(self.lines)}"),
                         STALE_SOURCE_ANCHOR)

    def test_out_of_bounds_is_reported_first(self):
        self.assertEqual(self.problem(f"L{len(self.lines) + 1}"), "source line anchor out of bounds")
        self.assertEqual(self.problem(f"L3-L{len(self.lines) + 1}"), "source line anchor out of bounds")

    def test_comment_depth_ignores_strings_and_line_comments(self):
        depths = comment_depths(['def s := "/-"  -- /- not a comment', "/- outer /- inner -/",
                                 "still inside -/", "def t := 0"])
        self.assertEqual(depths, [0, 0, 1, 0])


class BookRegistration(unittest.TestCase):
    """Run the chapter-list check with the real builder on placeholder copies of its pages."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="cslib-frontier-manual-registration-")
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.manual = self.repo / "manual"
        (self.manual / "data").mkdir(parents=True)
        for name in book.CONVERTER_INPUTS:
            shutil.copy(DATA.parent / name, self.manual / name)
        for name in [*book.FILES, "AGENT_OPERATORS.md"]:
            (self.manual / name).parent.mkdir(parents=True, exist_ok=True)
            (self.manual / name).write_text("# Placeholder chapter\n")

    def errors(self):
        return book_input_errors(self.repo, self.manual)

    def test_registered_pages_pass(self):
        self.assertEqual(self.errors(), [])

    def test_unregistered_page_names_the_list_to_edit(self):
        (self.manual / "machines-and-classes/unregistered.md").write_text("# Outside the book\n")
        [error] = self.errors()
        self.assertRegex(error, r"missing=\['machines-and-classes/unregistered\.md'\]")
        self.assertIn("ORDER in manual/data/build_latex.py", error)

    def test_deleted_page_must_leave_the_chapter_list(self):
        page = book.REFERENCE[-1]
        (self.manual / page).unlink()
        [error] = self.errors()
        self.assertIn(f"extra=['{page}']", error)

    def test_checked_manual_uses_its_own_chapter_lists(self):
        page = book.REFERENCE[-1]
        source = self.manual / "data/build_latex.py"
        entry = repr(Path(page).stem)
        self.assertEqual(source.read_text().count(entry), 1)
        source.write_text(source.read_text().replace(entry, ""))
        path, cached = list(sys.path), sys.modules.get("build_latex")
        [error] = self.errors()
        self.assertIn(f"missing=['{page}']", error)
        self.assertEqual(sys.path, path)
        self.assertIs(sys.modules.get("build_latex"), cached)

    def test_full_check_reports_unregistered_page(self):
        (self.manual / "workflows/unregistered.md").write_text("# Outside the book\n")
        result = check(self.repo)
        self.assertTrue(result["book_inputs_checked"])
        self.assertTrue(any("missing=['workflows/unregistered.md']" in e for e in result["errors"]))


class BookInputs(unittest.TestCase):
    """Exercise the actual assembler, replacing only Git and publishing-tool rendering."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="cslib-frontier-manual-book-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "manual"
        (self.root / "data").mkdir(parents=True)
        for name in book.CONVERTER_INPUTS:
            (self.root / name).write_text("# fixture rendering input\n")
        (self.root / "README.md").write_text("# A complete first chapter\n")
        (self.root / "AGENT_OPERATORS.md").write_text("# A short manual for the human driver\n")
        (self.root / "history").mkdir()
        (self.root / "history/paper-plan.md").write_text("# Archived editorial plan\n")
        self.sources = self.root / "sources.md"
        self.sources.write_text('# Sources\n\n<a id="example"></a>\n## example\n\nCanonical citation.\n')
        self.output = self.root / "_build"

    def build(self, files=None, agent=False):
        files = (book.AGENT_FILES if agent else ["README.md"]) if files is None else files
        def ast(text):
            return {"blocks": [{"t": "Para", "c": [{"t": "Str", "c": text}]}]}
        with contextlib.ExitStack() as stack:
            for name, value in {"ROOT": self.root, "REPO": self.root.parent, "FILES": files,
                                "WORKFLOWS": ["README.md"], "REFERENCE": ["unused-reference.md"],
                                "HISTORY": ["unused-history.md"], "APPENDICES": ["unused-appendix.md"]}.items():
                stack.enter_context(mock.patch.object(book, name, value))
            stack.enter_context(mock.patch.object(book, "git", return_value="test-revision"))
            stack.enter_context(mock.patch.object(book, "preamble", return_value="\\begin{document}\n"))
            stack.enter_context(mock.patch.object(book, "write", side_effect=lambda obj: json.dumps(obj) + "\n"))
            stack.enter_context(mock.patch.object(book.base, "ast_for", side_effect=ast))
            stack.enter_context(mock.patch.object(book.base, "run", return_value=""))
            stack.enter_context(mock.patch.object(book.base, "transform", side_effect=lambda node, *a, **k: node))
            stack.enter_context(mock.patch.object(book.base, "FILES", files))
            stack.enter_context(mock.patch.object(book.base, "OUTPUT_ROOT", self.output))
            argv = ["build_manual.py", "--tex-only", "--output-dir", str(self.output)]
            if agent:
                argv.append("--agent-manual")
            stack.enter_context(mock.patch.object(sys, "argv", argv))
            stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
            book.main()
        return (self.output / ((book.AGENT_STEM if agent else book.STEM) + ".tex")).read_text()

    def test_canonical_bibliography_edits_reach_output_without_generated_data(self):
        first = self.build()
        self.assertIn("Canonical citation.", first)
        self.assertFalse((self.root / "_generated").exists())
        self.sources.write_text(self.sources.read_text().replace("Canonical citation.", "Revised canonical citation."))
        second = self.build()
        self.assertIn("Revised canonical citation.", second)

    def test_missing_chapter_cannot_silently_disappear(self):
        (self.root / "second.md").write_text("# Another maintained chapter\n")
        with self.assertRaisesRegex(ValueError, "missing=.*second.md"):
            self.build()

    def test_removed_input_fails_even_when_other_inputs_exist(self):
        with self.assertRaisesRegex(ValueError, "missing=.*README.md"):
            self.build(files=[])

    def test_archived_plan_and_bibliography_are_explicit_exclusions(self):
        book.validate_inputs(self.root, ["README.md"])
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            book.validate_inputs(self.root, ["README.md", "README.md"])

    def test_existing_build_rejects_bibliography_drift(self):
        self.build()
        self.sources.write_text(self.sources.read_text().replace("Canonical citation.", "Changed citation."))
        with self.assertRaisesRegex(ValueError, "Stale bibliography"):
            book.validate_manifest(self.root, self.output, ["README.md"])

    def test_existing_build_rejects_chapter_drift(self):
        self.build()
        (self.root / "README.md").write_text("# Changed instructions\n")
        with self.assertRaisesRegex(ValueError, "Stale chapter"):
            book.validate_manifest(self.root, self.output, ["README.md"])

    def test_existing_build_rejects_missing_manifest_entry(self):
        self.build()
        path = self.output / "manual-source-manifest.json"
        manifest = json.loads(path.read_text())
        manifest["chapter_inputs"].pop("README.md")
        path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, "Manifest chapter inputs"):
            book.validate_manifest(self.root, self.output, ["README.md"])

    def test_existing_build_rejects_changed_latex(self):
        self.build()
        (self.output / (book.STEM + ".tex")).write_text("Altered generated file")
        with self.assertRaisesRegex(ValueError, "Stale generated LaTeX"):
            book.validate_manifest(self.root, self.output, ["README.md"])

    def test_tex_only_cannot_validate_an_older_pdf(self):
        self.build()
        (self.output / (book.STEM + ".pdf")).write_bytes(b"old PDF from another build")
        self.build()  # Regenerating TeX is allowed; the old PDF is not certified by that action.
        with self.assertRaisesRegex(ValueError, "PDF is missing, changed or not from this full build"):
            book.validate_manifest(self.root, self.output, ["README.md"])

    def test_generated_evidence_does_not_change_book_inputs(self):
        self.build()
        generated = self.root / "_generated"
        generated.mkdir()
        (generated / "unreviewed.md").write_text("# Not a book chapter\n")
        (generated / "history.svg").write_text("<svg/>\n")
        book.validate_manifest(self.root, self.output, ["README.md"])

    def test_existing_build_rejects_converter_drift(self):
        self.build()
        (self.root / book.CONVERTER_INPUTS[1]).write_text("# changed rendering behavior\n")
        with self.assertRaisesRegex(ValueError, "Stale converter inputs"):
            book.validate_manifest(self.root, self.output, ["README.md"])

    def test_two_editions_do_not_overwrite_artifacts_or_manifests(self):
        main_text = self.build()
        main_manifest = (self.output / "manual-source-manifest.json").read_bytes()
        agent_text = self.build(agent=True)
        self.assertIn("short manual for the human driver", agent_text)
        self.assertNotIn("Canonical citation", agent_text)
        self.assertEqual((self.output / (book.STEM + ".tex")).read_text(), main_text)
        self.assertEqual((self.output / "manual-source-manifest.json").read_bytes(), main_manifest)
        agent_manifest = json.loads((self.output / "agent-manual-source-manifest.json").read_text())
        self.assertEqual(agent_manifest["bibliography_keys"], [])
        self.assertEqual(agent_manifest["figure_inputs"], {})
        book.validate_manifest(self.root, self.output, ["README.md"])
        book.validate_manifest(self.root, self.output, book.AGENT_FILES, agent=True)

    def test_freshness_check_selects_the_intended_manual(self):
        self.build()
        self.build(agent=True)
        (self.root / "AGENT_OPERATORS.md").write_text("# Revised human intervention procedure\n")
        book.validate_manifest(self.root, self.output, ["README.md"])
        with self.assertRaisesRegex(ValueError, "Stale chapter hash: AGENT_OPERATORS.md"):
            book.validate_manifest(self.root, self.output, book.AGENT_FILES, agent=True)

    def test_missing_short_manual_cannot_silently_disappear(self):
        (self.root / "AGENT_OPERATORS.md").unlink()
        with self.assertRaisesRegex(ValueError, "Missing Agent Operator"):
            book.validate_inputs(self.root, ["README.md"])
        with self.assertRaisesRegex(ValueError, "Missing Agent Operator"):
            book.validate_inputs(self.root, book.AGENT_FILES, agent=True)

    def test_wrong_manual_manifest_is_rejected(self):
        self.build()
        self.build(agent=True)
        (self.output / "manual-source-manifest.json").write_bytes(
            (self.output / "agent-manual-source-manifest.json").read_bytes())
        with self.assertRaisesRegex(ValueError, "Manifest describes the other manual"):
            book.validate_manifest(self.root, self.output, ["README.md"])


class PortableLinks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="cslib-frontier-manual-links-")
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name).resolve()
        self.root = self.repo / 'manual'
        self.root.mkdir()
        (self.repo / 'CslibFrontierTests').mkdir()
        self.revision = 'a' * 40
        for name, value in {
            'ROOT': self.root, 'FILES': ['README.md', 'workflows/first.md'],
            'SOURCE_REVISION': self.revision,
            'SOURCE_PATHS': {'CslibFrontierTests', 'CslibFrontierTests/A client.lean',
                             'manual/AGENT_OPERATORS.md'},
            'CHANGED_PATHS': set(),
        }.items():
            patch = mock.patch.object(book.base, name, value)
            patch.start()
            self.addCleanup(patch.stop)

    def link(self, href, path='README.md'):
        return book.base.transform({'t': 'Link', 'c': [
            ['', [], []], [{'t': 'Str', 'c': 'Client'}], [href, 'Title']]}, path)

    def target(self, href, path='README.md'):
        return self.link(href, path)['c'][2][0]

    def test_source_links_are_pinned_encoded_and_keep_query_and_fragment(self):
        self.assertEqual(self.target('../CslibFrontierTests/A%20client.lean?plain=1#L12'),
                         f'https://github.com/cslib-community/cslib-frontier/blob/{self.revision}'
                         '/CslibFrontierTests/A%20client.lean?plain=1#L12')
        self.assertEqual(self.target('../CslibFrontierTests'),
                         f'https://github.com/cslib-community/cslib-frontier/tree/{self.revision}'
                         '/CslibFrontierTests')

    def test_internal_anchors_and_citations_stay_in_the_book(self):
        self.assertEqual(self.target('workflows/first.md#example'),
                         '#doc-workflows-first--example')
        self.assertEqual(self.target('#overview'), '#doc-README--overview')
        self.assertEqual(self.target('sources.md'), '#doc-sources')
        self.assertEqual(self.link('sources.md#example')['c'], ['latex', r'\cite{example}'])

    def test_other_manual_is_a_repository_link(self):
        self.assertEqual(self.target('AGENT_OPERATORS.md#review'),
                         f'https://github.com/cslib-community/cslib-frontier/blob/{self.revision}'
                         '/manual/AGENT_OPERATORS.md#review')

    def test_external_links_are_unchanged(self):
        for href in ('https://example.org/a?q=b#c', '//example.org/a#b', 'mailto:a@example.org'):
            with self.subTest(href=href):
                self.assertEqual(self.target(href), href)

    def test_unpublished_or_changed_targets_fail_instead_of_linking_wrong_content(self):
        with self.assertRaisesRegex(ValueError, 'absent from the rendered revision'):
            self.target('../CslibFrontierTests/New.lean')
        with mock.patch.object(book.base, 'CHANGED_PATHS', {'CslibFrontierTests/A client.lean'}):
            for href in ('../CslibFrontierTests/A%20client.lean', '../CslibFrontierTests'):
                with self.subTest(href=href), self.assertRaisesRegex(ValueError, 'uncommitted changes'):
                    self.target(href)

    def test_paths_outside_repository_are_rejected(self):
        with self.assertRaisesRegex(ValueError, 'outside the repository'):
            self.target('../../outside.txt')


class VisualSources(unittest.TestCase):
    diagram = 'flowchart TB\nA["Encoded input"]\nB["Machine<br/>certificate"]\nA -->|"realized by"| B\n'

    def test_diagram_labels_edges_and_line_breaks_survive_conversion(self):
        dot = book.visuals.graphviz_source(self.diagram)
        self.assertIn('A [label="Encoded input"]', dot)
        self.assertIn('B [label="Machine\\ncertificate"]', dot)
        self.assertIn('A -> B [label="realized by"]', dot)
        self.assertIn('style=dashed', book.visuals.graphviz_source(self.diagram.replace('-->', '-.->')))

    def test_unsupported_diagram_syntax_and_unknown_nodes_fail(self):
        for bad in (self.diagram + 'click A "https://example.org"\n',
                    self.diagram.replace('B["Machine<br/>certificate"]\n', ''),
                    self.diagram + 'A["Another input"]\n'):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                book.visuals.flowchart(bad)

    def test_diagrams_inside_documentation_fences_are_not_figures(self):
        text = '````markdown\n```mermaid\n' + self.diagram + '```\n````\n'
        self.assertEqual(book.visuals.diagram_sources(text), [])
        self.assertEqual(book.visuals.check_markup(text)['diagrams'], 0)

    def test_fenced_merge_conflicts_are_literal_examples(self):
        conflict = "<<<<<<< HEAD\nOld.\n||||||| base\nBase.\n=======\nNew.\n>>>>>>> feature\n"
        for fence in ("```", "~~~~", "`````"):
            with self.subTest(fence=fence):
                text = fence + "text\n" + conflict + fence + "\n"
                self.assertEqual(book.visuals.check_markup(text),
                                 {"diagrams": 0, "worked_examples": 0})
        nested = "````markdown\n```text\n" + conflict + "```\n````\n"
        self.assertEqual(book.visuals.check_markup(nested)['worked_examples'], 0)

    def test_valid_markdown_is_not_a_merge_conflict(self):
        text = "# Heading\n\nSetext heading\n=======\n\n---\n\n***\n\n___\n\n>>>>>>> A quotation\n"
        self.assertEqual(book.visuals.check_markup(text), {"diagrams": 0, "worked_examples": 0})

    def test_list_fenced_conflicts_are_literal_until_the_fence_closes(self):
        conflict = "<<<<<<< HEAD\nOld.\n=======\nNew.\n>>>>>>> feature\n"
        for marker in ("- ", "+ ", "* ", "1. ", "12) ", "- - "):
            with self.subTest(marker=marker):
                indent = " " * len(marker)
                example = marker + "```text\n" + "".join(
                    indent + line + "\n" for line in conflict.splitlines()) + indent + "```\n"
                self.assertEqual(book.visuals.check_markup(example),
                                 {"diagrams": 0, "worked_examples": 0})
                for after in ("<<<<<<< HEAD\n", indent + "<<<<<<< HEAD\n"):
                    with self.assertRaisesRegex(ValueError, "Line 8: unresolved Git merge conflict"):
                        book.visuals.check_markup(example + after)
                literal_diagram = marker + "````markdown\n" + indent + "```mermaid\n" + \
                    indent + "This is a literal example, not a model diagram.\n" + \
                    indent + "```\n" + indent + "````\n"
                self.assertEqual(book.visuals.check_markup(literal_diagram)['diagrams'], 0)

    def test_leaving_a_list_also_ends_its_literal_fence(self):
        text = "- ```text\n  Literal example.\n<<<<<<< HEAD\nOld.\n=======\nNew.\n>>>>>>> feature\n"
        with self.assertRaisesRegex(ValueError, "Line 3: unresolved Git merge conflict"):
            book.visuals.check_markup(text)

    def test_similar_source_paths_keep_distinct_diagram_assets(self):
        paths = ['topic-one.md', 'topic/one.md', 'topic_one.md']
        names = [book.visuals.diagram_name(path, 1) for path in paths]
        self.assertEqual(len(set(names)), len(paths))
        self.assertEqual(names[1], 'figures/topic/one-1.pdf')

    def test_nested_mermaid_fences_fail_before_publishing(self):
        for prefix in ('> ', '>> ', '  ', '    ', '- ', '1. ', '> - ', '- - ', '1. - '):
            with self.subTest(prefix=prefix), self.assertRaisesRegex(ValueError, 'top-level'):
                book.visuals.check_markup(prefix + '```mermaid\n' + self.diagram + '```\n')

    def test_nested_mermaid_ast_cannot_silently_remain_code(self):
        code = {'t': 'CodeBlock', 'c': [['', ['mermaid'], []], self.diagram]}
        for block in ({'t': 'BlockQuote', 'c': [code]},
                      {'t': 'BulletList', 'c': [[code]]}):
            with self.subTest(block=block), self.assertRaisesRegex(ValueError, 'top-level'):
                book.visuals.render_blocks([block], 'topic.md', Path('/unused'), {}, book.base.tex_escape)

    def test_example_boundaries_fail_before_publishing(self):
        for text in ('<!-- worked-example -->\n**Worked example: Test**\n',
                     '<!-- /worked-example -->',
                     '<!-- worked-example -->\n**Missing title prefix**\n<!-- /worked-example -->',
                     '<!-- worked-example -->\n**Worked example: Test**\n## Heading\n<!-- /worked-example -->'):
            with self.subTest(text=text), self.assertRaises(ValueError):
                book.visuals.check_markup(text)

    def test_example_markers_inside_code_are_not_boundaries(self):
        text = '<!-- worked-example -->\n**Worked example: Test**\n```text\n<!-- /worked-example -->\n```\n<!-- /worked-example -->'
        self.assertEqual(book.visuals.check_markup(text)['worked_examples'], 1)

    def test_example_title_and_lean_body_are_preserved_in_render_ast(self):
        blocks = [
            {'t': 'RawBlock', 'c': ['html', '<!-- worked-example -->']},
            {'t': 'Para', 'c': [{'t': 'Strong', 'c': [{'t': 'Str', 'c': 'Worked example: A & B'}]}]},
            {'t': 'CodeBlock', 'c': [['', ['lean'], []], 'example : True := by trivial']},
            {'t': 'RawBlock', 'c': ['html', '<!-- /worked-example -->']},
        ]
        result = book.visuals.render_blocks(blocks, 'topic.md', Path('/unused'), {}, book.base.tex_escape)
        self.assertEqual(result[1], blocks[2])
        self.assertEqual(result[0]['c'][1], r'\begin{manualexample}{A \& B}')
        self.assertEqual(result[-1]['c'][1], r'\end{manualexample}')


class DiagramFreshness(unittest.TestCase):
    setUp = BookInputs.setUp
    build = BookInputs.build
    def test_missing_or_altered_diagram_cannot_pass_freshness(self):
        self.build()
        chapter = self.root / 'README.md'
        chapter.write_text(chapter.read_text() + '\n```mermaid\n' + VisualSources.diagram + '```\n')
        path = self.output / 'manual-source-manifest.json'
        manifest = json.loads(path.read_text())
        manifest['chapter_inputs']['README.md'] = book.sha(chapter)
        path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'Manifest diagrams'):
            book.validate_manifest(self.root, self.output, ['README.md'])
        figure = self.output / 'figures/README-1.pdf'
        figure.parent.mkdir()
        figure.write_bytes(b'original diagram')
        manifest['diagram_outputs'] = {'figures/README-1.pdf': book.sha(figure)}
        path.write_text(json.dumps(manifest))
        book.validate_manifest(self.root, self.output, ['README.md'])
        figure.write_bytes(b'changed diagram')
        with self.assertRaisesRegex(ValueError, 'Missing or changed diagram'):
            book.validate_manifest(self.root, self.output, ['README.md'])
        figure.unlink()
        with self.assertRaisesRegex(ValueError, 'Missing or changed diagram'):
            book.validate_manifest(self.root, self.output, ['README.md'])


if __name__ == "__main__":
    unittest.main()
