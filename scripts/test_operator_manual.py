#!/usr/bin/env python3
"""Exercise live manual checks with isolated source/link drift and recovery cases."""
import json
import contextlib
import importlib.util
import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from check_operator_manual import check

DATA = Path(__file__).resolve().parents[1] / "manual/data"
with mock.patch.object(sys, "path", [str(DATA), *sys.path]):
    spec = importlib.util.spec_from_file_location("manual_book_builder", DATA / "build_manual.py")
    book = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(book)


class ManualChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="complexitylib-manual-check-")
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.manual = self.repo / "manual"
        (self.manual / "workflows/data").mkdir(parents=True)
        (self.repo / "ComplexityTests").mkdir()
        self.client = self.repo / "ComplexityTests/Client.lean"
        self.fragment = "example : True := by\n  trivial"
        self.client.write_text("import Lean\n\n" + self.fragment + "\n")
        self.doc = self.manual / "workflows/first.md"
        self.doc.write_text(
            "# First client\n\n[Complete client](../../ComplexityTests/Client.lean)\n\n"
            "<!-- excerpt: first -->\n```lean\n" + self.fragment + "\n```\n")
        (self.manual / "README.md").write_text(
            "# Manual\n\n[First client](workflows/first.md#first-client)\n"
            "[Human agent driver](AGENT_OPERATORS.md)\n")
        (self.manual / "AGENT_OPERATORS.md").write_text("# Human direction of agents\n")
        self.manifest = self.manual / "workflows/data/test-excerpts.json"
        self.manifest.write_text(json.dumps([{
            "id": "first", "document": "workflows/first.md",
            "source_path": "ComplexityTests/Client.lean"}]))

    def errors(self):
        return check(self.repo)["errors"]

    def test_current_checkout_needs_no_git_or_historical_revision(self):
        self.assertEqual(self.errors(), [])

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
            "[Complete client](../../ComplexityTests/Client.lean)", "Complete client omitted"))
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


class BookInputs(unittest.TestCase):
    """Exercise the actual assembler, replacing only Git and publishing-tool rendering."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="complexitylib-manual-book-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "manual"
        (self.root / "data").mkdir(parents=True)
        for name in book.CONVERTER_INPUTS:
            (self.root / name).write_text("# fixture rendering input\n")
        (self.root / "README.md").write_text("# A complete first chapter\n")
        (self.root / "AGENT_OPERATORS.md").write_text("# A short manual for the human driver\n")
        (self.root / "paper-plan.md").write_text("# Archived editorial plan\n")
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
        self.temp = tempfile.TemporaryDirectory(prefix="complexitylib-manual-links-")
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.root = self.repo / 'manual'
        self.root.mkdir()
        (self.repo / 'ComplexityTests').mkdir()
        self.revision = 'a' * 40
        for name, value in {
            'ROOT': self.root, 'FILES': ['README.md', 'workflows/first.md'],
            'SOURCE_REVISION': self.revision,
            'SOURCE_PATHS': {'ComplexityTests', 'ComplexityTests/A client.lean',
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
        self.assertEqual(self.target('../ComplexityTests/A%20client.lean?plain=1#L12'),
                         f'https://github.com/cslib-community/complexitylib/blob/{self.revision}'
                         '/ComplexityTests/A%20client.lean?plain=1#L12')
        self.assertEqual(self.target('../ComplexityTests'),
                         f'https://github.com/cslib-community/complexitylib/tree/{self.revision}'
                         '/ComplexityTests')

    def test_internal_anchors_and_citations_stay_in_the_book(self):
        self.assertEqual(self.target('workflows/first.md#example'),
                         '#doc-workflows-first--example')
        self.assertEqual(self.target('#overview'), '#doc-README--overview')
        self.assertEqual(self.target('sources.md'), '#doc-sources')
        self.assertEqual(self.link('sources.md#example')['c'], ['latex', r'\cite{example}'])

    def test_other_manual_is_a_repository_link(self):
        self.assertEqual(self.target('AGENT_OPERATORS.md#review'),
                         f'https://github.com/cslib-community/complexitylib/blob/{self.revision}'
                         '/manual/AGENT_OPERATORS.md#review')

    def test_external_links_are_unchanged(self):
        for href in ('https://example.org/a?q=b#c', '//example.org/a#b', 'mailto:a@example.org'):
            with self.subTest(href=href):
                self.assertEqual(self.target(href), href)

    def test_unpublished_or_changed_targets_fail_instead_of_linking_wrong_content(self):
        with self.assertRaisesRegex(ValueError, 'absent from the rendered revision'):
            self.target('../ComplexityTests/New.lean')
        with mock.patch.object(book.base, 'CHANGED_PATHS', {'ComplexityTests/A client.lean'}):
            for href in ('../ComplexityTests/A%20client.lean', '../ComplexityTests'):
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

    def test_similar_source_paths_keep_distinct_diagram_assets(self):
        paths = ['topic-one.md', 'topic/one.md', 'topic_one.md']
        names = [book.visuals.diagram_name(path, 1) for path in paths]
        self.assertEqual(len(set(names)), len(paths))
        self.assertEqual(names[1], 'figures/topic/one-1.pdf')

    def test_nested_mermaid_fences_fail_before_publishing(self):
        for prefix in ('> ', '>> ', '  ', '    ', '- ', '1. ', '> - '):
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
