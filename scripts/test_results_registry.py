# Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Christian Reitwiessner
"""Broken-reference regressions for the initial results inventory."""
import copy
import json
from pathlib import Path
import tempfile
import subprocess
import unittest
from unittest.mock import patch

import results_registry as registry


class RegistryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="codex-results-registry-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "Complexity").mkdir()
        (self.root / "Complexity/Example.lean").write_text("/-! [Example2026] -/\n")
        (self.root / "references.bib").write_text("@article{Example2026, title={An example}}\n")
        self.entry = {"id": "example", "title": "A result", "topic": "examples",
                      "module": "Complexity.Example", "theorems": ["Cslib.example"],
                      "scope": "One bounded model.", "source_review": "recorded",
                      "sources": [{"bib_key": "Example2026", "source_theorem": "Theorem 1",
                                   "locator": "Section 2, p. 3"}]}
        self.constant = {"m": "Complexity.Example", "k": "thm", "e": "axiom"}

    def test_missing_paper_module_and_duplicate(self):
        for change in (lambda e: e.update(module="Complexity.Missing"),
                       lambda e: e["sources"][0].update(bib_key="Missing2026"),
                       lambda e: e.update(module="Complexity../Example")):
            entry = copy.deepcopy(self.entry)
            change(entry)
            with self.assertRaises(ValueError):
                registry.validate([entry], self.root)
        with self.assertRaisesRegex(ValueError, "duplicate result id"):
            registry.validate([self.entry, self.entry], self.root)
        other = dict(self.entry, id="other")
        with self.assertRaisesRegex(ValueError, "Duplicate theorem"):
            registry.validate([self.entry, other], self.root)

    def test_source_theorem_identifier_must_be_explicit_and_nonblank_if_recorded(self):
        for change in (lambda r: r.pop("source_theorem"),
                       lambda r: r.update(source_theorem=""),
                       lambda r: r.update(source_theorem="  "),
                       lambda r: r.update(source_theorem=3)):
            entry = copy.deepcopy(self.entry)
            change(entry["sources"][0])
            with self.assertRaisesRegex(ValueError, "source theorem identifier"):
                registry.validate([entry], self.root)
        entry = copy.deepcopy(self.entry)
        entry["sources"][0]["source_theorem"] = None
        registry.validate([entry], self.root)
        rendered = registry.markdown([entry], self.root)
        self.assertIn("source theorem not yet identified", rendered)
        self.assertIn("Section 2, p. 3", rendered)
        entry["sources"][0]["source_theorem"] = "Theorem 1"
        entry["sources"][0]["locator"] = None
        rendered = registry.markdown([entry], self.root)
        self.assertIn("(Theorem 1)", rendered)
        self.assertIn("section/page locator not collected", rendered)
        self.assertNotIn("source theorem not yet identified", rendered)

    def test_compiled_rejects_missing_private_definition_axiom_and_wrong_owner(self):
        registry.validate_constants([self.entry], {"Cslib.example": self.constant})
        variants = [{}, {"Cslib.example": dict(self.constant, e="")},
                    {"Cslib.example": dict(self.constant, k="def")},
                    {"Cslib.example": dict(self.constant, k="axiom")},
                    {"Cslib.example": dict(self.constant, m="Complexity.Other")}]
        for constants in variants:
            with self.subTest(constants=constants), self.assertRaises(ValueError):
                registry.validate_constants([self.entry], constants)

    def test_stale_output_is_rejected_before_metadata_is_read(self):
        with patch.object(registry.lean_outputs, "run", side_effect=
                          subprocess.CalledProcessError(1, ["lake", "build", "--no-build"])), \
                patch.object(registry.lean_outputs, "load_constants") as load:
            with self.assertRaises(subprocess.CalledProcessError):
                registry.compiled_constants([self.entry])
            load.assert_not_called()

    def test_abstract_metadata_is_reused_and_citations_are_context(self):
        source = self.root / "abstracts/ComplexityAbstracts/ExampleAbstract.lean"
        source.parent.mkdir(parents=True)
        source.write_text("/-! [Example2026] -/\nnamespace Abstract\n"
                          "theorem example : True := trivial\nend Abstract\n")
        abstract = {"id": "example", "title": "Current catalogue title", "scope": "Current scope",
                    "module": "ComplexityAbstracts.ExampleAbstract",
                    "headline_theorems": ["Abstract.example"]}
        with patch.object(registry, "load_lean_registry", return_value={
                "schema_version": 1, "abstract_catalogue": "abstracts/catalogue.json", "results": []}), \
                patch.object(registry.build_abstracts, "load_catalogue", return_value=[abstract]):
            entries = registry.collect(self.root)
        self.assertEqual(entries[0]["title"], abstract["title"])
        self.assertEqual(entries[0]["scope"], abstract["scope"])
        self.assertEqual(entries[0]["source_review"], "module-citations")
        self.assertEqual(entries[0]["sources"], [{"bib_key": "Example2026", "source_theorem": None, "locator": None}])
        rendered = registry.markdown(entries, self.root)
        self.assertIn("abstracts/ComplexityAbstracts/ExampleAbstract.lean#L3", rendered)
        self.assertNotIn("ComplexityAbstracts/ExampleAbstract.html", rendered)

    def test_lean_export_checks_freshness_then_runs_exporter_in_requested_root(self):
        manifest = {"schema_version": 1, "abstract_catalogue": "abstracts/catalogue.json",
                    "results": [self.entry]}
        with patch.object(registry.subprocess, "run", side_effect=[
                subprocess.CompletedProcess([], 0, "", ""),
                subprocess.CompletedProcess([], 0, json.dumps(manifest), "")]) as run:
            self.assertEqual(registry.load_lean_registry(self.root), manifest)
        self.assertEqual([call.args[0] for call in run.call_args_list], [
            ["lake", "build", "--no-build", "ComplexityResults"],
            ["lake", "env", "lean", "--run", "scripts/ExportResults.lean"]])
        for call in run.call_args_list:
            self.assertEqual(call.kwargs, dict(cwd=self.root, text=True, check=True,
                                              capture_output=True))

    def test_lean_export_refuses_stale_outputs_and_failed_export(self):
        failure = subprocess.CalledProcessError(1, ["lake"], stderr="stale output")
        for outcomes, expected_calls in (([failure], 1),
                                         ([subprocess.CompletedProcess([], 0), failure], 2)):
            with self.subTest(expected_calls=expected_calls), \
                    patch.object(registry.subprocess, "run", side_effect=outcomes) as run:
                with self.assertRaises(subprocess.CalledProcessError):
                    registry.load_lean_registry(self.root)
                self.assertEqual(run.call_count, expected_calls)

    def test_lean_export_rejects_invalid_json(self):
        with patch.object(registry.subprocess, "run", side_effect=[
                subprocess.CompletedProcess([], 0), subprocess.CompletedProcess([], 0, "Lean error")]):
            with self.assertRaisesRegex(ValueError, "valid JSON"):
                registry.load_lean_registry(self.root)

    def test_indexes_resolve_declaration_and_bibliography_targets(self):
        text = registry.markdown([self.entry], self.root)
        self.assertIn("Complexity/Example.html#Cslib.example", text)
        self.assertIn("references.bib#L1", text)
        self.assertIn("Theorem 1", text)
        self.assertIn("Section 2, p. 3", text)
        self.assertIn("not newly source-verified", text)
        papers = registry.markdown([self.entry], self.root, papers=True)
        self.assertIn("## [Example2026]", papers)


if __name__ == "__main__":
    unittest.main()
