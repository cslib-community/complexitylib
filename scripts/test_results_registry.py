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
                      "sources": [{"bib_key": "Example2026", "locator": "Theorem 1"}]}
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
        (self.root / "results").mkdir()
        (self.root / "results/registry.json").write_text(json.dumps({
            "schema_version": 1, "abstract_catalogue": "abstracts/catalogue.json", "results": []}))
        abstract = {"id": "example", "title": "Current catalogue title", "scope": "Current scope",
                    "module": "ComplexityAbstracts.ExampleAbstract",
                    "headline_theorems": ["Abstract.example"]}
        with patch.object(registry.build_abstracts, "load_catalogue", return_value=[abstract]):
            entries = registry.collect(self.root)
        self.assertEqual(entries[0]["title"], abstract["title"])
        self.assertEqual(entries[0]["scope"], abstract["scope"])
        self.assertEqual(entries[0]["source_review"], "module-citations")
        self.assertEqual(entries[0]["sources"], [{"bib_key": "Example2026", "locator": None}])
        rendered = registry.markdown(entries, self.root)
        self.assertIn("abstracts/ComplexityAbstracts/ExampleAbstract.lean#L3", rendered)
        self.assertNotIn("ComplexityAbstracts/ExampleAbstract.html", rendered)

    def test_indexes_resolve_declaration_and_bibliography_targets(self):
        text = registry.markdown([self.entry], self.root)
        self.assertIn("Complexity/Example.html#Cslib.example", text)
        self.assertIn("references.bib#L1", text)
        self.assertIn("Theorem 1", text)
        self.assertIn("not newly source-verified", text)
        papers = registry.markdown([self.entry], self.root, papers=True)
        self.assertIn("## [Example2026]", papers)


if __name__ == "__main__":
    unittest.main()
