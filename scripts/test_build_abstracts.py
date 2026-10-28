#!/usr/bin/env python3
"""Selection, display-boundary and provenance regressions for formal abstract PDFs."""

import json
from contextlib import chdir
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import build_abstracts as build


SOURCE = """/-! # A checked statement

This is the mathematical introduction.
-/
namespace ComplexityTests.Abstracts.ExampleAbstract
/-- A visible definition. -/
def value : Nat := 0

/-- The selected result. -/
theorem chosen : value = 0 := rfl

/-- A supporting result that is not selected. -/
theorem other : True := by trivial
end ComplexityTests.Abstracts.ExampleAbstract
"""


class BuildAbstractsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="test-abstract-builder-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        source = self.root / "abstracts/ComplexityAbstracts/ExampleAbstract.lean"
        source.parent.mkdir(parents=True)
        source.write_text(SOURCE)
        scripts = self.root / "scripts"
        scripts.mkdir()
        for name in ("build_abstracts.py", "abstract_to_tex.py", "proof_lengths.py"):
            shutil.copyfile(Path(build.__file__).with_name(name), scripts / name)
        self.entry = {"id": "example", "title": "An example", "summary": "The selected result.",
                      "scope": "No algorithmic claim.",
                      "module": "ComplexityAbstracts.ExampleAbstract",
                      "namespace": "ComplexityTests.Abstracts.ExampleAbstract",
                      "headline_theorems": ["ComplexityTests.Abstracts.ExampleAbstract.chosen"]}
        self.manifest = self.root / "catalogue.json"
        self.write_manifest([self.entry])

    def write_manifest(self, entries):
        self.manifest.write_text(json.dumps({"title": "Selected abstracts", "entries": entries}))

    def add_foundations(self):
        modules = ["ComplexityAbstracts.Encoding", "ComplexityAbstracts.Computation"]
        for module, imports, name in (
            (modules[0], "import Complexity.ProofOnly\n", "binaryCode"),
            (modules[1], "import ComplexityAbstracts.Encoding\n", "polynomialTime"),
        ):
            build.module_source_path(module, self.root).write_text(
                imports + f"/-! # {module.rsplit('.', 1)[-1]} foundation\n"
                "Exact checked definitions.\n-/\n"
                f"namespace ComplexityTests.Abstracts.{module.rsplit('.', 1)[-1]}\n"
                f"/-- The foundational definition {name}. -/\ndef {name} : Nat := 0\n"
                f"end ComplexityTests.Abstracts.{module.rsplit('.', 1)[-1]}\n")
        source = build.module_source_path(self.entry["module"], self.root)
        source.write_text("import ComplexityAbstracts.Check\n"
                          "import ComplexityAbstracts.ExampleBridge\n"
                          "import ComplexityAbstracts.Computation\n" + SOURCE)
        self.entry["foundations"] = modules
        self.write_manifest([self.entry])
        return modules

    @staticmethod
    def fake_pdf(tex):
        pdf = tex.with_suffix(".pdf")
        pdf.write_bytes(b"%PDF-fixture")
        return pdf

    def test_foundations_require_an_exact_manifest_and_import_closure(self):
        modules = self.add_foundations()
        self.assertEqual(build.entry_foundations(self.entry, self.root), modules)
        self.assertEqual(build.load_catalogue(self.manifest, self.root), [self.entry])
        for listed, message in ((None, "list of module"), (modules * 2, "Duplicate foundation"),
                                ([modules[1]], "missing"), ([], "missing"),
                                (["Other.Encoding"], "formal-abstract module"),
                                (["ComplexityAbstracts.Missing"], "Missing shared foundation"),
                                (["ComplexityAbstracts.ExampleAbstract"], "Not a shared")):
            self.entry["foundations"] = listed
            self.write_manifest([self.entry])
            with self.subTest(listed=listed), self.assertRaisesRegex(ValueError, message):
                build.load_catalogue(self.manifest, self.root)
        self.entry["foundations"] = modules
        build.module_source_path(self.entry["module"], self.root).write_text(SOURCE)
        self.write_manifest([self.entry])
        with self.assertRaisesRegex(ValueError, "unused"):
            build.load_catalogue(self.manifest, self.root)

    def test_comment_import_spoofs_do_not_create_foundation_dependencies(self):
        source = build.module_source_path(self.entry["module"], self.root)
        source.write_text('/- import ComplexityAbstracts.Missing -/\n' + SOURCE +
                          '\ndef banner := "import ComplexityAbstracts.Missing"\n')
        self.assertEqual(build.entry_foundations(self.entry, self.root), [])

    def test_cyclic_foundations_fail_closed(self):
        modules = self.add_foundations()
        source = build.module_source_path(modules[0], self.root)
        source.write_text("import ComplexityAbstracts.Computation\n" + source.read_text())
        with self.assertRaisesRegex(ValueError, "Cyclic shared foundations"):
            build.load_catalogue(self.manifest, self.root)

    def test_foundations_are_displayed_with_source_and_declaration_links(self):
        modules = self.add_foundations()
        output = build.render_entry(self.entry, "owner/repo", "a" * 40, False, self.root)
        self.assertLess(output.index(r"\textbf{theorem}"), output.index("Appendix: shared"))
        self.assertIn("binary", output)
        self.assertIn("polynomial", output)
        for module in modules:
            record = build.foundation_record(module, "owner/repo", "a" * 40, self.root)
            self.assertIn(record["url"], output)
            self.assertIn(record["declarations"][0]["url"], output)
            self.assertEqual(record["source_sha256"],
                             build.digest(build.module_source_path(module, self.root)))
        self.assertIn("ComplexityTests.Abstracts.Encoding",
                      build.foundation_record(modules[0], "owner/repo", "a" * 40,
                                              self.root)["namespaces"])

    def test_combined_catalogue_includes_shared_foundations_once(self):
        modules = self.add_foundations()
        other = {**self.entry, "id": "second", "module": "ComplexityAbstracts.SecondAbstract",
                 "namespace": "ComplexityTests.Abstracts.SecondAbstract",
                 "headline_theorems": ["ComplexityTests.Abstracts.SecondAbstract.chosen"]}
        source = build.module_source_path(self.entry["module"], self.root).read_text()
        build.module_source_path(other["module"], self.root).write_text(
            source.replace("ExampleAbstract", "SecondAbstract"))
        self.write_manifest([self.entry, other])
        with patch.object(build, "git", side_effect=["a" * 40, ""]), \
             patch.object(build.shutil, "which", return_value="latexmk"), \
             patch.object(build, "build_pdf", side_effect=self.fake_pdf):
            result = build.build(self.manifest, self.root / "build", root=self.root)
        for name in ("example", "second", "catalogue"):
            output = (self.root / f"build/{name}.tex").read_text()
            self.assertEqual(output.count(r"\section*{Appendix: shared foundations}"), 1)
            self.assertEqual(output.count(r"\subsection*{Encoding foundation}"), 1)
            self.assertEqual(output.count(r"\subsection*{Computation foundation}"), 1)
        combined = (self.root / "build/catalogue.tex").read_text()
        self.assertGreater(combined.index("Appendix: shared"), combined.index(r"\hypertarget{second}"))
        self.assertEqual(result["catalogue"]["foundations"], modules)
        for module in modules:
            path = build.module_source_path(module, self.root)
            self.assertIn({"path": str(path.relative_to(self.root)), "sha256": build.digest(path)},
                          result["inputs"])
        self.assertEqual([record["module"] for record in result["documents"][0]["foundations"]],
                         modules)

    def test_foundation_change_during_generation_invalidates_provenance(self):
        modules = self.add_foundations()

        def changing_pdf(tex):
            path = build.module_source_path(modules[0], self.root)
            path.write_text(path.read_text() + "\n-- changed\n")
            return self.fake_pdf(tex)

        with patch.object(build, "git", side_effect=["a" * 40, ""]), \
             patch.object(build.shutil, "which", return_value="latexmk"), \
             patch.object(build, "build_pdf", side_effect=changing_pdf):
            with self.assertRaisesRegex(ValueError, "Source changed.*Encoding.lean"):
                build.build(self.manifest, self.root / "build", root=self.root)
        self.assertFalse((self.root / "build/provenance.json").exists())

    def test_selected_theorems_cannot_be_moved_to_an_appendix(self):
        source = build.module_source_path(self.entry["module"], self.root)
        source.write_text(SOURCE.replace("/-- The selected result. -/",
                                        "/-! ## Representation details -/\n/-- The selected result. -/"))
        with self.assertRaisesRegex(ValueError, "main presentation"):
            build.load_catalogue(self.manifest, self.root)

    def test_other_section_headings_do_not_hide_selected_theorems(self):
        source = build.module_source_path(self.entry["module"], self.root)
        source.write_text(SOURCE.replace("/-- The selected result. -/",
                                        "/-! ## Other results -/\n/-- The selected result. -/"))
        self.assertEqual(build.load_catalogue(self.manifest, self.root), [self.entry])
        self.assertIn("theorem chosen", build.render.render_source(source, "markdown"))

    def test_standalone_previews_include_foundation_definitions_and_digests(self):
        modules = self.add_foundations()
        source = build.module_source_path(self.entry["module"], self.root)
        for format in ("markdown", "tex"):
            output = build.render.render_source(source, format)
            for module in modules:
                path = build.module_source_path(module, self.root)
                self.assertIn(build.digest(path), output)
            self.assertIn("binary", output)
            self.assertIn("polynomial", output)
            self.assertLess(output.index("chosen"), output.index("Shared foundation:"))

    def test_module_source_path_uses_dedicated_library_root(self):
        self.assertEqual(build.module_source_path(self.entry["module"], self.root),
                         self.root / "abstracts/ComplexityAbstracts/ExampleAbstract.lean")
        for module in ("ComplexityTests.Abstracts.ExampleAbstract", "Other.ExampleAbstract",
                       "ComplexityAbstracts../ExampleAbstract", "ComplexityAbstracts.9Abstract"):
            with self.subTest(module=module), self.assertRaisesRegex(ValueError, "module"):
                build.module_source_path(module, self.root)

    def test_module_namespace_is_the_default_when_not_overridden(self):
        self.entry.pop("namespace")
        source = build.module_source_path(self.entry["module"], self.root)
        source.write_text(SOURCE.replace("ComplexityTests.Abstracts.ExampleAbstract",
                                         self.entry["module"]))
        self.entry["headline_theorems"] = [self.entry["module"] + ".chosen"]
        self.write_manifest([self.entry])
        self.assertEqual(build.load_catalogue(self.manifest, self.root), [self.entry])

    def test_invalid_missing_and_foreign_namespaces_are_rejected(self):
        for namespace in (None, 42, "", " ", "Other..Abstract", "Other.9Abstract", "Other\nAbstract"):
            with self.subTest(namespace=namespace):
                self.entry["namespace"] = namespace
                self.write_manifest([self.entry])
                with self.assertRaisesRegex(ValueError, "Invalid abstract namespace"):
                    build.load_catalogue(self.manifest, self.root)
        self.entry.pop("namespace")
        self.write_manifest([self.entry])
        with self.assertRaisesRegex(ValueError, "namespace.*not declared"):
            build.load_catalogue(self.manifest, self.root)
        self.entry["namespace"] = "Other.Abstract"
        self.write_manifest([self.entry])
        with self.assertRaisesRegex(ValueError, "namespace.*not declared"):
            build.load_catalogue(self.manifest, self.root)

    def test_quote_character_does_not_hide_the_source_namespace(self):
        source = build.module_source_path(self.entry["module"], self.root)
        source.write_text("def quote := '\"'\n" + SOURCE)
        self.assertEqual(build.load_catalogue(self.manifest, self.root), [self.entry])

    def test_primed_identifiers_are_not_character_literals(self):
        self.assertEqual(build.declaration_line(
            "namespace Example\ntheorem lemma'a' : True := by trivial\nend Example\n",
            "Example.lemma'a'"), 2)
        source = build.module_source_path(self.entry["module"], self.root)
        source.write_text(SOURCE.replace("theorem chosen :", "theorem chosen'a' :")
                          .replace("rfl\n", "rfl\n\ndef quote := 'q'\n", 1))
        entry = {**self.entry,
                 "headline_theorems": ["ComplexityTests.Abstracts.ExampleAbstract.chosen'a'"]}
        self.write_manifest([entry])
        self.assertEqual(build.load_catalogue(self.manifest, self.root), [entry])

    def test_comment_and_string_namespace_spoofs_are_rejected(self):
        namespace = self.entry["namespace"]
        source = build.module_source_path(self.entry["module"], self.root)
        foreign_source = SOURCE.replace(namespace, "Other.Abstract")
        for spoof in (f"/- outer /- nested -/\nnamespace {namespace}\n-/\n",
                      f' def banner := "\nnamespace {namespace}\n"\n',
                      f' def banner := r##"\nnamespace {namespace}\n"##\n'):
            with self.subTest(spoof=spoof):
                source.write_text(spoof + foreign_source)
                with self.assertRaisesRegex(ValueError, "namespace.*not declared"):
                    build.load_catalogue(self.manifest, self.root)

    def test_headline_in_a_different_source_namespace_is_rejected(self):
        namespace = self.entry["namespace"]
        source = build.module_source_path(self.entry["module"], self.root)
        source.write_text(SOURCE.replace("/-- The selected result. -/",
                                         f"end {namespace}\nnamespace Other.Abstract\n"
                                         "/-- The selected result. -/"))
        with self.assertRaisesRegex(ValueError, "outside namespace"):
            build.load_catalogue(self.manifest, self.root)

    def test_selection_rejects_duplicates_and_non_theorem_headlines(self):
        self.assertEqual(build.load_catalogue(self.manifest, self.root), [self.entry])
        self.write_manifest([self.entry, self.entry])
        with self.assertRaisesRegex(ValueError, "duplicate catalogue id"):
            build.load_catalogue(self.manifest, self.root)
        self.entry["headline_theorems"] = [self.entry["namespace"] + ".value"]
        self.write_manifest([self.entry])
        with self.assertRaisesRegex(ValueError, "not a theorem"):
            build.load_catalogue(self.manifest, self.root)

    def test_missing_or_foreign_headline_is_rejected(self):
        self.entry["headline_theorems"] = [self.entry["namespace"] + ".missing"]
        self.write_manifest([self.entry])
        with self.assertRaisesRegex(ValueError, "found 0"):
            build.load_catalogue(self.manifest, self.root)
        self.entry["headline_theorems"] = ["Other.Abstract.chosen"]
        self.write_manifest([self.entry])
        with self.assertRaisesRegex(ValueError, "qualified within"):
            build.load_catalogue(self.manifest, self.root)

    def test_display_keeps_definitions_and_selected_statements_without_proofs(self):
        rendered = build.render_entry(self.entry, "owner/repo", "a" * 40, False, self.root)
        self.assertIn(r"\begin{leanbox}", rendered)
        self.assertIn("value", rendered)
        self.assertIn("chosen", rendered)
        self.assertNotIn("supporting result", rendered)
        self.assertNotIn("other", rendered)
        self.assertNotIn("rfl", rendered)
        self.assertIn("a" * 40 + "/abstracts/ComplexityAbstracts/ExampleAbstract.lean", rendered)
        self.assertIn(r"\textcolor{leanblue}", rendered)

    def test_selected_statement_with_bindings_is_displayed_in_full(self):
        """Issue #699: statements with `let` bindings and `:=` in comments or strings keep
        their full type, blank lines in proofs do not leak them, and an adjacent definition
        is displayed."""
        statement = ("theorem chosen :\n    let width := value + 1 -- an `:=` in a comment\n"
                     '    let label := "a := b"\n    width = 1 ∧ label = label')
        source = build.module_source_path(self.entry["module"], self.root)
        source.write_text(SOURCE.replace(
            "theorem chosen : value = 0 := rfl",
            statement + " := by\n  simp\n\n  -- proofTailMarker\n  exact proofMarker\n"
                        "def adjacentMarker : Nat := 3"))
        self.assertEqual(build.load_catalogue(self.manifest, self.root), [self.entry])
        self.assertEqual(build.selected_statement(source.read_text(),
                                                  self.entry["headline_theorems"][0]), statement)
        rendered = build.render_entry(self.entry, "owner/repo", "a" * 40, False, self.root)
        for marker in ("width = 1", "label = label", "adjacent"):
            self.assertIn(marker, rendered)
        for marker in ("TailMarker", "proofMarker", "simp"):
            self.assertNotIn(marker, rendered)

    def test_multiline_absolute_value_statement_is_checked_in_full(self):
        """#716 review: `Eq\n    |x| |x|` was cut at `Eq`, and the check accepted it."""
        source = build.module_source_path(self.entry["module"], self.root)
        for statement in ("theorem chosen (x : Int) : Eq\n    |x| |x|",
                          "theorem chosen (x : Int) : Eq (|x|)\n    |x|",
                          "theorem chosen (x : Int) : (fun y : Int => y = y)\n    |x|"):
            with self.subTest(statement=statement):
                source.write_text(SOURCE.replace("theorem chosen : value = 0 := rfl",
                                                 statement + " := rfl"))
                self.assertEqual(build.load_catalogue(self.manifest, self.root), [self.entry])
                self.assertEqual(build.selected_statement(
                    source.read_text(), self.entry["headline_theorems"][0]), statement)
                rendered = build.render_entry(self.entry, "owner/repo", "a" * 40, False, self.root)
                self.assertIn(statement.splitlines()[-1].strip(), rendered)
        source.write_text(SOURCE.replace("theorem chosen : value = 0 := rfl",
                                         "theorem chosen : ∀ n : Nat, n = n\n  |0 => rfl\n"
                                         "  |_ => rfl"))
        with self.assertRaisesRegex(ValueError, "chosen: Ambiguous"):
            build.load_catalogue(self.manifest, self.root)

    def test_truncated_statement_fails_the_coverage_check(self):
        """Issue #699: a name-only check accepted `theorem chosen : let n` as rendered."""
        source = build.module_source_path(self.entry["module"], self.root)
        source.write_text(SOURCE.replace("theorem chosen : value = 0 := rfl",
                                         "theorem chosen : let n := 1; n = value + 1 := by rfl"))
        self.assertEqual(build.load_catalogue(self.manifest, self.root), [self.entry])
        # The former renderer ended every statement at its first top-level `:=`.
        with patch.object(build.render, "strip_theorem_proof",
                          side_effect=lambda block: block.split(":=", 1)[0].rstrip()):
            with self.assertRaisesRegex(ValueError, "not displayed in full: .*chosen"):
                build.load_catalogue(self.manifest, self.root)
            with self.assertRaisesRegex(ValueError, "not displayed in full: .*chosen"):
                build.render_entry(self.entry, "owner/repo", "a" * 40, False, self.root)

    def test_attributed_unselected_theorems_do_not_leak_docs_or_proofs(self):
        sections = [{"kind": "decl", "doc": "Unselected compatibility helper.",
                     "code": '@[deprecated (since := "2026-10-23")]\n'
                             "theorem helper : True := Bridge.helper"},
                    {"kind": "decl", "doc": "Selected result.",
                     "code": "@[simp]\ntheorem chosen : True := Bridge.chosen"}]
        output, displayed = build.render_sections(sections, {"chosen"})
        self.assertEqual(displayed, {"chosen": "@[simp]\ntheorem chosen : True"})
        self.assertNotIn("helper", output)
        self.assertNotIn("Bridge", output)
        self.assertIn("chosen", output)

    @unittest.skipUnless(shutil.which("latexmk") and shutil.which("pdftotext")
                         and shutil.which("kpsewhich"), "TeX/Poppler not installed")
    def test_short_declaration_stays_together_and_long_definition_still_breaks(self):
        for package in ("libertine.sty", "newtxmath.sty", "zi4.sty", "tcolorbox.sty"):
            if subprocess.run(["kpsewhich", package], capture_output=True).returncode:
                self.skipTest(f"TeX package missing: {package}")
        short = {
            "kind": "decl",
            "doc": ("`firstparagraphmarker` stays above when room allows.\n\n"
                    "`explanationstartmarker` begins a multi-line explanation that wraps across\n"
                    "several words so it takes more than one line before `explanationendmarker`."),
            "code": "def ShortMarker : Nat :=\n  123456",
        }
        long = {
            "kind": "decl",
            "doc": ("`longstart123` introduces a genuinely long definition across\n"
                    "multiple lines ending with `longend456`."),
            "code": "def longDefinition : List Nat := [\n" +
                    ",\n".join(f"  {n}" for n in range(1001, 1081)) + "]",
        }
        rendered, _ = build.render_sections([short, long])
        self.assertIn(r"\texttt{firstparagraphmarker} stays above when room allows." + "\n\n"
                      "\\begin{leandeclaration}\n\n"
                      r"\texttt{explanationstartmarker} begins a multi-line explanation that "
                      "wraps across several words so it takes more than one line before "
                      r"\texttt{explanationendmarker}.",
                      rendered)
        body = r"\vbox to 0.86\textheight{\hbox{BeforeMarker}\vfil}\par" + "\n" + rendered
        tex = self.root / "pagination.tex"
        tex.write_text(build.document(body))
        pdf = build.build_pdf(tex)
        pages = subprocess.check_output(["pdftotext", "-layout", str(pdf), "-"], text=True).split("\f")

        def page_of(marker):
            return next(i for i, page in enumerate(pages) if marker in page)

        self.assertEqual(page_of("firstparagraphmarker"), page_of("BeforeMarker"))
        self.assertGreater(page_of("explanationstartmarker"), page_of("BeforeMarker"))
        self.assertEqual(page_of("explanationstartmarker"), page_of("explanationendmarker"))
        self.assertEqual(page_of("explanationstartmarker"), page_of("ShortMarker"))
        self.assertEqual(page_of("ShortMarker"), page_of("123456"))
        self.assertEqual(page_of("longstart123"), page_of("longend456"))
        self.assertEqual(page_of("longstart123"), page_of("1001"))
        self.assertLess(page_of("1001"), page_of("1080"))
        for number in range(1001, 1081):
            self.assertIn(str(number), "\n".join(pages))

    @unittest.skipUnless(shutil.which("latexmk") and shutil.which("pdftotext")
                         and shutil.which("kpsewhich"), "TeX/Poppler not installed")
    def test_footer_collision_detection_rejects_box_and_text_encroachment(self):
        for package in ("libertine.sty", "newtxmath.sty", "zi4.sty", "tcolorbox.sty"):
            if subprocess.run(["kpsewhich", package], capture_output=True).returncode:
                self.skipTest(f"TeX package missing: {package}")
        # A code box whose text stays well above the footer while its drawn frame extends into
        # the footer clearance zone is rejected by the vector-border check.
        protruding_box = (
            r"\vbox to 0.90\textheight{\hbox{TopFiller}\vfil}\par"
            r"\vbox to 0pt{\tcbset{leandeclarationmeasure/.style={unbreakable}}"
            r"\begin{leanbox}\small\ttfamily\noindent "
            r"def highText : Nat := 1\\[55pt]~"
            r"\end{leanbox}\vss}"
        )
        box_tex = self.root / "footer_box_collision.tex"
        box_tex.write_text(build.document(protruding_box))
        with self.assertRaisesRegex(ValueError, "Code box encroaches on provenance footer"):
            build.build_pdf(box_tex)

        protruding_text = (
            r"\vbox to 0.90\textheight{\hbox{TopFiller}\vfil}\par"
            r"\vbox to 0pt{\noindent HighText\\[60pt]LowBodyTextMarker\vss}"
        )
        text_tex = self.root / "footer_text_collision.tex"
        text_tex.write_text(build.document(protruding_text))
        with self.assertRaisesRegex(ValueError, "Body text encroaches on provenance footer"):
            build.build_pdf(text_tex)

    @unittest.skipUnless(shutil.which("latexmk") and shutil.which("pdftotext")
                         and shutil.which("kpsewhich"), "TeX/Poppler not installed")
    def test_gsw_security_abstract_renders_without_split_explanations_or_footer_contact(self):
        for package in ("libertine.sty", "newtxmath.sty", "zi4.sty", "tcolorbox.sty"):
            if subprocess.run(["kpsewhich", package], capture_output=True).returncode:
                self.skipTest(f"TeX package missing: {package}")
        gsw_source = build.ROOT / "abstracts/ComplexityAbstracts/GSWSecurityAbstract.lean"
        for name in (
            "Encoding.lean",
            "Computation.lean",
            "Randomized.lean",
            "GSW.lean",
            "GSWSecurityAbstract.lean",
            "GSWSecurityBridge.lean",
        ):
            shutil.copyfile(
                build.ROOT / "abstracts/ComplexityAbstracts" / name,
                self.root / "abstracts/ComplexityAbstracts" / name,
            )
        gsw_entry = {
            "id": "gsw-security",
            "title": "Generated-key GSW security from decision LWE",
            "summary": "The explicit positive-noise GSW key generator and encryption program are "
                       "uniform strict polynomial time and satisfy single-challenge IND-CPA under "
                       "decision LWE for their exact centered-binomial error family.",
            "scope": "Classical public-key IND-CPA under exact decision LWE; no LWE hardness, "
                     "circular security, or bootstrappability claim.",
            "module": "ComplexityAbstracts.GSWSecurityAbstract",
            "namespace": "ComplexityTests.Abstracts.GSWSecurityAbstract",
            "headline_theorems": [
                "ComplexityTests.Abstracts.GSWSecurityAbstract.native_algorithms",
                "ComplexityTests.Abstracts.GSWSecurityAbstract.indCPA",
            ],
            "foundations": [
                "ComplexityAbstracts.Encoding",
                "ComplexityAbstracts.Computation",
                "ComplexityAbstracts.Randomized",
                "ComplexityAbstracts.GSW",
            ],
        }
        self.write_manifest([gsw_entry])
        sha = "a406f81f19d5cb9c7383cacc1ca37e3d82e60eae"
        with patch.object(build, "git", side_effect=[sha, ""]):
            result = build.build(self.manifest, self.root / "build", root=self.root,
                                 require_clean=True)
        pdf = self.root / "build/gsw-security.pdf"
        pages = subprocess.check_output(["pdftotext", "-layout", str(pdf), "-"],
                                        text=True).split("\f")[:-1]
        self.assertGreaterEqual(len(pages), 5)

        def page_of(snippet):
            matches = [index for index, page in enumerate(pages, 1) if snippet in page]
            self.assertEqual(len(matches), 1, f"Expected {snippet!r} on one page, found {matches}")
            return matches[0]

        for start, end, decl in (
            ("Unary size or security parameter:", "exactly n bits.",
             "def encUnary"),
            ("Total polynomial-time computation on encoded inputs,",
             "explicit time and space bounds.", "def PolyTime"),
            ("Native efficiency.", "supplies efficiency for free.",
             "theorem native_algorithms"),
            ("GSW generated-key IND-CPA from exact decision LWE.",
             "retaining arbitrary saved words.", "theorem indCPA"),
        ):
            with self.subTest(decl=decl):
                self.assertEqual(page_of(start), page_of(end))
                self.assertEqual(page_of(start), page_of(decl))

        doc_record = result["documents"][0]
        self.assertEqual(doc_record["source_sha256"], build.digest(gsw_source))
        self.assertEqual(
            [item["url"].rsplit("#", 1)[-1] for item in doc_record["headlines"]],
            ["L118", "L129"],
        )
        if shutil.which("pdfinfo"):
            links = subprocess.check_output(["pdfinfo", "-url", str(pdf)], text=True)
            for headline in doc_record["headlines"]:
                self.assertIn(headline["url"], links)
            self.assertIn(build.STYLE_SOURCE, links)
            self.assertIn(build.EXTRACTION_SOURCE, links)

    def test_source_links_pin_the_declaration_line(self):
        line = build.declaration_line(SOURCE, self.entry["headline_theorems"][0])
        self.assertEqual(SOURCE.splitlines()[line - 1], "theorem chosen : value = 0 := rfl")
        self.assertEqual(build.source_url("owner/repo", "a" * 40, "X.lean", line),
                         "https://github.com/owner/repo/blob/" + "a" * 40 + f"/X.lean#L{line}")

    def test_provenance_records_pdf_and_input_digests(self):
        source = build.module_source_path(self.entry["module"], self.root)
        bridge = source.with_name("ExampleBridge.lean")
        bridge.write_text("-- proof bridge fixture\n")

        def fake_pdf(tex):
            pdf = tex.with_suffix(".pdf")
            pdf.write_bytes(b"%PDF-fixture")
            return pdf

        with patch.object(build, "git", side_effect=["a" * 40, ""]), \
             patch.object(build.shutil, "which", return_value="latexmk"), \
             patch.object(build, "build_pdf", side_effect=fake_pdf):
            result = build.build(self.manifest, self.root / "build", root=self.root)
        self.assertFalse(result["source_dirty"])
        self.assertEqual(result["documents"][0]["pdf_sha256"],
                         build.digest(self.root / "build/example.pdf"))
        self.assertEqual(result["documents"][0]["source_sha256"],
                         build.digest(self.root / "abstracts/ComplexityAbstracts/ExampleAbstract.lean"))
        self.assertTrue(result["documents"][0]["headlines"][0]["url"].endswith("#L10"))
        self.assertEqual(result["documents"][0]["source"],
                         "abstracts/ComplexityAbstracts/ExampleAbstract.lean")
        self.assertIn("/abstracts/ComplexityAbstracts/ExampleAbstract.lean#L10",
                      result["documents"][0]["headlines"][0]["url"])
        self.assertIn({"path": "abstracts/ComplexityAbstracts/ExampleBridge.lean",
                       "sha256": build.digest(bridge)}, result["inputs"])
        # The renderer's command and statement scanner is part of the rendering source.
        self.assertIn({"path": "scripts/proof_lengths.py",
                       "sha256": build.digest(self.root / "scripts/proof_lengths.py")},
                      result["inputs"])
        self.assertEqual(len(result["inputs"]), 6)

    def test_relative_manifest_and_output_paths_record_relative_inputs(self):
        def fake_pdf(tex):
            pdf = tex.with_suffix(".pdf")
            pdf.write_bytes(b"%PDF-fixture")
            return pdf

        with chdir(self.root), \
             patch.object(build, "git", side_effect=["a" * 40, ""]), \
             patch.object(build.shutil, "which", return_value="latexmk"), \
             patch.object(build, "build_pdf", side_effect=fake_pdf):
            result = build.build(Path("catalogue.json"), Path("build"), root=self.root)
        self.assertIn({"path": "catalogue.json", "sha256": build.digest(self.manifest)},
                      result["inputs"])
        self.assertTrue((self.root / "build/provenance.json").is_file())

    def test_list_root_is_rejected_consistently(self):
        self.manifest.write_text(json.dumps([self.entry]))
        with self.assertRaisesRegex(ValueError, "title and an entries list"):
            build.load_catalogue(self.manifest, self.root)

    def test_dirty_checkout_cannot_be_published(self):
        with patch.object(build, "git", side_effect=["a" * 40, " M X.lean"]):
            with self.assertRaisesRegex(ValueError, "clean source checkout"):
                build.build(self.manifest, self.root / "build", root=self.root, require_clean=True)

    def test_a_source_change_during_generation_invalidates_provenance(self):
        def changing_pdf(tex):
            pdf = tex.with_suffix(".pdf")
            pdf.write_bytes(b"%PDF-fixture")
            source = self.root / "abstracts/ComplexityAbstracts/ExampleAbstract.lean"
            source.write_text(source.read_text() + "\n-- changed during generation\n")
            return pdf

        output = self.root / "build"
        output.mkdir()
        (output / "provenance.json").write_text("stale provenance")
        with patch.object(build, "git", side_effect=["a" * 40, ""]), \
             patch.object(build.shutil, "which", return_value="latexmk"), \
             patch.object(build, "build_pdf", side_effect=changing_pdf):
            with self.assertRaisesRegex(ValueError, "Source changed during PDF generation"):
                build.build(self.manifest, output, root=self.root)
        self.assertFalse((output / "provenance.json").exists())

    def test_explicit_support_is_rendered_without_promoting_it_to_a_headline(self):
        self.entry["supporting_theorems"] = [self.entry["namespace"] + ".other"]
        self.write_manifest([self.entry])
        build.load_catalogue(self.manifest, self.root)
        rendered = build.render_entry(self.entry, "owner/repo", "a" * 40, False, self.root)
        self.assertIn("supporting result", rendered)
        self.assertIn("other", rendered)
        self.assertEqual(len(self.entry["headline_theorems"]), 1)

    @unittest.skipUnless(shutil.which("latexmk") and shutil.which("pdftotext")
                         and shutil.which("kpsewhich"), "TeX/Poppler not installed")
    def test_styled_pdfs_build_with_source_pinned_hyperlinks(self):
        for package in ("libertine.sty", "newtxmath.sty", "zi4.sty", "tcolorbox.sty"):
            if subprocess.run(["kpsewhich", package], capture_output=True).returncode:
                self.skipTest(f"TeX package missing: {package}")
        self.add_foundations()
        with patch.object(build, "git", side_effect=["a" * 40, ""]):
            result = build.build(self.manifest, self.root / "build", root=self.root,
                                 require_clean=True)
        self.assertEqual(len(result["documents"]), 1)
        self.assertIn("Selected abstracts", (self.root / "build/catalogue.tex").read_text())
        if shutil.which("pdfinfo"):
            links = subprocess.check_output(
                ["pdfinfo", "-url", str(self.root / "build/example.pdf")], text=True)
            self.assertIn(result["documents"][0]["headlines"][0]["url"], links)
            for foundation in result["documents"][0]["foundations"]:
                self.assertIn(foundation["url"], links)
                self.assertIn(foundation["declarations"][0]["url"], links)


if __name__ == "__main__":
    unittest.main()
