#!/usr/bin/env python3
"""Unit and pdflatex integration tests for scripts/abstract_to_tex.py."""

from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
import xml.etree.ElementTree as ET

import abstract_to_tex
import proof_lengths


ROOT = Path(__file__).resolve().parents[1]
ABSTRACTS_DIR = ROOT / "abstracts/ComplexityAbstracts"


class AbstractToTexTests(unittest.TestCase):
    def test_representation_sections_move_after_results_without_losing_code(self):
        sample = """/-! # Title
An abstract.
-/
namespace Example
universe u
/-! ## Representation details
The exact delimiter convention.
-/
/-- A delimiter. -/
def delimiter : Bool := false
/-! A continuation of the representation explanation. -/
def serial : List Bool := [delimiter]
/-! ## Main result -/
/-- The result. -/
theorem headline : serial = [false] := rfl
/-! ## Representation details -/
/-- A second representation detail. -/
def extra : Nat := 2
end Example
"""
        title, intro, sections = abstract_to_tex.parse_abstract(sample)
        for renderer in (abstract_to_tex.render_markdown, abstract_to_tex.render_tex):
            with self.subTest(renderer=renderer.__name__):
                output = renderer(title, intro, sections)
                self.assertIn("universe u", output)
                self.assertLess(output.index("headline"), output.index("Appendix:"))
                self.assertLess(output.index("Appendix:"), output.index("def delimiter"))
                self.assertLess(output.index("def serial"), output.index("def extra"))
                self.assertEqual(output.count("def delimiter"), 1)
                self.assertIn("continuation of the representation", output)
                self.assertNotIn("rfl", output)

    def test_undocumented_declarations_are_not_silently_omitted(self):
        sample = "/-! # Title\nIntro.\n-/\nnamespace Example\ndef first := 1\nend Example\n"
        output = abstract_to_tex.render_markdown(*abstract_to_tex.parse_abstract(sample))
        self.assertIn("def first := 1", output)

    def test_lean_scanner_preserves_primed_identifiers_beside_character_literals(self):
        text = "def result := f' 'a'\ndef quote := '\"'\nnamespace Real\n"
        masked = abstract_to_tex.lean_code(text)
        self.assertIn("f'", masked)
        self.assertNotIn("'a'", masked)
        self.assertNotIn("\"", masked)
        self.assertIn("namespace Real", masked)
        self.assertEqual(len(masked), len(text))

    def test_all_abstracts_render_markdown_and_tex(self):
        expected_theorems = {
            "CookLevinAbstract.lean": [
                "theorem sat_npComplete : NPComplete encCNF SAT",
                "theorem unsat_coNPComplete : coNPComplete encCNF UNSAT",
                "theorem exactThreeSAT_npComplete : NPComplete encCNF ExactThreeSAT",
            ],
            "TQBFAbstract.lean": [
                "inductive Formula where",
                "theorem tqbf_pspaceComplete : PSPACEComplete encQBF TQBF",
            ],
            "SubsetSumAbstract.lean": [
                "def SubsetSum : Set (List ℕ × ℕ) :=",
                "theorem subsetSum_npComplete : NPComplete encSubsetSum SubsetSum",
            ],
        }
        paths = sorted(ABSTRACTS_DIR.glob("*Abstract.lean"))
        self.assertTrue(set(expected_theorems).issubset({path.name for path in paths}),
                        f"Expected abstract sources under {ABSTRACTS_DIR}")
        for path in paths:
            filename = path.name
            snippets = expected_theorems.get(filename, [])
            title, intro, sections = abstract_to_tex.parse_abstract(path.read_text())
            md = abstract_to_tex.render_markdown(title, intro, sections)
            tex = abstract_to_tex.render_tex(title, intro, sections)

            for snippet in snippets:
                self.assertIn(snippet, md, f"Missing {snippet!r} in Markdown for {filename}")

            # Verify proof bodies and #check_abstract command are stripped from code blocks
            self.assertNotIn("#check_abstract ComplexityTests", md)
            self.assertNotIn("abstract audit passed", md)
            self.assertNotIn("guard_msgs", md)
            self.assertNotIn("check\\_abstract ComplexityTests", tex)
            self.assertNotIn("Bridge.", md.split("## Main result")[-1])

            # Verify LaTeX output contains only ASCII characters (safe for pdflatex T1 fontenc)
            non_ascii = [ch for ch in tex if ord(ch) >= 128]
            self.assertEqual(
                non_ascii,
                [],
                f"Unescaped non-ASCII characters in TeX output for {filename}: {set(non_ascii)}",
            )

    def test_strip_theorem_proof_preserves_named_arguments(self):
        sample = (
            "theorem foo (x : ℕ) :\n"
            "    Bar (V := ℕ) x :=\n"
            "  Bridge.foo x"
        )
        self.assertEqual(
            abstract_to_tex.clean_code_for_display(sample),
            "theorem foo (x : ℕ) :\n    Bar (V := ℕ) x",
        )
        prose = "Check `x ** y` and **bold** text."
        self.assertEqual(
            abstract_to_tex.escape_tex_prose(prose),
            r"Check \texttt{x ** y} and \textbf{bold} text.",
        )

    def test_statement_bindings_are_not_the_proof(self):
        """Issue #699: the first top-level `:=` used to end the statement."""
        display = abstract_to_tex.clean_code_for_display
        self.assertEqual(display("theorem chosen : let n := 1; n = 1 := by rfl"),
                         "theorem chosen : let n := 1; n = 1")
        # The shape of `Cslib.Circuits.Boolean.Layered.length_encCompiled_compile_le`.
        statement = (
            "theorem length_encCompiled_compile_le {n m : ℕ} (c : Circuit signature n m) :\n"
            "    let width := n + 3 * c.size\n"
            "    let bits := Nat.log2 width + 1\n"
            "    (encCompiled (compile n c.code)).length ≤\n"
            "      4 * c.depth * (2 * width * (6 * bits + 21) + 1) + m * (2 * bits + 1) + 1")
        self.assertEqual(display(statement + " := by\n  dsimp only\n  let width := n + 3 * c.size\n"
                                 "  exact Bridge.bound c"), statement)
        for statement in (
                "theorem binders (i : Fin 3) :\n    have := i.isLt\n    letI : Inhabited ℕ := ⟨0⟩\n"
                "    (⟨i.val, by have := i.isLt; omega⟩ : Fin 3) = i",
                "theorem bound : some 1 = do\n    let n ← some 1\n    let m := n\n    return m",
                "theorem named (x : ℕ) : Bar (V := ℕ) { val := x } (h := by simp) x"):
            with self.subTest(statement=statement):
                self.assertEqual(display(statement + " := by\n  rfl"), statement)

    def test_blank_lines_and_commands_are_not_confused(self):
        """Issue #699: blank lines are not command boundaries, and a missing blank line is not
        a missing boundary."""
        display = abstract_to_tex.clean_code_for_display
        self.assertEqual(display("theorem t : True := by\n  trivial\n\n  -- tail\n  exact trivial"),
                         "theorem t : True")
        self.assertEqual(display("theorem t : True := trivial\ndef d : Nat := 3"),
                         "theorem t : True\n\ndef d : Nat := 3")
        self.assertEqual(
            display("def table : List ℕ :=\n  [1,\n\n   2]\n@[simp]\ntheorem t : True := trivial\n"
                    "set_option maxRecDepth 1000 in\nprivate theorem u : True := by\n  trivial\n"
                    "-- Explains `d`.\nnoncomputable def d : ℕ := 3"),
            "def table : List ℕ :=\n  [1,\n\n   2]\n\n@[simp]\ntheorem t : True\n\n"
            "set_option maxRecDepth 1000 in\nprivate theorem u : True\n\n"
            "-- Explains `d`.\nnoncomputable def d : ℕ := 3")
        # Top-level text that the scanner does not recognize is never silently omitted.
        with self.assertRaisesRegex(ValueError, "Unrecognized top-level command after theorem t"):
            display("theorem t : True := trivial\nproof_wanted u : False")

    def test_comment_and_string_delimiters_do_not_end_statements(self):
        display = abstract_to_tex.clean_code_for_display
        for statement in (
                "theorem t : True -- not a proof := here (\n  ∧ True",
                "theorem t : True /- := /- nested ) := -/ [ -/ ∧ True",
                'theorem t : "a := b" = "a := (b" ∧ r#"x := ")"# = r#"x := ")"#',
                "theorem t : '(' = '(' ∧ ')' ≠ '['"):
            with self.subTest(statement=statement):
                self.assertEqual(display(statement + " := by\n  rfl"), statement)
        text = 'def gap := "one \\\ntwo"\ndef raw := r#"say "x := y""#\n'
        masked = abstract_to_tex.lean_code(text)
        self.assertEqual(masked.count("\n"), text.count("\n"))
        self.assertNotIn(":= y", masked)

    def test_where_equation_and_absolute_value_statements(self):
        display = abstract_to_tex.clean_code_for_display
        self.assertEqual(display("theorem s : Nonempty ℕ where\n  out := ⟨0⟩"),
                         "theorem s : Nonempty ℕ")
        self.assertEqual(display("theorem e : ∀ n : ℕ, n = n\n  | 0 | 1 => rfl\n  | _ => rfl"),
                         "theorem e : ∀ n : ℕ, n = n")
        for statement in ("theorem a (x : ℤ) :\n    |x| ≤ |x|",
                          "theorem f : g = fun\n    | 0 => 1\n    | _ => 2",
                          "theorem m (n : ℕ) : match n with\n    | 0 => True\n    | _ => True"):
            with self.subTest(statement=statement):
                self.assertEqual(display(statement + " := by\n  simp"), statement)

    def test_multiline_absolute_value_arguments_are_not_equation_clauses(self):
        """#716 review: after a complete term, a line starting with `|x|` continues the
        statement. These compile with Mathlib's absolute value."""
        display = abstract_to_tex.clean_code_for_display
        for statement, proof in (
                ("theorem chosen (x : Int) : Eq\n    |x| |x|", " := rfl"),
                ("theorem chosen (x : Int) : Eq (|x|)\n    |x|", " := rfl"),
                ("theorem chosen (x : Int) : (fun y : Int => y = y)\n    |x|", " := rfl"),
                ("theorem chosen (x : Int) : Eq\n    |x| |x|", " := by\n  exact (fun h => h) rfl"),
                ("theorem chosen (x : Int) : Eq\n    |(fun y : Int => y) x|\n    |x|", " := rfl")):
            with self.subTest(statement=statement, proof=proof):
                self.assertEqual(display(statement + proof), statement)
        # Mathlib's `|a|` allows no space after the opening bar, so `| 0 =>` is a clause; an
        # unspaced clause-like line is ambiguous and is rejected rather than guessed.
        with self.assertRaisesRegex(ValueError, "e: Ambiguous `\\|`"):
            display("theorem e : ∀ n : ℕ, n = n\n  |0 => rfl\n  |_ => rfl")

    def test_shared_scanner_self_check(self):
        proof_lengths.self_check()

    def test_attributed_theorems_strip_proofs_and_injectivity_helpers(self):
        attribute = '@[deprecated (since := "2026-10-23")]\n'
        sample = "def encX := f\n\n" + attribute + (
            "theorem encX_injective : Function.Injective encX := Bridge.proof\n\n") + attribute + (
            "lemma visible : P := Bridge.other_proof")
        output = abstract_to_tex.clean_code_for_display(sample)
        self.assertNotIn("encX_injective", output)
        self.assertNotIn("Bridge.", output)
        self.assertIn("lemma visible : P", output)
        self.assertEqual(abstract_to_tex.theorem_name(attribute + "theorem selected : P := proof"),
                         "selected")

    def test_wrapped_prose_is_one_paragraph_and_citation_keys_allow_whitespace(self):
        output = abstract_to_tex.render_tex_intro(
            "A machine has read-only input and write-only\noutput, with a polynomial bound.\n\n"
            "A separate paragraph.\n## References\n"
            "* [A. Author, *A paper*]\n  [Reference2026]\n")
        self.assertEqual(output[0],
                         "A machine has read-only input and write-only output, with a polynomial bound.")
        self.assertEqual(output[1], "A separate paragraph.")
        self.assertIn(r"\item{} A. Author, \emph{A paper} {\footnotesize (Reference2026)}", output)
        self.assertEqual(abstract_to_tex.escape_tex_prose("[A title]\n[Reference2026]"),
                         r"A title {\footnotesize (Reference2026)}")

    def test_render_tex_preserves_paragraph_boundaries_and_joins_wrapped_lines(self):
        sample = (
            "/-! # Title\n\nIntro.\n-/\n\nnamespace Foo\n\n"
            "/-! ## Section heading\n\n"
            "First section paragraph wrapped\nacross two source lines.\n\n"
            "Second section paragraph with *wrapped\nemphasis* before code.\n-/\n"
            "def sectionCode : Nat := 1\n\n"
            "/-- Preliminaries paragraph.\n\n"
            "**Bold lead.** Final explanatory paragraph wrapped\n"
            "across two lines for the declaration. -/\n"
            "theorem mainResult : sectionCode = 1 := rfl\n\n"
            "end Foo\n"
        )
        title, intro, sections = abstract_to_tex.parse_abstract(sample)
        rendered = abstract_to_tex.render_tex(title, intro, sections)
        self.assertIn(
            "First section paragraph wrapped across two source lines.\n\n"
            r"Second section paragraph with \emph{wrapped emphasis} before code.",
            rendered,
        )
        self.assertIn(
            "Preliminaries paragraph.\n\n"
            r"\textbf{Bold lead.} Final explanatory paragraph wrapped across two lines "
            "for the declaration.",
            rendered,
        )

    def test_only_injectivity_helpers_are_elided(self):
        sample = (
            "def encX : X → List Bool := f\n\n"
            "theorem encX_injective : Function.Injective encX :=\n  Bridge.encX_injective\n\n"
            "theorem other_fact : P :=\n  Bridge.other_fact\n\n"
            "theorem misnamed_injective : Q :=\n  Bridge.misnamed_injective"
        )
        self.assertEqual(
            abstract_to_tex.clean_code_for_display(sample),
            "def encX : X → List Bool := f\n\ntheorem other_fact : P\n\n"
            "theorem misnamed_injective : Q",
        )

    def test_reference_bullets_cannot_become_tex_item_labels(self):
        rendered = "\n".join(abstract_to_tex.render_tex_intro(
            "## References\n\n* [S. Arora, B. Barak, *Computational Complexity*][AroraBarak09]"
        ))
        self.assertIn(r"\item{} S. Arora, B. Barak,", rendered)
        self.assertIn(r"\emph{Computational Complexity}", rendered)
        self.assertIn(r"{\footnotesize (AroraBarak09)}", rendered)

    def test_wrapped_reference_stays_in_its_list_item(self):
        rendered = "\n".join(abstract_to_tex.render_tex_intro(
            "## References\n\n* [S. A. Cook, R. A. Reckhow, *The relative efficiency of\n"
            "  propositional proof systems*][CookReckhow1979]\n\n"
            "* [A. Haken, *The intractability of resolution*][Haken1985]\n"
        ))
        self.assertIn(r"\emph{The relative efficiency of propositional proof systems}", rendered)
        self.assertEqual(rendered.count(r"\begin{itemize}"), 1)
        self.assertEqual(rendered.count(r"\item{}"), 2)

    def test_section_heading_and_machine_name_can_wrap(self):
        machine = "Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength"
        rendered = abstract_to_tex.render_tex("Title", "", [{
            "kind": "section",
            "doc": f"## Polynomial-time computability, NP, coNP, and completeness\n\n"
                   f"In upstream `Cslib`, `{machine}` means a halting machine.",
            "code": "",
        }])
        self.assertIn("\\subsubsection*{Polynomial-time computability, NP, coNP, "
                      "and completeness}\n\nIn upstream", rendered)
        self.assertIn(r"Turing.\allowbreak{}Multi\allowbreak{}Tape\allowbreak{}TM.\allowbreak{}"
                      r"Computable\allowbreak{}In\allowbreak{}Time", rendered)
        self.assertNotIn(r"\paragraph{", rendered)

    def test_catalogue_symbols_and_author_names_are_pdflatex_safe(self):
        sample = "∏ ∑ ⊥ ⊤ χ π ρ μ ν ι ℓ ∞ ⨅ ⨆ ≃ Σ ⦃x⦄ ⌈x⌉₊ x₀ x₁ x₂ xₖ f⁻¹ x⁰ x² x³ x⁵ x⁹ ∑ˢ ⋃ ⊂ ·"
        rendered = abstract_to_tex.escape_tex_code_line(sample)
        self.assertTrue(rendered.isascii())
        for command in (r"\prod", r"\sum", r"\bot", r"\top", r"\chi", r"\infty", r"^{0}"):
            self.assertIn(command, rendered)
        self.assertEqual(abstract_to_tex.escape_tex_prose("AC⁰ circuits"), r"AC$^{0}$ circuits")
        self.assertEqual(abstract_to_tex.escape_tex_prose("Håstad, Erdős, Bonami–Beckner"),
                         r"H\r{a}stad, Erd\H{o}s, Bonami--Beckner")
        self.assertEqual(abstract_to_tex.escape_tex_prose("2^(n/24), {0,1}, $5 and ~n"),
                         r"2\textasciicircum{}(n/24), \{0,1\}, \$5 and \textasciitilde{}n")

    def test_floor_delta_omega_eventually_and_cdots_are_pdflatex_safe(self):
        sample = "d = ⌊log₂ ⌊log₂ n⌋⌋, Δ, ω(1), ∀ᶠ n in atTop, X_0 ⋯ X_{d-1}"
        for rendered in (abstract_to_tex.escape_tex_code_line(sample),
                         abstract_to_tex.escape_tex_prose(sample)):
            with self.subTest(rendered=rendered):
                self.assertTrue(rendered.isascii())
                for command in (r"\lfloor", r"\rfloor", r"\Delta", r"\omega",
                                r"^{\mathsf{f}}", r"\cdots"):
                    self.assertIn(command, rendered)

    def test_named_axiom_audits_are_stripped(self):
        sample = (
            "/-! # Title\n\nIntro.\n-/\n\nnamespace Foo\n\n"
            "/-- A result. -/\ntheorem result : True := by trivial\n\n"
            "/-- info: 'Foo.result' does not depend on any axioms -/\n"
            "#guard_msgs in\n#print axioms result\n\nend Foo\n"
        )
        title, intro, sections = abstract_to_tex.parse_abstract(sample)
        self.assertEqual(len(sections), 1)
        rendered = abstract_to_tex.render_markdown(title, intro, sections)
        self.assertIn("theorem result : True", rendered)
        self.assertNotIn("axioms", rendered)
        self.assertNotIn("guard_msgs", rendered)

    def test_guarded_audit_is_stripped(self):
        sample = (
            "/-! # Title\n\nIntro.\n-/\n\n"
            "namespace Foo\n\n"
            "/-- A definition. -/\ndef x : Nat := 0\n\n"
            "/--\ninfo: abstract audit passed for `Foo`: 1 root\ndeclarations, 0 dependencies"
            " checked\n-/\n#guard_msgs (whitespace := lax) in\n#check_abstract Foo\n\n"
            "end Foo\n"
        )
        _, _, sections = abstract_to_tex.parse_abstract(sample)
        self.assertEqual(len(sections), 1)
        self.assertEqual(sections[0]["code"], "def x : Nat := 0")

    def test_guarded_multiline_allowlist_is_stripped(self):
        sample = (
            "/-! # Title\n\nIntro.\n-/\n\n"
            "namespace Foo\n\n"
            "/-- A definition. -/\ndef x : Nat := 0\n\n"
            "/-- info: audit passed -/\n#guard_msgs in\n"
            "#check_abstract Foo allowing [\n"
            "  Complexity.First,\n  Complexity.Second\n]\n\n"
            "end Foo\n"
        )
        title, intro, sections = abstract_to_tex.parse_abstract(sample)
        self.assertEqual(len(sections), 1)
        self.assertEqual(sections[0]["code"], "def x : Nat := 0")
        for rendered in (
            abstract_to_tex.render_markdown(title, intro, sections),
            abstract_to_tex.render_tex(title, intro, sections),
        ):
            self.assertNotIn("Complexity.First", rendered)
            self.assertNotIn("Complexity.Second", rendered)
            self.assertNotIn("audit passed", rendered)

    @unittest.skipUnless(shutil.which("pdflatex"), "pdflatex not installed")
    def test_pdflatex_compiles_rendered_abstracts(self):
        tex_bodies = []
        for path in sorted(ABSTRACTS_DIR.glob("*Abstract.lean")):
            title, intro, sections = abstract_to_tex.parse_abstract(path.read_text())
            tex_bodies.append(abstract_to_tex.render_tex(title, intro, sections))

        document = "\n".join([
            r"\documentclass[11pt]{article}",
            r"\usepackage[T1]{fontenc}",
            r"\usepackage{lmodern}",
            r"\usepackage[margin=1in]{geometry}",
            r"\usepackage{microtype,amsmath,amssymb,xcolor,enumitem,titlesec}",
            r"\setlength{\parindent}{0pt}",
            r"\setlength{\parskip}{0.45em}",
            r"\begin{document}",
            r"\section{Formal Abstracts}",
            *tex_bodies,
            r"\end{document}",
            "",
        ])
        with tempfile.TemporaryDirectory(prefix="test-abstract-tex-") as tmpdir:
            tmp = Path(tmpdir)
            tex_file = tmp / "abstracts.tex"
            tex_file.write_text(document)
            proc = subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "abstracts.tex"],
                cwd=tmp,
                capture_output=True,
                text=True,
                errors="replace",  # TeX may log accented author names in its legacy font encoding.
                check=False,
            )
            self.assertEqual(
                proc.returncode,
                0,
                f"pdflatex failed:\n{proc.stdout[-2000:]}\n{proc.stderr[-2000:]}",
            )
            self.assertTrue((tmp / "abstracts.pdf").is_file())
            if shutil.which("pdftotext"):
                # Compilation succeeds even when bibliography labels and long identifiers
                # extend off the page. Check the actual glyph positions as well.
                bbox_file = tmp / "abstracts.html"
                subprocess.run(
                    ["pdftotext", "-bbox", str(tmp / "abstracts.pdf"), str(bbox_file)],
                    capture_output=True,
                    text=True,
                    check=True,
                )
                root = ET.parse(bbox_file).getroot()
                for page in root.findall(".//{*}page"):
                    page_width = float(page.attrib["width"])
                    for word in page.findall(".//{*}word"):
                        self.assertGreaterEqual(float(word.attrib["xMin"]), 36,
                                                f"Text clips the left margin: {word.text!r}")
                        self.assertLessEqual(float(word.attrib["xMax"]), page_width - 36,
                                             f"Text clips the right margin: {word.text!r}")


if __name__ == "__main__":
    unittest.main()
