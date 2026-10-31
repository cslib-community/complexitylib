"""Unit tests for scripts/check_hygiene.py."""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_hygiene  # noqa: E402
import proof_lengths  # noqa: E402


class CheckHygieneTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = pathlib.Path(self.tmp.name)
        (self.root / "Complexity").mkdir()
        (self.root / "ComplexityTests").mkdir()

    def write(self, rel: str, content: str) -> pathlib.Path:
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
        return p

    def test_clean_candidate_module_passes(self) -> None:
        p = self.write(
            "Complexity/Clean.lean",
            "module\n"
            "-- upstream: candidate\n\n"
            "-- Justified heartbeat bump for large polynomial ring normalizer.\n"
            "set_option maxHeartbeats 400000 in\n"
            "theorem demo : True := by\n"
            "  simp only [and_self]\n"
            "  simp +decide only [and_self]\n"
            "  simp (config := { decide := true }) only [and_self]\n"
            "  simp\n",
        )
        self.assertEqual(check_hygiene.check_file(p, root=self.root, check_simp=True), [])

    def test_missing_upstream_marker_fails(self) -> None:
        p = self.write("Complexity/NoMarker.lean", "module\ntheorem demo : True := trivial\n")
        errors = check_hygiene.check_file(p, root=self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("missing or invalid `-- upstream:` marker", errors[0])

    def test_upstream_marker_must_be_a_standalone_line_comment(self) -> None:
        examples = (
            '/- Example:\n-- upstream: candidate\n-/\n',
            '/- Outer /- nested -/\n-- upstream: candidate\n-/\n',
            'def text := "\n-- upstream: candidate\n"\n',
            'def text := r##"\n-- upstream: candidate\n"##\n',
            'def value := 0 -- upstream: candidate\n',
        )
        for example in examples:
            with self.subTest(example=example):
                p = self.write("Complexity/NoMarker.lean", "module\n" + example)
                self.assertEqual(check_hygiene.check_file(p, root=self.root),
                                 ["Complexity/NoMarker.lean: missing or invalid `-- upstream:` marker"])

    def test_standalone_upstream_status_forms_pass(self) -> None:
        statuses = ("candidate", "submitted #123 @deadbeef",
                    "vendored contributor:feature/api @deadbeef (unsubmitted)",
                    "merged @deadbeef", "local-only (test scaffolding)")
        for status in statuses:
            for indent in ("", "  "):
                with self.subTest(status=status, indent=indent):
                    p = self.write("Complexity/Marker.lean",
                                   f"module\n{indent}-- upstream: {status}\n")
                    self.assertEqual(check_hygiene.check_file(p, root=self.root), [])

    def test_candidate_marker_examples_do_not_enable_simp_check(self) -> None:
        for example in ('/-\n-- upstream: candidate\n-/\n',
                        'def text := r#"\n-- upstream: candidate\n"#\n'):
            with self.subTest(example=example):
                p = self.write(
                    "Complexity/Local.lean",
                    "module\n-- upstream: local-only (test scaffolding)\n" + example
                    + "theorem demo : True := by\n  simp\n  trivial\n",
                )
                self.assertEqual(check_hygiene.check_file(p, root=self.root, check_simp=True), [])

    def heartbeat_module(self, rel: str, value: int | str) -> pathlib.Path:
        return self.write(
            rel,
            "module\n"
            "-- upstream: candidate\n\n"
            "-- Justified: a large closed certificate.\n"
            f"set_option maxHeartbeats {value} in\n"
            "theorem demo : True := trivial\n",
        )

    def test_heartbeat_above_default_requires_allowlist(self) -> None:
        p = self.heartbeat_module("Complexity/Big.lean", 400000)
        errors = check_hygiene.check_file(p, root=self.root, heartbeat_caps={})
        self.assertEqual(len(errors), 1)
        self.assertIn("exceeds the 200000 default", errors[0])
        # The default itself, and smaller budgets, need no entry.
        q = self.heartbeat_module("Complexity/Default.lean", 200000)
        self.assertEqual(check_hygiene.check_file(q, root=self.root, heartbeat_caps={}), [])

    def test_heartbeat_allowlist_cap_is_enforced(self) -> None:
        p = self.heartbeat_module("Complexity/Big.lean", 400000)
        ok = {"Complexity/Big.lean": 400000}
        self.assertEqual(check_hygiene.check_file(p, root=self.root, heartbeat_caps=ok), [])
        low = {"Complexity/Big.lean": 300000}
        errors = check_hygiene.check_file(p, root=self.root, heartbeat_caps=low)
        self.assertEqual(len(errors), 1)
        self.assertIn("exceeds its allowlisted cap 300000", errors[0])

    def test_heartbeat_check_is_off_without_caps(self) -> None:
        p = self.heartbeat_module("Complexity/Big.lean", 400000)
        self.assertEqual(check_hygiene.check_file(p, root=self.root), [])

    def test_heartbeat_budget_in_a_comment_is_ignored(self) -> None:
        p = self.write(
            "Complexity/Commented.lean",
            "module\n-- upstream: candidate\n\n"
            "-- An earlier version used set_option maxHeartbeats 8000000 here.\n"
            "theorem demo : True := trivial\n",
        )
        self.assertEqual(check_hygiene.check_file(p, root=self.root, heartbeat_caps={}), [])

    def test_stale_heartbeat_allowlist_entries_are_reported(self) -> None:
        self.heartbeat_module("Complexity/Big.lean", 400000)
        self.heartbeat_module("Complexity/Small.lean", 100000)
        caps = {"Complexity/Big.lean": 500000, "Complexity/Small.lean": 400000,
                "Complexity/Gone.lean": 400000}
        errors = check_hygiene.check_heartbeat_allowlist_stale(caps, root=self.root)
        self.assertEqual(len(errors), 3)
        self.assertTrue(any("cap 500000 exceeds its largest budget 400000" in e for e in errors))
        self.assertTrue(any("`Complexity/Small.lean` has no budget above" in e for e in errors))
        self.assertTrue(any("`Complexity/Gone.lean` does not exist" in e for e in errors))
        exact = {"Complexity/Big.lean": 400000}
        self.assertEqual(check_hygiene.check_heartbeat_allowlist_stale(exact, root=self.root), [])

    def test_heartbeat_alternate_forms_are_checked(self) -> None:
        settings = [
            "set_option maxHeartbeats 400_000 in\ntheorem demo : True := trivial",
            "set_option maxHeartbeats 0x61A80 in\ntheorem demo : True := trivial",
            "set_option maxHeartbeats\n  400000 in\ntheorem demo : True := trivial",
            "theorem demo : True := by set_option maxHeartbeats 400000 in trivial",
            "example : True := by\n  skip; set_option maxHeartbeats 400000 in trivial",
        ]
        for setting in settings:
            with self.subTest(setting=setting):
                p = self.write("Complexity/Big.lean", "module\n-- upstream: candidate\n\n"
                               "-- Justified: closed certificate.\n" + setting + "\n")
                errors = check_hygiene.check_file(p, root=self.root, heartbeat_caps={})
                self.assertTrue(any("exceeds the 200000 default" in e for e in errors), errors)
                self.assertEqual(check_hygiene.check_file(
                    p, root=self.root, heartbeat_caps={"Complexity/Big.lean": 400000}), [])

    def test_zero_budget_requires_explicit_unlimited_cap(self) -> None:
        p = self.heartbeat_module("Complexity/Big.lean", 0)
        for caps in ({}, {"Complexity/Big.lean": 8000000}):
            with self.subTest(caps=caps):
                self.assertTrue(check_hygiene.check_file(p, root=self.root, heartbeat_caps=caps))
        caps = {"Complexity/Big.lean": 0}
        self.assertEqual(check_hygiene.check_file(p, root=self.root, heartbeat_caps=caps), [])
        self.assertEqual(check_hygiene.check_heartbeat_allowlist_stale(caps, self.root), [])
        self.heartbeat_module("Complexity/Big.lean", 400000)
        self.assertTrue(check_hygiene.check_heartbeat_allowlist_stale(caps, self.root))

    def test_unparsed_heartbeat_budget_fails_closed(self) -> None:
        for token in ("unlimited", "-1", "400000oops"):
            with self.subTest(token=token):
                p = self.heartbeat_module("Complexity/Big.lean", token)
                errors = check_hygiene.check_file(
                    p, root=self.root, heartbeat_caps={"Complexity/Big.lean": 0})
                self.assertTrue(any("cannot parse" in e for e in errors), errors)

    def test_inline_and_multiline_options_require_justification(self) -> None:
        for setting in ("example : True := by set_option maxHeartbeats 400000 in trivial",
                        "set_option maxRecDepth\n  1000 in\nexample : True := trivial"):
            with self.subTest(setting=setting):
                p = self.write("Complexity/Big.lean", "module\n-- upstream: candidate\n"
                               + "\n" * 5 + setting + "\n")
                errors = check_hygiene.check_file(p, root=self.root)
                self.assertTrue(any("justifying comment" in e for e in errors), errors)

    def test_options_in_interpolated_terms_are_checked(self) -> None:
        # Interpolation braces contain executable Lean terms, including tactic proofs.
        for option, value in (("maxHeartbeats", 400000), ("maxRecDepth", 1000)):
            with self.subTest(option=option):
                p = self.write(
                    "Complexity/Interpolation.lean",
                    "module\n-- upstream: candidate\n" + "\n" * 5
                    + f'def text := s!"{{(by set_option {option} {value} '
                    'in exact (0 : Nat))}"\n',
                )
                errors = check_hygiene.check_file(p, root=self.root, heartbeat_caps={})
                self.assertEqual(len(errors), 2 if option == "maxHeartbeats" else 1, errors)
                self.assertTrue(all(e.startswith("Complexity/Interpolation.lean:8:")
                                    for e in errors), errors)
                self.assertIn("requires a justifying comment", errors[0])
                if option == "maxHeartbeats":
                    self.assertIn("exceeds the 200000 default", errors[1])

    def test_heartbeat_allowlist_parsing(self) -> None:
        path = self.write("scripts/heartbeat_allowlist.txt",
                          "# header\n\nComplexity/Big.lean 400000  # see #1528\n")
        self.assertEqual(check_hygiene.load_heartbeat_allowlist(path),
                         {"Complexity/Big.lean": 400000})
        self.assertEqual(check_hygiene.load_heartbeat_allowlist(self.root / "missing.txt"), {})
        bad = self.write("scripts/bad.txt", "Complexity/Big.lean lots\n")
        with self.assertRaises(ValueError):
            check_hygiene.load_heartbeat_allowlist(bad)

    def test_unjustified_set_option_fails(self) -> None:
        p = self.write(
            "Complexity/UnjustifiedOption.lean",
            "module\n"
            "-- upstream: candidate\n\n"
            "\n\n\n"
            "set_option maxHeartbeats 400000 in\n"
            "theorem demo : True := trivial\n",
        )
        errors = check_hygiene.check_file(p, root=self.root)
        self.assertEqual(len(errors), 1)
        self.assertIn("requires a justifying comment", errors[0])

    def test_set_option_justified_on_the_next_line_passes(self) -> None:
        p = self.write(
            "Complexity/MathlibStyleOption.lean",
            "module\n"
            "-- upstream: candidate\n\n"
            "\n\n\n"
            "set_option maxHeartbeats 400000 in\n"
            "-- Mathlib's maxHeartbeats linter expects the reason on this line.\n"
            "theorem demo : True := trivial\n",
        )
        self.assertEqual(check_hygiene.check_file(p, root=self.root), [])

    def test_forbidden_tokens_and_nonterminal_simp(self) -> None:
        p = self.write(
            "Complexity/BadProof.lean",
            "module\n"
            "-- upstream: candidate\n\n"
            "axiom bad_ax : False\n"
            "theorem t1 : True := by\n"
            "  simp\n"
            "  exact trivial\n"
            "theorem t2 : True := by sorry\n",
        )
        errors = check_hygiene.check_file(p, root=self.root, check_simp=True)
        self.assertEqual(len(errors), 3)
        self.assertTrue(any("forbidden custom `axiom`" in e for e in errors))
        self.assertTrue(any("non-terminal bare `simp`" in e for e in errors))
        self.assertTrue(any("forbidden `sorry`" in e for e in errors))

    def test_quote_characters_do_not_hide_forbidden_theorem(self) -> None:
        for literal in ("'\"'", r"'\"'"):
            with self.subTest(literal=literal):
                p = self.write(
                    "Complexity/Quote.lean",
                    "module\n-- upstream: candidate\n"
                    f"def quote : Char := {literal}\n"
                    "theorem hole : True := by sorry\n"
                    f"def quoteAgain : Char := {literal}\n",
                )
                self.assertEqual(check_hygiene.check_file(p, root=self.root),
                                 ["Complexity/Quote.lean:4: forbidden `sorry`"])

    def test_character_masks_preserve_offsets_and_count_literal_proofs(self) -> None:
        literals = ("'a'", "'é'", "'😊'", "'('", "')'", "'['", "']'", "'{'", "'}'",
                    r"'\''", r"'\\'", r"'\n'", r"'\r'",
                    r"'\t'", r"'\x22'", r"'\u0022'")
        for literal in literals:
            with self.subTest(literal=literal):
                text = f"theorem quoted : {literal} = {literal} := by\n  rfl\n"
                code, syntax = proof_lengths.masks(text)
                self.assertEqual(code, text)
                self.assertEqual(len(syntax), len(text))
                self.assertEqual([i for i, c in enumerate(syntax) if c == "\n"],
                                 [i for i, c in enumerate(text) if c == "\n"])
                self.assertEqual(syntax.count("'"), 0)
                rows = proof_lengths.scan(text, "Complexity/Quote.lean")
                self.assertEqual([(row["name"], row["body_lines"]) for row in rows],
                                 [("quoted", 1)])

    def test_primed_identifiers_are_not_character_literals(self) -> None:
        names = ("lemma'a'", "lemma!'a'", "lemma?'a'", "α'a'")
        text = "\n".join(f"theorem {name} : True := True.intro" for name in names)
        code, syntax = proof_lengths.masks(text)
        self.assertEqual((code, syntax), (text, text))
        self.assertEqual([row["name"] for row in proof_lengths.scan(text, "Complexity/Prime.lean")],
                         list(names))

    def test_character_literal_text_in_strings_and_comments_is_ignored(self) -> None:
        p = self.write(
            "Complexity/QuotedText.lean",
            "module\n-- upstream: candidate\n"
            r'''def text := "'\"' sorry"''' + "\n"
            "-- '\"' sorry\n"
            "/- outer '\"' /- sorry -/ comment -/\n"
            "def quote : Char := '\"'\n"
            "theorem hole : True := by native_decide\n",
        )
        self.assertEqual(check_hygiene.check_file(p, root=self.root),
                         ["Complexity/QuotedText.lean:7: forbidden `native_decide`"])

    def test_docstring_markdown_links_and_module_paths_from_1358_and_1367(self) -> None:
        self.write(
            "Complexity/Computability/Circuit/Monotone/Clique/LogarithmicPetals.lean",
            "module\n-- upstream: candidate\n",
        )
        self.write(
            "Complexity/Computability/Circuit/Monotone/Clique/Asymptotic.lean",
            "module\n-- upstream: candidate\n",
        )
        self.write(
            "Complexity/Logics/Propositional/ClauseSet/Sparsification/Tree.lean",
            "module\n-- upstream: candidate\n",
        )

        # Before #1358: bare sibling `.html` link, root-relative `.lean` code spans, and brace-expanded paths.
        broken_1358 = self.write(
            "Complexity/Broken1358.lean",
            "module\n-- upstream: candidate\n"
            "/-!\n"
            "[LogarithmicPetals](LogarithmicPetals.html) gives stronger bounds.\n"
            "See `Monotone/Clique/Asymptotic.lean` and `Sparsification/Tree.lean`.\n"
            "Adapted from `LeanTrominoes/SAT/Planar/PlanarThreeSATGadgets.lean` and\n"
            "`SAT/ThreeSAT/PeriodicThreeSATThree{,Correctness,ExactSize}.lean`.\n"
            "-/\n",
        )
        errors_1358 = check_hygiene.check_file(broken_1358, root=self.root)
        self.assertEqual(len(errors_1358), 5, errors_1358)
        self.assertIn("Complexity/Broken1358.lean:4: invalid docstring Markdown link target `LogarithmicPetals.html`",
                      errors_1358[0])
        self.assertIn("Complexity/Broken1358.lean:5: invalid docstring module path `Monotone/Clique/Asymptotic.lean`",
                      errors_1358[1])
        self.assertIn("Complexity/Broken1358.lean:5: invalid docstring module path `Sparsification/Tree.lean`",
                      errors_1358[2])
        self.assertIn("Complexity/Broken1358.lean:6: invalid docstring module path `LeanTrominoes/SAT/Planar/PlanarThreeSATGadgets.lean`",
                      errors_1358[3])
        self.assertIn("Complexity/Broken1358.lean:7: invalid docstring module path `SAT/ThreeSAT/PeriodicThreeSATThree{,Correctness,ExactSize}.lean`",
                      errors_1358[4])

        # After #1358: root-qualified `Complexity/...` paths, external URLs, bare filenames without `/`, and dependency paths.
        fixed_1358 = self.write(
            "Complexity/Fixed1358.lean",
            "module\n-- upstream: candidate\n"
            "/-!\n"
            "[LogarithmicPetals](Complexity/Computability/Circuit/Monotone/Clique/LogarithmicPetals.html)\n"
            "gives stronger bounds than `Complexity/Computability/Circuit/Monotone/Clique/Asymptotic.lean`\n"
            "and `Complexity/Logics/Propositional/ClauseSet/Sparsification/Tree.lean` (`Game.lean`).\n"
            "Also see `Cslib/Foundations/Data/BitString.lean`, `Mathlib/Data/Nat/Log.lean`,\n"
            "[#anchor](#section-anchor), [decl](##SomeDecl), and\n"
            "[PlanarThreeSATGadgets.lean](https://github.com/edemaine/lean-trominoes/blob/6d5b36c15cec6cb18d30137b7f1c7fb92ea24332/LeanTrominoes/SAT/Planar/PlanarThreeSATGadgets.lean).\n"
            "-/\n",
        )
        self.assertEqual(check_hygiene.check_file(fixed_1358, root=self.root), [])

        # Before #1367: unescaped bracketed notation `MCSP-C[s](y)` parsed as a Markdown link.
        broken_1367 = self.write(
            "Complexity/Broken1367.lean",
            "module\n-- upstream: candidate\n"
            "/-!\n"
            "> • D is never incorrect. For each y, D(y) ∈ {MCSP-C[s](y), \"?\"}.\n"
            "-/\n",
        )
        errors_1367 = check_hygiene.check_file(broken_1367, root=self.root)
        self.assertEqual(len(errors_1367), 1, errors_1367)
        self.assertIn("Complexity/Broken1367.lean:4: invalid docstring Markdown link target `y`",
                      errors_1367[0])

        # After #1367: escaped `MCSP-C\[s\](y)`, math spans `$...[A, H](\lambda)$`, and inline code `` `MCSP-C[s](y)` ``.
        fixed_1367 = self.write(
            "Complexity/Fixed1367.lean",
            "module\n-- upstream: candidate\n"
            "-- Ordinary comment `Foo/Bar.lean` and MCSP-C[s](y) are not docstrings.\n"
            "/- Non-doc block comment `Foo/Bar.lean` and MCSP-C[s](y) -/\n"
            "/-!\n"
            "> • D is never incorrect. For each y, D(y) ∈ {MCSP-C\\[s\\](y), \"?\"}.\n"
            "Math span $\\mathsf{Adv}^{\\text{cr}}[\\mathcal{A}, H](\\lambda)$ and code `MCSP-C[s](y)`.\n"
            "Link with code label [`LeanTrominoes/SAT/Planar/PlanarThreeSATGadgets.lean`](https://example.com/file.lean).\n"
            "-/\n",
        )
        self.assertEqual(check_hygiene.check_file(fixed_1367, root=self.root), [])

    def test_docstring_reference_link_targets(self) -> None:
        self.write("Complexity/Init.lean", "module\n-- upstream: candidate\n")
        bad_targets = (
            "/Complexity/Init.lean",  # The reference-link gap reported in #1616.
            "Complexity/Init.lean",
            "Init.html",
            "Complexity/Missing.html#result",
            "Complexity/../Init.html",
            "mailto:example@example.com",
        )
        for target in bad_targets:
            for destination in (target, f"<{target}>"):
                with self.subTest(destination=destination):
                    p = self.write(
                        "Complexity/Reference.lean",
                        "module\n-- upstream: candidate\n/-!\nSee [consumer][adjacency].\n\n"
                        f"[adjacency]: {destination} 'Consumer'\n-/\n",
                    )
                    errors = check_hygiene.check_file(p, root=self.root)
                    self.assertEqual(len(errors), 1, errors)
                    self.assertIn(
                        f"Complexity/Reference.lean:6: invalid docstring Markdown link target `{target}`",
                        errors[0],
                    )

        good = self.write(
            "Complexity/Reference.lean",
            "module\n-- upstream: candidate\n/-!\n"
            "See [consumer][module], [external] and [anchor][].\n\n"
            "[module]: Complexity/Init.html#result \"Init\"\n"
            " [external]: <https://example.com/paper.pdf> (Paper)\n"
            "   [anchor]: #result\n"
            "[dependency]: Mathlib/Data/Nat/Basic.html\n"
            "[next-line]:\n  <Complexity/Init.html>\n"
            "-/\n",
        )
        self.assertEqual(check_hygiene.check_file(good, root=self.root), [])

    def test_reference_definitions_ignore_code_math_escapes_and_citation_prose(self) -> None:
        p = self.write(
            "Complexity/ReferenceExamples.lean",
            "module\n-- upstream: candidate\n/-!\n"
            "```markdown\n[example]: Missing.html\n```\n"
            "`[inline]: Missing.html`\n"
            "`multiline\n[code]: Missing.html\n`\n"
            "$$\n[math]: Missing.html\n$$\n"
            "\\[escaped]: Missing.html\n"
            "    [indented]: Missing.html\n"
            "`x`[not-a-definition]: Missing.html\n"
            "[AroraBarak09]: for each input, the theorem applies.\n"
            "[real]: Missing.html\n-/\n",
        )
        errors = check_hygiene.check_file(p, root=self.root)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("invalid docstring Markdown link target `Missing.html`", errors[0])
        self.assertIn(":18:", errors[0])

    def test_wrapped_citation_prose_is_not_a_reference_destination(self) -> None:
        p = self.write(
            "Complexity/CitationProse.lean",
            "module\n-- upstream: candidate\n/-!\n"
            "[AroraBarak09, Theorem 1]: if\n"
            "the hypothesis holds, the conclusion follows.\n\n"
            "[AroraBarak09]: the\n"
            "first part of the result.\n\n"
            "[AroraBarak09]: /Complexity/Init.lean\n"
            "[AroraBarak09]: <Missing>\n"
            "[ordinary-label]: Missing\n-/\n",
        )
        errors = check_hygiene.check_file(p, root=self.root)
        self.assertEqual(len(errors), 3, errors)
        self.assertIn("`/Complexity/Init.lean`", errors[0])
        self.assertIn("`Missing`", errors[1])
        self.assertIn("`Missing`", errors[2])

    def test_unmatched_backtick_does_not_hide_links_or_citations_in_later_paragraphs(self) -> None:
        doc = "Literal unmatched ` in prose.\n\n[broken]: Missing.html\n\n[Unknown2026]\n\nLater `code`."
        p = self.write(
            "Complexity/Paragraphs.lean",
            "module\n-- upstream: candidate\n/-!\n" + doc + "\n-/\n",
        )
        errors = check_hygiene.check_file(p, root=self.root)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("`Missing.html`", errors[0])
        self.assertEqual([key for _, key in check_hygiene.docstring_citations(doc)],
                         ["Unknown2026"])

    def test_reference_definition_next_line_and_dependency_existence(self) -> None:
        self.write(".lake/packages/mathlib/Mathlib/Existing.lean", "module\n")
        p = self.write(
            "Complexity/Reference.lean",
            "module\n-- upstream: candidate\n/-!\n"
            "[missing]:\n   <Mathlib/Missing.html>\n"
            "[existing]: Mathlib/Existing.html\n-/\n",
        )
        errors = check_hygiene.check_file(p, root=self.root)
        self.assertEqual(len(errors), 1, errors)
        self.assertIn("Complexity/Reference.lean:4:", errors[0])
        self.assertIn("target dependency module `Mathlib/Missing.lean` does not exist", errors[0])

    def test_docstring_nonexistent_complexity_module_or_fenced_code_path_fails(self) -> None:
        p = self.write(
            "Complexity/MissingTarget.lean",
            "module\n-- upstream: candidate\n"
            "/--\n"
            "Broken HTML target [Missing](Complexity/DoesNotExist.html#sec) and\n"
            "missing module `Complexity/AlsoMissing.lean`.\n"
            "```lean\n"
            "-- see Monotone/Clique/Asymptotic.lean\n"
            "```\n"
            "-/\n"
            "theorem demo : True := trivial\n",
        )
        errors = check_hygiene.check_file(p, root=self.root)
        self.assertEqual(len(errors), 3, errors)
        self.assertIn("Complexity/MissingTarget.lean:7: invalid docstring module path `Monotone/Clique/Asymptotic.lean`",
                      errors[0])
        self.assertIn("Complexity/MissingTarget.lean:4: invalid docstring Markdown link target `Complexity/DoesNotExist.html#sec`",
                      errors[1])
        self.assertIn("Complexity/MissingTarget.lean:5: invalid docstring module path `Complexity/AlsoMissing.lean`",
                      errors[2])

    def test_docstring_link_schemes_titles_and_angles(self) -> None:
        self.write("Complexity/Init.lean", "module\n-- upstream: candidate\n")

        # doc-gen4's `extendLink` prefixes `getRoot` to `mailto:` and `//`, so both must fail;
        # single-quoted/parenthesized titles with bad targets must also fail.
        bad = self.write(
            "Complexity/BadSchemesAndTitles.lean",
            "module\n-- upstream: candidate\n"
            "/-!\n"
            "Bad schemes: [me](mailto:a@b.c) and [proto](//example.com/y).\n"
            "Bad titled links: [s](Foo.html 'single') and [p](Bar.html (parens)).\n"
            "-/\n",
        )
        errors = check_hygiene.check_file(bad, root=self.root)
        self.assertEqual(len(errors), 4, errors)
        self.assertIn("Complexity/BadSchemesAndTitles.lean:4: invalid docstring Markdown link target `mailto:a@b.c`",
                      errors[0])
        self.assertIn("Complexity/BadSchemesAndTitles.lean:4: invalid docstring Markdown link target `//example.com/y`",
                      errors[1])
        self.assertIn("Complexity/BadSchemesAndTitles.lean:5: invalid docstring Markdown link target `Foo.html`",
                      errors[2])
        self.assertIn("Complexity/BadSchemesAndTitles.lean:5: invalid docstring Markdown link target `Bar.html`",
                      errors[3])

        # Angle-bracket targets and titled valid links pass.
        good = self.write(
            "Complexity/GoodAnglesAndTitles.lean",
            "module\n-- upstream: candidate\n"
            "/-!\n"
            "Angle target [init](<Complexity/Init.html>) and [titled](Complexity/Init.html 'Init').\n"
            "-/\n",
        )
        self.assertEqual(check_hygiene.check_file(good, root=self.root), [])


class BibliographyTests(unittest.TestCase):
    def test_sorted_unique_keys_pass(self) -> None:
        text = ("@article{arora2010,\n}\n\n@book{ AroraBarak09,\n  title = {A}\n}\n\n"
                "@misc{Sipser2013,\n  note = {@inline is not an entry}\n}\n")
        self.assertEqual(check_hygiene.check_bibliography(text), [])

    def test_unsorted_and_duplicate_keys_fail(self) -> None:
        text = "@book{Zed,\n}\n@book{alpha,\n}\n@misc{ZED,\n}\n"
        self.assertEqual(check_hygiene.check_bibliography(text), [
            "references.bib:5: duplicate key `ZED` (first at line 1)",
            "references.bib:3: entry `alpha` comes after `Zed`; keep entries sorted by key",
        ])

    def test_repository_bibliography_is_sorted(self) -> None:
        text = (check_hygiene.ROOT / "references.bib").read_text(encoding="utf-8")
        self.assertEqual(check_hygiene.check_bibliography(text), [])


class AbstractReadmeTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name)
        (self.root / "abstracts").mkdir()
        catalogue = {"entries": [
            {"id": "a", "module": "ComplexityAbstracts.AAbstract"},
            {"id": "b", "module": "ComplexityAbstracts.BAbstract"},
        ]}
        (self.root / "abstracts/catalogue.json").write_text(json.dumps(catalogue),
                                                            encoding="utf-8")

    def write_readmes(self, top: str, abstracts: str) -> None:
        (self.root / "README.md").write_text(top, encoding="utf-8")
        (self.root / "abstracts/README.md").write_text(abstracts, encoding="utf-8")

    def test_every_entry_listed_passes(self) -> None:
        self.write_readmes(
            "* [A](abstracts/ComplexityAbstracts/AAbstract.lean)\n"
            "* [B](abstracts/ComplexityAbstracts/BAbstract.lean); see also "
            "[A](abstracts/ComplexityAbstracts/AAbstract.lean) and the shared "
            "[encoding](abstracts/ComplexityAbstracts/Encoding.lean).\n",
            "| [A](ComplexityAbstracts/AAbstract.lean) |\n"
            "| [B](ComplexityAbstracts/BAbstract.lean) |\n",
        )
        self.assertEqual(check_hygiene.check_abstract_readmes(self.root), [])

    def test_missing_stale_and_misrooted_links_fail(self) -> None:
        self.write_readmes(
            "* [A](abstracts/ComplexityAbstracts/AAbstract.lean)\n"
            "* [C](abstracts/ComplexityAbstracts/CAbstract.lean)\n",
            "| [A](ComplexityAbstracts/AAbstract.lean) |\n"
            "| [B](abstracts/ComplexityAbstracts/BAbstract.lean) |\n",
        )
        self.assertEqual(check_hygiene.check_abstract_readmes(self.root), [
            "README.md: catalogue entry `b` is not listed; add a line linking "
            "`abstracts/ComplexityAbstracts/BAbstract.lean`",
            "README.md: links `abstracts/ComplexityAbstracts/CAbstract.lean`, which is not a "
            "catalogue entry of `abstracts/catalogue.json` (or uses the wrong relative path)",
            "abstracts/README.md: catalogue entry `b` is not listed; add a line linking "
            "`ComplexityAbstracts/BAbstract.lean`",
            "abstracts/README.md: links `abstracts/ComplexityAbstracts/BAbstract.lean`, which is "
            "not a catalogue entry of `abstracts/catalogue.json` (or uses the wrong relative path)",
        ])

    def test_malformed_catalogue_fails(self) -> None:
        (self.root / "abstracts/catalogue.json").write_text('{"entries": [{"id": "a"}]}',
                                                            encoding="utf-8")
        self.write_readmes("", "")
        errors = check_hygiene.check_abstract_readmes(self.root)
        self.assertEqual(len(errors), 1)
        self.assertTrue(errors[0].startswith("abstracts/catalogue.json: cannot read"))

    def test_repository_readmes_list_the_catalogue(self) -> None:
        self.assertEqual(check_hygiene.check_abstract_readmes(), [])


class CitationTests(unittest.TestCase):
    keys = frozenset({"AroraBarak09", "Ilango2020FOCS", "Sipser2013"})

    def citations(self, doc: str) -> list[str]:
        return [key for _, key in check_hygiene.docstring_citations(doc)]

    def test_citation_forms(self) -> None:
        doc = ("See [Sipser2013], [AroraBarak09, Theorem 2.1], [Ilango2020FOCS; Sipser2013] and\n"
               "[Arora and Barak, Section 3][AroraBarak09] or [*Title*, Section 4]\n"
               "  [Khrapchenko1971b]; [NISTFIPS203].")
        self.assertEqual(self.citations(doc), [
            "Sipser2013", "AroraBarak09", "Ilango2020FOCS", "Sipser2013", "AroraBarak09",
            "Khrapchenko1971b", "NISTFIPS203",
        ])

    def test_text_that_is_not_a_citation(self) -> None:
        doc = ("MCSP[s], [Section 4], [n], [x1], `xs[Foo2020]`, $v[Foo2020]$, \\[Foo2020\\],\n"
               "[Foo2020](https://example.com), ![Foo2020](image.png) and AC[2].\n"
               "> **Definition 43** (Average-case MCSP [HS17]). Quoted from the source.\n"
               "```lean\nexample := xs[Foo2020]\n```\n")
        self.assertEqual(self.citations(doc), [])

    def test_brackets_after_a_word_character_are_not_citations(self) -> None:
        # Indexing and subscripts written outside backticks; a bracket after `)` still counts.
        doc = ("xs[i10], H[SHA256], A_n[Foo2020], α[x10] and f(x)[Bar2021].\n[Sipser2013] (see\n"
               "[AroraBarak09]), \"[Ilango2020FOCS]\" and —[Baz2022].")
        self.assertEqual(self.citations(doc),
                         ["Bar2021", "Sipser2013", "AroraBarak09", "Ilango2020FOCS", "Baz2022"])

    def test_unknown_key_reports_file_line_and_key(self) -> None:
        # #1415 cited `[BussHay1991]` without a bibliography entry.
        raw = ("/-! # Title\n\nSee [Sipser2013].\n-/\n\n"
               "/-- Shown in [BussHay1991, Theorem 3] and [AroraBarak09]. -/\n"
               "theorem t : True := trivial\n"
               "-- [Comment2020] is not a docstring.\n")
        self.assertEqual(
            check_hygiene.check_docstring_citations(raw, pathlib.Path("Complexity/X.lean"),
                                                    self.keys),
            ["Complexity/X.lean:6: docstring cites `BussHay1991`, which is not a key in "
             "references.bib (add the entry, or escape the brackets `\\[...\\]` if it is not a "
             "citation)"])

    def test_check_file_checks_citations_only_with_keys(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            path = root / "ComplexityTests/X.lean"
            path.parent.mkdir()
            path.write_text("/-- [Missing2024] -/\ntheorem t : True := trivial\n",
                            encoding="utf-8")
            self.assertEqual(check_hygiene.check_file(path, root=root), [])
            errors = check_hygiene.check_file(path, root=root, bib_keys=self.keys)
            self.assertEqual(len(errors), 1)
            self.assertTrue(errors[0].startswith(
                "ComplexityTests/X.lean:1: docstring cites `Missing2024`"), errors)

    def test_bibliography_keys(self) -> None:
        text = "@book{ AroraBarak09,\n}\n@misc{Sipser2013,\n  note = {@inline{Not, a key}}\n}\n"
        self.assertEqual(check_hygiene.bibliography_keys(text),
                         frozenset({"AroraBarak09", "Sipser2013"}))


class CheckHygieneCLITests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = pathlib.Path(tmp.name).resolve()
        self.empty = self.root / "empty"
        self.empty.mkdir()
        self.clean = self.root / "Clean.lean"
        self.clean.write_text("theorem clean : True := trivial\n", encoding="utf-8")
        self.bad = self.root / "Bad.lean"
        self.bad.write_text("theorem bad : True := by sorry\n", encoding="utf-8")
        self.missing = self.root / "missing"

    def run_checker(self, *paths: pathlib.Path) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [sys.executable, "-B", str(pathlib.Path(check_hygiene.__file__)),
             *map(str, paths)],
            cwd=self.root, capture_output=True, text=True, check=False,
        )

    def test_empty_directory_fails_without_success_message(self) -> None:
        result = self.run_checker(self.empty)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, "")
        self.assertEqual(result.stderr, "ERROR: no source files found in selected paths\n")

    def test_missing_path_fails_without_traceback(self) -> None:
        result = self.run_checker(self.missing)
        self.assertEqual(result.returncode, 1)
        self.assertIn(f"ERROR: {self.missing}: input path does not exist\n", result.stderr)
        self.assertNotIn("Traceback", result.stderr)
        self.assertEqual(result.stdout, "")

    def test_empty_directory_does_not_hide_clean_file(self) -> None:
        for paths in ((self.clean,), (self.empty, self.clean)):
            with self.subTest(paths=paths):
                result = self.run_checker(*paths)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout, "All hygiene checks passed.\n")
                self.assertEqual(result.stderr, "")

    def test_mixed_selection_reports_both_missing_path_and_violation(self) -> None:
        result = self.run_checker(self.empty, self.missing, self.bad)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, "")
        self.assertIn(f"ERROR: {self.missing}: input path does not exist\n", result.stderr)
        self.assertIn(f"ERROR: {self.bad}:1: forbidden `sorry`\n", result.stderr)
        self.assertNotIn("no source files", result.stderr)
        self.assertNotIn("Traceback", result.stderr)

    def test_explicit_path_checks_citations_against_the_repository_bibliography(self) -> None:
        cited = self.root / "Cited.lean"
        cited.write_text("/-- [Sipser2013], [BussHay1991] -/\ntheorem t : True := trivial\n",
                         encoding="utf-8")
        result = self.run_checker(cited)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(result.stdout, "")
        self.assertIn(f"ERROR: {cited}:1: docstring cites `BussHay1991`", result.stderr)
        self.assertNotIn("Sipser2013", result.stderr)


if __name__ == "__main__":
    unittest.main()
