"""Report-only S4 scanner regressions: literals, primes, attributes and unknown targets."""

from __future__ import annotations

import contextlib
import io
import json
import os
import pathlib
import sys
import tempfile
import subprocess
import unittest
from unittest.mock import patch

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import check_tidy_usage as command
import quality_report as q


class TidyUsageTests(unittest.TestCase):
    def test_private_counts_use_types_not_names_and_exclude_generated_children(self):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "Source.lean"
            path.write_text("private theorem plainName : Raw f := proof\n"
                            "private theorem tidyNamed : Plain f := proof\n")
            source = q.Source(path)
            raw = {"m": "X", "tidy": ["Raw"], "r": [1, 0, 1, 42, 1, 16, 1, 25]}
            constants = {"_private.X.0.plainName": raw,
                         "_private.X.0.plainName.eq_1": raw,
                         "_private.X.0.generated": {**raw, "r": None},
                         "_private.X.0.tidyNamed": {**raw, "tidy": [],
                             "r": [2, 0, 2, 44, 2, 16, 2, 25]}}
            found = q.private_tidy_declarations(constants, lambda _: source)
            self.assertEqual([r["name"] for r in found["X"]], ["_private.X.0.plainName"])

    def test_bridges_mask_nested_comments_and_literals_but_keep_primed_identifiers(self):
        text = '''
/- h.tidy /- nested.of_tidy -/ -/
def s := "h.tidy"
def raw := r#"h.of_tidy"#
def char := '.'
theorem f' := h'.tidy
theorem g := ComputableInPolyTime.of_tidy h
theorem ignored := h.tidy' -- a different identifier
'''
        rows = q.tidy_source_signals(text, set())["bridges"]
        self.assertEqual(rows, [{"line": 6, "bridge": "tidy"},
                                {"line": 7, "bridge": "of_tidy"}])

    def test_inline_and_command_attributes_count_targets_not_commands(self):
        text = '''@[local fun_prop]
private theorem helper : Raw f := old
attribute [local fun_prop] helper Namespace.raw plain missing in
example : True := by trivial
@[fun_prop] theorem global : Raw g := old
-- attribute [local fun_prop] phantom
'''
        rows = q.tidy_source_signals(text, {"_private.X.0.helper", "Namespace.raw"},
                                     {"plain"})
        self.assertEqual([r["target"] for r in rows["local_tidy_fun_prop"]],
                         ["helper", "helper", "Namespace.raw"])
        self.assertEqual(rows["unresolved_local_fun_prop"], [{"line": 3, "target": "missing"}])

    def test_multiline_attributes_and_unknown_shape_remain_visible(self):
        text = '''@[simp, local fun_prop]
private lemma foo' : Raw f := old
@[local fun_prop]
macro "unknown" : term => `(True)
'''
        rows = q.tidy_source_signals(text, {"Ns.foo'"})
        self.assertEqual(rows["local_tidy_fun_prop"][0]["target"], "foo'")
        self.assertEqual(rows["unresolved_local_fun_prop"], [{"line": 3, "target": None}])

    def test_ambiguous_suffix_is_conservative(self):
        rows = q.tidy_source_signals("attribute [local fun_prop] rule", {"A.rule", "B.rule"})
        self.assertEqual(rows["local_tidy_fun_prop"][0]["candidates"], ["A.rule", "B.rule"])

    def test_multiline_attribute_targets_stop_at_next_command(self):
        text = "attribute [local fun_prop]\n  first\n  second in\nexample : True := by trivial"
        rows = q.tidy_source_signals(text, {"Ns.first", "Ns.second"})
        self.assertEqual([r["target"] for r in rows["local_tidy_fun_prop"]], ["first", "second"])

    def test_command_has_no_update_or_allow_increase_mode(self):
        for option in ("--update", "--allow-increase"):
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as e:
                command.main([option])
            self.assertEqual(e.exception.code, 2)

    def test_boundary_rejects_absolute_and_parent_paths(self):
        for prefix in ("/tmp/", "../Complexity/", "Complexity"):
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as e:
                command.main(["--internal-prefix", prefix])
            self.assertEqual(e.exception.code, 2)

    def test_positive_counts_do_not_fail_or_write_a_baseline(self):
        report = {"provenance": {"revision": "test"}, "internal_prefixes": [],
                  "modules": [], "totals": {"bridges": 100}, "notes": [],
                  "files_mentioning_tidy": 1}
        with patch.object(q, "check_outputs", return_value="unchecked"), \
                patch.object(q, "Library"), patch.object(q, "tidy_usage_report", return_value=report), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(command.main([]), 0)
        self.assertEqual(report["provenance"]["outputs"], "unchecked")


@unittest.skipUnless(os.environ.get("TIDY_USAGE_NATIVE") == "1",
                     "set TIDY_USAGE_NATIVE=1 for isolated Lean metadata fixtures")
class NativeMetadataTests(unittest.TestCase):
    def test_classic_and_split_private_metadata_and_incomplete_split_rejection(self):
        with tempfile.TemporaryDirectory(prefix="tidy-usage-native-") as directory:
            root = pathlib.Path(directory)
            for module, header in (("Classic", ""), ("Split", "module\n@[expose] public section\n")):
                src = root / (module + ".lean")
                src.write_text(header + "def ComputableTidilyProbe (_ : Nat) : Prop := True\n"
                               "private theorem hidden : ComputableTidilyProbe 0 := by trivial\n")
                subprocess.run(["lake", "env", "lean", "-R", str(root), str(src), "-o",
                                str(root / (module + ".olean")), "-i",
                                str(root / (module + ".ilean"))], cwd=q.ROOT, check=True,
                               capture_output=True, text=True)
            cmd = ["lake", "env", "lean", "--run", "scripts/QualityReport.lean", str(root)]
            result = subprocess.run(cmd, cwd=q.ROOT, input="Classic\nSplit\n", text=True,
                                    capture_output=True, check=True)
            rows = [json.loads(line) for line in result.stdout.splitlines()]
            hidden = [r for r in rows if r.get("n", "").endswith(".hidden")]
            self.assertEqual({r["m"] for r in hidden}, {"Classic", "Split"})
            self.assertTrue(all(r["tidy"] and r["r"] for r in hidden))
            (root / "Split.olean.server").unlink()
            failure = subprocess.run(cmd, cwd=q.ROOT, input="Split\n", text=True,
                                     capture_output=True)
            self.assertNotEqual(failure.returncode, 0)
            self.assertIn("incomplete split module outputs", failure.stderr)
            # Both missing parts must not be misread as a valid classic module either.
            (root / "Split.olean.private").unlink()
            failure = subprocess.run(cmd, cwd=q.ROOT, input="Split\n", text=True,
                                     capture_output=True)
            self.assertNotEqual(failure.returncode, 0)
            self.assertIn("incomplete split module outputs", failure.stderr)


if __name__ == "__main__":
    unittest.main()
