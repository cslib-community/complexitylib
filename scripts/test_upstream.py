#!/usr/bin/env python3
"""Regression tests for scripts/upstream.py using temporary checkouts only."""

from __future__ import annotations

import contextlib
import io
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import upstream  # noqa: E402


class UpstreamExportTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="test-upstream-")
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.repo = self.base / "complexitylib"
        self.cslib = self.base / "cslib"
        (self.repo / "CslibFrontier").mkdir(parents=True)
        (self.cslib / "Cslib").mkdir(parents=True)
        (self.cslib / "lakefile.toml").write_text('name = "cslib"\n', encoding="utf-8")

        self.write_local(
            "CslibFrontier/Init.lean",
            "module\n-- upstream: local-only (shim)\n",
        )
        self.write_local(
            "CslibFrontier/Foundations/SubmittedDep.lean",
            "module\n-- upstream: submitted #999 @deadbeef\n\npublic import CslibFrontier.Init\n",
        )
        self.write_local(
            "CslibFrontier/Foundations/CandidateDep.lean",
            "module\n-- upstream: candidate\n\npublic import CslibFrontier.Init\n",
        )

    def write_local(self, rel_path: str, content: str) -> Path:
        path = self.repo / rel_path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        return path

    def write_cslib(self, rel_path: str, content: bytes | str) -> Path:
        path = self.cslib / rel_path
        path.parent.mkdir(parents=True, exist_ok=True)
        if isinstance(content, bytes):
            path.write_bytes(content)
        else:
            path.write_text(content, encoding="utf-8")
        return path

    def run_upstream(self, *args: str) -> tuple[int, str, str]:
        stdout = io.StringIO()
        stderr = io.StringIO()
        code = 0
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            try:
                code = upstream.main(["--cslib", str(self.cslib), *args], root=self.repo)
            except SystemExit as exc:
                if isinstance(exc.code, int):
                    code = exc.code
                else:
                    code = 1
                    if exc.code:
                        print(exc.code, file=stderr)
        return code, stdout.getvalue(), stderr.getvalue()

    def test_new_module_export_rewrites_imports_refs_and_drops_marker(self) -> None:
        self.write_local(
            "CslibFrontier/Computability/NewModule.lean",
            "module\n"
            "-- upstream: candidate\n\n"
            "public import CslibFrontier.Init\n"
            "import CslibFrontier.Foundations.SubmittedDep\n\n"
            "/-!\n"
            "# New Complexity Module\n\n"
            "See `CslibFrontier.Foundations.SubmittedDep` and `CslibFrontier.NonExistent.Ref`.\n"
            "-/\n",
        )
        code, out, err = self.run_upstream("--no-mk-all", "CslibFrontier.Computability.NewModule")
        self.assertEqual(code, 0, out + err)
        self.assertEqual(err, "")
        dest = self.cslib / "Cslib/Computability/NewModule.lean"
        self.assertTrue(dest.is_file())
        exported = dest.read_text(encoding="utf-8")
        self.assertNotIn("-- upstream:", exported)
        self.assertIn("public import Cslib.Init\n", exported)
        self.assertIn("import Cslib.Foundations.SubmittedDep\n", exported)
        self.assertIn("`Cslib.Foundations.SubmittedDep`", exported)
        self.assertIn("`CslibFrontier.NonExistent.Ref`", exported)
        self.assertIn("suggested PR title: feat(Computability): new Complexity Module", out)

    def test_refuses_existing_destination_file_and_preserves_bytes(self) -> None:
        self.write_local(
            "CslibFrontier/Computability/Circuit/Program.lean",
            "module\n"
            "-- upstream: candidate\n\n"
            "public import CslibFrontier.Init\n"
            "public import Cslib.Computability.Circuit.Program\n",
        )
        original_bytes = b"-- upstream Cslib Program module\ndef upstreamDecl : Nat := 42\n"
        dest = self.write_cslib("Cslib/Computability/Circuit/Program.lean", original_bytes)

        code, out, err = self.run_upstream(
            "--no-mk-all",
            "CslibFrontier.Computability.Circuit.Program",
        )
        self.assertNotEqual(code, 0)
        self.assertIn("integrate additions", out + err)
        self.assertIn(str(dest), out + err)
        self.assertEqual(dest.read_bytes(), original_bytes)

    def test_header_rewrites_modifiers_comments_and_multiline_imports(self) -> None:
        text = (
            "module\n-- upstream: candidate\n"
            "public import CslibFrontier.Init -- keep this comment\n"
            "public /- explanation -/ meta import CslibFrontier.Foundations.SubmittedDep\n"
            "import all\n  CslibFrontier.Foundations.SubmittedDep\n"
            "meta import CslibFrontier.Init import CslibFrontier.Foundations.SubmittedDep\n"
        )
        self.write_local("CslibFrontier/Computability/Header.lean", text)
        code, out, err = self.run_upstream("--no-mk-all", "CslibFrontier.Computability.Header")
        self.assertEqual(code, 0, out + err)
        exported = (self.cslib / "Cslib/Computability/Header.lean").read_text()
        self.assertEqual(exported, text.replace("-- upstream: candidate\n", "")
                         .replace("CslibFrontier.", "Cslib."))

    def test_import_layout_cannot_bypass_dependency_check(self) -> None:
        for i, header in enumerate((
            "import CslibFrontier.Foundations.CandidateDep -- explanation\n",
            "meta import CslibFrontier.Foundations.CandidateDep\n",
            "public /- explanation -/ import\n  CslibFrontier.Foundations.CandidateDep\n",
            "import CslibFrontier.Init import CslibFrontier.Foundations.CandidateDep\n",
        )):
            with self.subTest(header=header):
                self.write_local(f"CslibFrontier/Computability/Blocked{i}.lean", "module\n" + header)
                code, out, err = self.run_upstream("--no-mk-all", f"CslibFrontier.Computability.Blocked{i}")
                self.assertNotEqual(code, 0, out + err)
                self.assertIn("CslibFrontier.Foundations.CandidateDep", err)
                self.assertFalse((self.cslib / f"Cslib/Computability/Blocked{i}.lean").exists())

    def test_comments_and_literals_do_not_create_imports_or_change_runtime_strings(self) -> None:
        text = (
            "module\npublic import CslibFrontier.Init\n"
            "/- An example, with /- a nested comment -/:\n"
            "import CslibFrontier.Foundations.CandidateDep\n-/\n"
            "/-!\n# Comments and literals\n"
            "See `CslibFrontier.Foundations.SubmittedDep`.\n-/\n"
            'def exampleText := r#"\n'
            "import CslibFrontier.Foundations.CandidateDep\n"
            "-- upstream: submitted #123\n"
            '`CslibFrontier.Foundations.SubmittedDep`\n"#\n'
            'def ordinary := "`CslibFrontier.Foundations.SubmittedDep`"\n'
        )
        self.write_local("CslibFrontier/Computability/Examples.lean", text)
        code, out, err = self.run_upstream("--no-mk-all", "CslibFrontier.Computability.Examples")
        self.assertEqual(code, 0, out + err)
        exported = (self.cslib / "Cslib/Computability/Examples.lean").read_text()
        self.assertEqual(exported, text.replace("public import CslibFrontier.Init", "public import Cslib.Init")
                         .replace("See `CslibFrontier.", "See `Cslib."))

    def test_dependency_marker_must_be_a_real_line_comment(self) -> None:
        self.write_local(
            "CslibFrontier/Foundations/CandidateDep.lean",
            "module\n/- Example marker:\n-- upstream: submitted #123\n-/\n"
            "-- upstream: candidate\n",
        )
        self.write_local(
            "CslibFrontier/Computability/Blocked.lean",
            "module\nimport CslibFrontier.Foundations.CandidateDep\n",
        )
        code, out, err = self.run_upstream("--no-mk-all", "CslibFrontier.Computability.Blocked")
        self.assertNotEqual(code, 0, out + err)
        self.assertIn("'candidate'", err)
        self.assertFalse((self.cslib / "Cslib/Computability/Blocked.lean").exists())

    def test_invalid_module_names_are_rejected_without_writing(self) -> None:
        self.write_local("CslibFrontier.lean", "module\n")
        for name in ("CslibFrontier", "CslibFrontier..Init", "CslibFrontier./Init", "CslibFrontier.Init/../Init"):
            with self.subTest(name=name):
                code, out, err = self.run_upstream("--no-mk-all", name)
                self.assertNotEqual(code, 0, out + err)
                self.assertIn("invalid module", err)
                self.assertEqual(list((self.cslib / "Cslib").rglob("*.lean")), [])

    def test_refuses_existing_valid_and_broken_symlinks(self) -> None:
        self.write_local(
            "CslibFrontier/Computability/Symlinked.lean",
            "module\n-- upstream: candidate\n\npublic import CslibFrontier.Init\n",
        )
        target = self.write_cslib("Cslib/Computability/Target.lean", "-- target content\n")
        dest = self.cslib / "Cslib/Computability/Symlinked.lean"
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.symlink_to(target)

        code, out, err = self.run_upstream("--no-mk-all", "CslibFrontier.Computability.Symlinked")
        self.assertNotEqual(code, 0)
        self.assertIn("integrate additions", out + err)
        self.assertTrue(dest.is_symlink())
        self.assertEqual(target.read_text(encoding="utf-8"), "-- target content\n")

        # Now test a broken symlink at the destination path.
        dest.unlink()
        dest.symlink_to(self.cslib / "Cslib/Computability/MissingTarget.lean")
        self.assertTrue(dest.is_symlink())
        self.assertFalse(dest.exists())

        code, out, err = self.run_upstream("--no-mk-all", "CslibFrontier.Computability.Symlinked")
        self.assertNotEqual(code, 0)
        self.assertIn("integrate additions", out + err)
        self.assertTrue(dest.is_symlink())
        self.assertFalse(dest.exists())

    def test_mixed_new_and_colliding_batch_writes_nothing(self) -> None:
        self.write_local(
            "CslibFrontier/Computability/FirstNew.lean",
            "module\n-- upstream: candidate\n\npublic import CslibFrontier.Init\n",
        )
        self.write_local(
            "CslibFrontier/Computability/SecondExisting.lean",
            "module\n-- upstream: candidate\n\npublic import CslibFrontier.Init\n",
        )
        existing_bytes = b"-- existing upstream file\n"
        existing_dest = self.write_cslib(
            "Cslib/Computability/SecondExisting.lean",
            existing_bytes,
        )
        new_dest = self.cslib / "Cslib/Computability/FirstNew.lean"

        code, out, err = self.run_upstream(
            "--no-mk-all",
            "CslibFrontier.Computability.FirstNew",
            "CslibFrontier.Computability.SecondExisting",
        )
        self.assertNotEqual(code, 0)
        self.assertFalse(new_dest.exists())
        self.assertEqual(existing_dest.read_bytes(), existing_bytes)
        self.assertIn("CslibFrontier.Computability.SecondExisting", out + err)
        self.assertIn("integrate additions", out + err)

    def test_mixed_batch_with_later_unmerged_dependency_writes_nothing(self) -> None:
        self.write_local(
            "CslibFrontier/Computability/FirstNew.lean",
            "module\n-- upstream: candidate\n\npublic import CslibFrontier.Init\n",
        )
        self.write_local(
            "CslibFrontier/Computability/SecondBlocked.lean",
            "module\n"
            "-- upstream: candidate\n\n"
            "public import CslibFrontier.Init\n"
            "import CslibFrontier.Foundations.CandidateDep\n",
        )
        new_dest = self.cslib / "Cslib/Computability/FirstNew.lean"

        code, out, err = self.run_upstream(
            "--no-mk-all",
            "CslibFrontier.Computability.FirstNew",
            "CslibFrontier.Computability.SecondBlocked",
        )
        self.assertNotEqual(code, 0)
        self.assertFalse(new_dest.exists())
        self.assertIn("CslibFrontier.Foundations.CandidateDep", err)

    def test_dry_run_reports_preview_and_collision_without_writing(self) -> None:
        self.write_local(
            "CslibFrontier/Computability/DryRunNew.lean",
            "module\n"
            "-- upstream: candidate\n\n"
            "public import CslibFrontier.Init\n\n"
            "/-!\n# Dry Run Module\n-/\n",
        )
        new_dest = self.cslib / "Cslib/Computability/DryRunNew.lean"

        code, out, err = self.run_upstream("--dry-run", "CslibFrontier.Computability.DryRunNew")
        self.assertEqual(code, 0, out + err)
        self.assertFalse(new_dest.exists())
        self.assertIn(str(new_dest), out)
        self.assertIn("suggested PR title: feat(Computability): dry Run Module", out)

        existing_bytes = b"-- untouched by dry-run\n"
        self.write_cslib("Cslib/Computability/DryRunNew.lean", existing_bytes)
        code, out, err = self.run_upstream("--dry-run", "CslibFrontier.Computability.DryRunNew")
        self.assertNotEqual(code, 0)
        self.assertIn("suggested PR title: feat(Computability): dry Run Module", out)
        self.assertIn("existing destination:", out)
        self.assertIn("integrate additions", out + err)
        self.assertEqual(new_dest.read_bytes(), existing_bytes)

    def test_cli_subprocess_invokes_mk_all_only_when_export_succeeds(self) -> None:
        script_copy = self.repo / "scripts/upstream.py"
        script_copy.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(Path(upstream.__file__), script_copy)
        shutil.copyfile(Path(upstream.__file__).with_name("proof_lengths.py"),
                        script_copy.with_name("proof_lengths.py"))

        bin_dir = self.base / "bin"
        bin_dir.mkdir()
        marker_file = self.base / "mk_all_invoked.txt"
        fake_lake = bin_dir / "lake"
        fake_lake.write_text(
            "#!/bin/sh\n"
            f'echo "$@" > "{marker_file}"\n',
            encoding="utf-8",
        )
        fake_lake.chmod(0o755)
        env = dict(os.environ, PATH=f"{bin_dir}:{os.environ.get('PATH', '')}")

        self.write_local(
            "CslibFrontier/Computability/CliMod.lean",
            "module\n-- upstream: candidate\n\npublic import CslibFrontier.Init\n",
        )
        res = subprocess.run(
            [sys.executable, str(script_copy), "--cslib", str(self.cslib), "CslibFrontier.Computability.CliMod"],
            cwd=self.repo,
            env=env,
            text=True,
            capture_output=True,
        )
        self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
        self.assertTrue((self.cslib / "Cslib/Computability/CliMod.lean").is_file())
        self.assertEqual(marker_file.read_text(encoding="utf-8").strip(), "exe mk_all")

        # Second run hits the now-existing destination and must not invoke `lake exe mk_all`.
        marker_file.unlink()
        res2 = subprocess.run(
            [sys.executable, str(script_copy), "--cslib", str(self.cslib), "CslibFrontier.Computability.CliMod"],
            cwd=self.repo,
            env=env,
            text=True,
            capture_output=True,
        )
        self.assertNotEqual(res2.returncode, 0)
        self.assertFalse(marker_file.exists())


if __name__ == "__main__":
    unittest.main()
