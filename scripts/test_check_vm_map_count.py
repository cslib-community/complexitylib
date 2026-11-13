"""Unit tests for `scripts/check_vm_map_count.py`."""

import io
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

try:
    import check_vm_map_count as vma
except ModuleNotFoundError:
    from scripts import check_vm_map_count as vma


SAMPLE_MAPS = """\
55d8f0000000-55d8f0020000 r-xp 00000000 fd:01 100 /elan/bin/lean
7f0000010000-7f0000020000 r-xp 00000000 fd:01 101 /usr/lib/libc.so.6
7f0000030000-7f0000035000 rw-p 00000000 fd:01 201 /repo/.lake/build/lib/lean/CslibFrontier/Foo.olean
7f0000040000-7f0000042000 rw-p 00000000 fd:01 202 /repo/.lake/build/lib/lean/CslibFrontier/Foo.olean.server
7f0000050000-7f0000058000 rw-p 00000000 fd:01 203 /repo/.lake/build/lib/lean/CslibFrontier/Foo.olean.private
7f0000060000-7f0000061000 rw-p 00000000 fd:01 204 /repo/.lake/build/lib/lean/CslibFrontier/Foo.ir.sig
7f0000070000-7f0000074000 rw-p 00000000 fd:01 205 /repo/.lake/build/lib/lean/CslibFrontier/Foo.ir
7ffdf0000000-7ffdf0021000 rw-p 00000000 00:00 0   [stack]
"""


class CheckVmMapCountTests(unittest.TestCase):
    def test_count_root_aggregate_imports_and_threshold(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "CslibFrontier.lean").write_text(
                "-- comment\nimport CslibFrontier.A\npublic import CslibFrontier.B\n\n",
                encoding="utf-8",
            )
            self.assertEqual(vma.count_root_aggregate_imports(root), 2)
            needed, count = vma.required_map_count(root)
            self.assertEqual(count, 2)
            self.assertGreaterEqual(needed, vma.DEFAULT_MIN_MAP_COUNT)

    def test_preflight_rejects_default_65530_limit_with_actionable_guidance(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "CslibFrontier.lean").write_text(
                "".join(f"import CslibFrontier.M{i}\n" for i in range(7000)),
                encoding="utf-8",
            )
            proc = root / "max_map_count"
            proc.write_text("65530\n", encoding="utf-8")
            out = io.StringIO()
            status = vma.preflight(root=root, out=out, proc_path=proc)
            self.assertEqual(status, 1)
            msg = out.getvalue()
            self.assertIn("65,530", msg)
            self.assertIn("failed to read file", msg)
            self.assertIn("vm.max_map_count=", msg)
            self.assertIn("--quick --no-full-fallback", msg)
            self.assertIn("do NOT modify host kernel settings", msg)

    def test_preflight_passes_when_limit_is_sufficient_or_non_linux(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "CslibFrontier.lean").write_text("import CslibFrontier.A\n", encoding="utf-8")
            proc = root / "max_map_count"
            proc.write_text("262144\n", encoding="utf-8")
            out = io.StringIO()
            self.assertEqual(vma.preflight(root=root, out=out, proc_path=proc), 0)
            self.assertEqual(out.getvalue(), "")
            missing = root / "absent_proc"
            self.assertEqual(vma.preflight(root=root, out=out, proc_path=missing), 0)

    def test_classify_maps_counts_all_five_module_artifacts(self):
        summary = vma.classify_maps(SAMPLE_MAPS)
        self.assertEqual(summary["total_vmas"], 8)
        self.assertEqual(summary[".olean"], 1)
        self.assertEqual(summary[".olean.server"], 1)
        self.assertEqual(summary[".olean.private"], 1)
        self.assertEqual(summary[".ir"], 1)
        self.assertEqual(summary[".ir.sig"], 1)
        self.assertEqual(summary[".so"], 1)
        self.assertEqual(summary["other"], 2)

    def test_measure_reports_breakdown_and_flags_insufficient_headroom(self):
        fake = subprocess.CompletedProcess(["lake"], 0, stdout=SAMPLE_MAPS, stderr="")
        with tempfile.TemporaryDirectory() as temp, \
             patch.object(vma, "measure_importer", return_value=fake):
            root = Path(temp)
            out_ok = io.StringIO()
            self.assertEqual(
                vma.run_measure(["CslibFrontierResults"], root=root, out=out_ok,
                                max_map_count=100_000),
                0,
            )
            self.assertIn("Child `lean` VMAs (`/proc/self/maps`): 8", out_ok.getvalue())
            out_low = io.StringIO()
            self.assertEqual(
                vma.run_measure(["CslibFrontierResults"], root=root, out=out_low,
                                max_map_count=10),
                1,
            )
            self.assertIn("measured 8 VMAs", out_low.getvalue())

    def test_measure_rejects_invalid_module_names(self):
        with self.assertRaises(ValueError):
            vma.measure_importer(["CslibFrontier; rm -rf /"])


if __name__ == "__main__":
    unittest.main()
