"""Exercise the Guide helper's failure propagation and output handling without Lean."""

import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]


class GuideGenerationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="guide generation ")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "scripts").mkdir()
        shutil.copyfile(ROOT / "scripts/guide.sh", self.root / "scripts/guide.sh")
        (self.root / "scripts/check_docs.py").write_text(
            "import os, sys\nsys.exit(int(os.environ.get('PIN_STATUS', '0')))\n")
        self.out = self.root / "guide/.lake/build/site"
        self.out.mkdir(parents=True)
        (self.out / "stale.html").write_text("previous output")
        self.bin = self.root / "bin"
        self.bin.mkdir()
        lake = self.bin / "lake"
        lake.write_text(f"#!{sys.executable}\n" + '''
import os
from pathlib import Path
import sys
args = sys.argv[1:]
with open('calls', 'a') as log:
    log.write(repr(args) + '\\n')
if 'build' in args:
    sys.exit(int(os.environ.get('BUILD_STATUS', '0')))
if 'lean' not in args or '--run' not in args:
    sys.exit('expected interpreted generation')
# Both Lake and Lean must receive the same existing source filename.
source = args[args.index('lean') + 1]
assert source == args[args.index('--run') + 1]
assert Path(source).is_file()
status = int(os.environ.get('RENDER_STATUS', '0'))
if status:
    sys.exit(status)
out = Path(args[args.index('--output') + 1]) / 'html-multi'
out.mkdir(parents=True)
(out / 'index.html').write_text('current output')
''')
        lake.chmod(0o755)
        (self.root / "guide/CslibFrontierGuideMain.lean").write_text("-- fixture")

    def run_helper(self, **env):
        return subprocess.run(["bash", str(self.root / "scripts/guide.sh")],
                              cwd=self.bin, text=True, capture_output=True,
                              env={**os.environ, "PATH": str(self.bin) + os.pathsep + os.environ["PATH"],
                                   **env})

    def test_runs_from_another_directory_and_replaces_old_pages(self):
        result = self.run_helper()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse((self.out / "stale.html").exists())
        self.assertEqual((self.out / "html-multi/index.html").read_text(), "current output")
        self.assertIn("Guide written to", result.stdout)

    def test_bad_pins_stop_before_lake_or_output_removal(self):
        result = self.run_helper(PIN_STATUS="23")
        self.assertEqual(result.returncode, 23)
        self.assertFalse((self.root / "calls").exists())
        self.assertTrue((self.out / "stale.html").is_file())

    def test_bad_chapters_stop_before_rendering_or_output_removal(self):
        result = self.run_helper(BUILD_STATUS="24")
        self.assertEqual(result.returncode, 24)
        self.assertEqual(len((self.root / "calls").read_text().splitlines()), 1)
        self.assertTrue((self.out / "stale.html").is_file())

    def test_generator_failure_is_not_reported_as_success(self):
        result = self.run_helper(RENDER_STATUS="25")
        self.assertEqual(result.returncode, 25)
        self.assertNotIn("Guide written to", result.stdout)
        self.assertFalse((self.out / "html-multi/index.html").exists())


if __name__ == "__main__":
    unittest.main()
