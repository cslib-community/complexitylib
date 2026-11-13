"""Exercise live audit progress through both check runners, with real subprocesses."""

import io
from pathlib import Path
import shlex
import sys
import tempfile
import unittest
from contextlib import redirect_stdout
from unittest.mock import MagicMock, patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_progress as progress  # noqa: E402
import full_check as full  # noqa: E402
import quick_check as quick  # noqa: E402


CHILD = """
from pathlib import Path
import sys, time
root = Path(sys.argv[1])
print('retained diagnostic', flush=True)
print('Cache-restore audit: checking 1 source(s) serially.', flush=True)
deadline = time.monotonic() + 5
while not (root / 'seen').exists():
    if time.monotonic() > deadline:
        raise SystemExit(99)
    time.sleep(0.01)
print('Cache-restore audit [1/1]: Demo.lean (elapsed 0.1s)', flush=True)
(root / 'exited').touch()
raise SystemExit(int(sys.argv[2]))
"""


class ProgressTests(unittest.TestCase):
    def test_both_runners_stream_before_exit_and_preserve_failure_logs(self):
        for runner in ("full", "quick"):
            for exit_code in (0, 7):
                with self.subTest(runner=runner, exit_code=exit_code), \
                     tempfile.TemporaryDirectory() as temp, \
                     patch.object(tempfile, "tempdir", temp):
                    root = Path(temp)
                    test = self

                    class Output(io.StringIO):
                        def write(self, text):
                            if text.startswith("Cache-restore audit: checking"):
                                test.assertFalse((root / "exited").exists())
                                (root / "seen").touch()
                            return super().write(text)

                    out = Output()
                    command = [sys.executable, "-u", "-c", CHILD, str(root), str(exit_code)]
                    if runner == "full":
                        step = full.Step("audit", (shlex.join(command),), progress=True)
                        result = full.run_steps((step,), "unused", root=root, out=out)
                        self.assertEqual(result, int(bool(exit_code)))
                    else:
                        with redirect_stdout(out):
                            result = quick.run_check(root, command, "audit", progress=True)
                        self.assertEqual(result, exit_code)
                    self.assertIn("[1/1]: Demo.lean (elapsed 0.1s)", out.getvalue())
                    logs = list(root.rglob("*.log"))
                    if exit_code:
                        self.assertEqual(len(logs), 1)
                        self.assertIn("retained diagnostic", logs[0].read_text())
                        self.assertIn("Cache-restore audit", logs[0].read_text())
                        self.assertIn("FAIL  audit", out.getvalue())
                        self.assertIn("Full log", out.getvalue())
                    else:
                        self.assertEqual(logs, [])
                        self.assertNotIn("retained diagnostic", out.getvalue())
                        self.assertIn("ok    audit", out.getvalue())

    def test_interruption_reaps_child_and_propagates(self):
        child = MagicMock()
        child.__enter__.return_value = child
        child.stdout.__iter__.side_effect = KeyboardInterrupt
        with patch.object(progress.subprocess, "Popen", return_value=child), \
             self.assertRaises(KeyboardInterrupt):
            progress.run_logged(["unused"], log=io.BytesIO(), progress=io.StringIO())
        child.kill.assert_called_once()
        child.wait.assert_called_once()

    def test_full_audit_requests_progress_even_when_ci_is_set(self):
        step, = full.LOCAL_STEPS
        self.assertTrue(step.progress)
        self.assertIn("--progress", step.commands[0])


if __name__ == "__main__":
    unittest.main()
