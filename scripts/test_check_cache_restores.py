"""Unit tests for scripts/check_cache_restores.py, with a real Lake regression test (#4523)."""

from __future__ import annotations

import io
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from contextlib import redirect_stderr, redirect_stdout
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_cache_restores as c  # noqa: E402
import quick_check as quick  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
LAKEFILE = """name = "restorefixture"
enableArtifactCache = true
restoreAllArtifacts = true

[[lean_lib]]
name = "Demo"

[[lean_lib]]
name = "DemoTests"
roots = []
globs = ["DemoTests.+"]

[[lean_exe]]
name = "tool"
srcDir = "tools"
root = "Tool"
"""


class ProcessAssertions:
    def assert_processes_stopped(self, pids: list[int], timeout: float = 1.0) -> None:
        """Wait until every PID is absent or unable to execute, retaining states in failures."""
        deadline = time.monotonic() + timeout
        while True:
            running = {pid: state for pid in pids
                       if (state := c._process_state(pid)) not in (None, "Z", "X")}
            if not running:
                return
            if time.monotonic() >= deadline:
                self.fail(f"child processes still running after cleanup: {running}")
            time.sleep(0.01)


class InterruptReadiness:
    """Signal this test's audit after two live Lean children, or abort with timeout evidence."""

    def __init__(self, root: Path, sig: signal.Signals, timeout: float = 60.0) -> None:
        self.root = root
        self.sig = sig
        self.timeout = timeout
        self.cancelled = threading.Event()
        self.thread = threading.Thread(target=self.run, daemon=True)
        self.pids: set[int] = set()
        self.observations: dict[str, object] = {}
        self.ready = False
        self.timed_out = False
        self.signal_at: float | None = None

    def observe(self) -> bool:
        live: set[int] = set()
        for name in ("slowa.pid", "slowb.pid"):
            observation: dict[str, object] = {}
            try:
                raw = (self.root / name).read_text(errors="replace")
                observation["contents"] = raw
                pid = int(raw.strip())
                if pid <= 0:
                    raise ValueError("PID must be positive")
                self.pids.add(pid)
                state = c._process_state(pid)
                observation.update(pid=pid, state=state)
                if state not in (None, "Z", "X"):
                    live.add(pid)
            except (ValueError, OSError) as error:
                observation["error"] = repr(error)
            self.observations[name] = observation
        return len(live) == 2

    def run(self) -> None:
        deadline = time.monotonic() + self.timeout
        while not self.cancelled.is_set():
            ready = self.observe()
            now = time.monotonic()
            self.timed_out = now >= deadline
            if ready or self.timed_out:
                self.ready = ready and not self.timed_out
                if not self.cancelled.is_set():
                    # On timeout this interrupts only our audit so it can clean up its workers.
                    # The caller must fail readiness, not count this as a successful signal test.
                    self.signal_at = time.monotonic()
                    # SIGTERM may still have its default handler if startup never reached
                    # the audit's handler installation. Use Python's interrupt on that path.
                    os.kill(os.getpid(), signal.SIGINT if self.timed_out else self.sig)
                return
            self.cancelled.wait(0.02)

    def stop(self) -> None:
        self.cancelled.set()
        if self.thread.ident is not None:
            self.thread.join(timeout=1)

    def cleanup_elapsed(self, finished: float) -> float:
        assert self.signal_at is not None, "no signal was sent"
        return finished - self.signal_at

    def diagnostics(self) -> str:
        return f"ready={self.ready}, timeout={self.timed_out}, PID observations={self.observations!r}"


class Fixture(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Restore fixture")
        self.git("config", "user.email", "restore@example.invalid")
        self.write(".gitignore", ".lake/\n")
        self.write("lakefile.toml", LAKEFILE)
        self.write("Demo.lean", "import Demo.Base\n")
        self.write("Demo/Base.lean", "def value : Nat := 1\n")
        self.write("DemoTests/Client.lean", "import Demo.Base\nexample : value = 1 := rfl\n")
        self.write("tools/Tool.lean", "def main : IO Unit := pure ()\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")

    def write(self, name: str, text: str) -> None:
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def git(self, *args: str) -> str:
        env = {**os.environ, "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}
        return subprocess.check_output(["git", *args], cwd=self.root, env=env, text=True).strip()

    def commit(self) -> None:
        self.git("add", ".")
        self.git("commit", "-qm", "fixture")

    def trace(self, module_path: str, **fields) -> None:
        self.write(f".lake/build/lib/lean/{module_path}.trace", json.dumps(fields))


@unittest.skipUnless(sys.platform == "linux" and hasattr(os, "fork"),
                     "Linux process states required")
class ProcessStateTests(ProcessAssertions, unittest.TestCase):
    def test_proc_stat_parser_handles_parentheses_and_non_utf8_command(self) -> None:
        self.assertEqual(c._parse_proc_stat_state(b"123 (bad\xff)name) S 1 2 3"), "S")
        self.assertIsNone(c._parse_proc_stat_state(b"123 malformed"))

    def test_unreadable_proc_state_uses_conservative_presence_fallback(self) -> None:
        with patch.object(Path, "read_bytes", side_effect=OSError("unreadable")):
            self.assertEqual(c._process_state(os.getpid()), "?")
            self.assertTrue(c._process_is_running(os.getpid()))

    def test_zombie_has_stopped_even_while_kill_zero_reports_it(self) -> None:
        pid = os.fork()
        if pid == 0:
            os._exit(0)
        try:
            deadline = time.monotonic() + 2.0
            while time.monotonic() < deadline and c._process_state(pid) != "Z":
                time.sleep(0.01)
            self.assertEqual(c._process_state(pid), "Z")
            os.kill(pid, 0)
            self.assertFalse(c._process_is_running(pid))
        finally:
            os.waitpid(pid, 0)

    def test_live_process_is_still_running(self) -> None:
        proc = subprocess.Popen(
            [sys.executable, "-c", "import time; time.sleep(30)"],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        try:
            self.assertTrue(c._process_is_running(proc.pid))
            with self.assertRaisesRegex(AssertionError, "still running"):
                self.assert_processes_stopped([proc.pid], timeout=0.05)
        finally:
            proc.terminate()
            proc.wait(timeout=5)


class RestoredFileTests(Fixture):
    def test_full_check_includes_unchanged_built_clients_and_executables(self) -> None:
        self.write("Demo/Committed.lean", "def committed := 1\n")
        self.commit()
        self.write("Demo/Staged.lean", "def staged := 1\n")
        self.git("add", "Demo/Staged.lean")
        self.write("DemoTests/Client.lean", "import Demo.Base\nexample : value = 1 := rfl -- edit\n")
        self.write("DemoTests/Untracked.lean", "example : 1 = 1 := rfl\n")
        self.write("DemoTests/Unbuilt.lean", "example : 2 = 2 := rfl\n")
        self.write("tools/Tool.lean", "def main : IO Unit := pure () -- edit\n")
        self.write("notes.md", "not Lean\n")
        for module in ("Demo/Committed", "Demo/Staged", "DemoTests/Untracked", "Tool"):
            self.trace(module, synthetic=True, log=[])
        self.trace("DemoTests/Client", log=[])  # built here: its log was replayed
        self.trace("Demo/Base", synthetic=True, log=[])  # unchanged sources are covered too
        self.assertEqual(c.restored_files(self.root),
                         ["Demo/Base.lean", "Demo/Committed.lean", "Demo/Staged.lean",
                          "DemoTests/Untracked.lean", "tools/Tool.lean"])

    def test_full_check_does_not_depend_on_changed_file_selection(self) -> None:
        self.trace("DemoTests/Client", synthetic=True, log=[])
        self.trace("Demo/Base", synthetic=True, log=[])
        (self.root / "Demo/Base.lean").unlink()
        self.write("lean-toolchain", "a different toolchain\n")
        self.assertEqual(c.restored_files(self.root), ["DemoTests/Client.lean"])

    def test_explicit_scope_covers_unchanged_client_and_missing_traces(self) -> None:
        self.trace("Demo/Base", synthetic=True, log=[])
        self.trace("DemoTests/Client", synthetic=True, log=[])
        self.assertEqual(c.restored_files(self.root, ["DemoTests/Client.lean", "tools/Tool.lean"]),
                         ["DemoTests/Client.lean", "tools/Tool.lean"])

    def test_full_check_includes_outputs_without_traces(self) -> None:
        self.write(".lake/build/lib/lean/DemoTests/Client.olean", "compiled output")
        self.assertEqual(c.restored_files(self.root), ["DemoTests/Client.lean"])

    def test_executable_scope_includes_built_helpers_without_expanding_library_scope(self) -> None:
        self.write("tools/Helper.lean", "import Demo.Base\n")
        for module in ("Demo/Base", "DemoTests/Client", "Tool", "Helper"):
            self.trace(module, synthetic=True, log=[])
        self.assertEqual(c.restored_files(self.root, ["Demo/Base.lean"], ["tools"]),
                         ["Demo/Base.lean", "tools/Helper.lean", "tools/Tool.lean"])

    def test_optional_aggregate_is_checked_only_when_built(self) -> None:
        self.assertEqual(c.restored_files(self.root, [], ["Demo.lean"]), [])
        self.write(".lake/build/lib/lean/Demo.olean", "compiled output")
        self.assertEqual(c.restored_files(self.root, [], ["Demo.lean"]), ["Demo.lean"])

    def test_paths_with_whitespace_are_preserved(self) -> None:
        self.write("Demo/has space\nand newline.lean", "example : True := trivial\n")
        self.trace("Demo/has space\nand newline", synthetic=True, log=[])
        self.assertEqual(c.restored_files(self.root), ["Demo/has space\nand newline.lean"])

    def test_unreadable_trace_counts_as_restored(self) -> None:
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.write(".lake/build/lib/lean/Demo/Base.trace", "{not json")
        self.assertEqual(c.restored_files(self.root), ["Demo/Base.lean"])

    def test_custom_source_directories_and_build_directory(self) -> None:
        self.write("lakefile.toml", 'name = "f"\nsrcDir = "src"\nbuildDir = "out"\n'
                   '[[lean_lib]]\nname = "Demo"\n[[lean_exe]]\nname = "t"\nsrcDir = "tools"\n')
        lib_dir, dirs = c.layout(self.root)
        self.assertEqual((lib_dir, dirs), (self.root / "out/lib/lean",
                                           [Path("src/tools"), Path("src")]))
        self.write("src/tools/Tool.lean", "def main : IO Unit := pure ()\n")
        self.write("out/lib/lean/Tool.trace", '{"synthetic": true}')
        self.assertEqual(c.trace_path("src/tools/Tool.lean", lib_dir, dirs),
                         self.root / "out/lib/lean/Tool.trace")
        self.assertIsNone(c.trace_path("Elsewhere/Tool.lean", lib_dir, dirs))
        self.assertEqual(c.restored_files(self.root), ["src/tools/Tool.lean"])


class MainTests(Fixture):
    def setUp(self) -> None:
        super().setUp()
        self.write("Demo/Base.lean", "def value : Nat := 2\n")
        self.trace("Demo/Base", synthetic=True, log=[])

    def run_main(self, returncode: int, output: str,
                 argv: list[str] | None = None) -> tuple[int, str, list[str]]:
        calls = []

        def elaborate(root, rel, **kwargs):
            calls.append(rel)
            return subprocess.CompletedProcess([], returncode, output)

        out, err = io.StringIO(), io.StringIO()
        with patch.object(c, "elaborate", side_effect=elaborate), \
             redirect_stdout(out), redirect_stderr(err):
            status = c.main(argv or [], self.root)
        return status, out.getvalue() + err.getvalue(), calls

    def test_clean_restored_file_passes(self) -> None:
        status, out, calls = self.run_main(0, "")
        self.assertEqual((status, calls), (0, ["Demo/Base.lean"]))
        self.assertIn("cleanly (1)", out)

    def test_any_output_fails_although_lean_exits_zero(self) -> None:
        warning = "warning: Demo/Base.lean:1:4: This line exceeds the 100 character limit"
        for output in (warning, "info: Demo/Base.lean:1:0: 2\n"):
            with self.subTest(output=output):
                status, out, _ = self.run_main(0, output)
                self.assertEqual(status, 1)
                self.assertIn("FAIL  Demo/Base.lean", out)
                self.assertIn(output.strip(), out)

    def test_failed_elaboration_fails(self) -> None:
        self.assertEqual(self.run_main(1, "")[0], 1)

    def test_progress_announces_count_and_current_file_before_elaboration(self) -> None:
        self.trace("DemoTests/Client", synthetic=True, log=[])
        out = io.StringIO()

        def elaborate(root, rel, **kwargs):
            self.assertIn(rel, out.getvalue())
            self.assertNotIn("cleanly", out.getvalue())
            return subprocess.CompletedProcess([], 0, "")

        with patch.object(c, "elaborate", side_effect=elaborate) as run, \
             patch.object(c.time, "monotonic", side_effect=[10, 10.5, 12, 17]), \
             redirect_stdout(out):
            self.assertEqual(c.main(["--progress", "--jobs", "1"], self.root), 0)
        self.assertEqual(run.call_count, 2)
        self.assertIn("checking 2 source(s) serially", out.getvalue())
        self.assertIn("[1/2]: Demo/Base.lean (elapsed 0.5s)", out.getvalue())
        self.assertIn("[2/2]: DemoTests/Client.lean (elapsed 2.0s)", out.getvalue())
        self.assertIn("cleanly (2) in 7.0s", out.getvalue())

    def test_parallel_progress_and_deterministic_failure_order(self) -> None:
        self.write("Demo/A.lean", "def a := 1\n")
        self.trace("Demo/A", synthetic=True, log=[])
        self.trace("DemoTests/Client", synthetic=True, log=[])
        second_finished = threading.Event()

        def elaborate(root, rel, **kwargs):
            if rel == "Demo/A.lean":
                self.assertTrue(second_finished.wait(timeout=5))
                return subprocess.CompletedProcess([], 0, "warning: first file finished second\n")
            if rel == "Demo/Base.lean":
                second_finished.set()
                return subprocess.CompletedProcess([], 0, "warning: second file finished first\n")
            return subprocess.CompletedProcess([], 0, "")

        out, err = io.StringIO(), io.StringIO()
        with patch.object(c, "elaborate", side_effect=elaborate), \
             redirect_stdout(out), redirect_stderr(err):
            self.assertEqual(c.main(["--progress", "--jobs", "2"], self.root), 1)
        stdout = out.getvalue()
        self.assertIn("checking 3 source(s) with 2 worker(s).", stdout)
        self.assertLess(stdout.index("FAIL  Demo/A.lean"), stdout.index("FAIL  Demo/Base.lean"))
        self.assertNotIn("FAIL  DemoTests/Client.lean", stdout)
        self.assertIn("Re-elaborating 2 file(s)", err.getvalue())

    def test_ci_is_quiet_by_default_but_progress_can_be_requested(self) -> None:
        with patch.dict(os.environ, {"CI": "true"}):
            self.assertNotIn("Cache-restore audit", self.run_main(0, "")[1])
            self.assertIn("Cache-restore audit", self.run_main(0, "", ["--progress"])[1])
        with patch.dict(os.environ, {"CI": ""}):
            self.assertIn("Cache-restore audit", self.run_main(0, "")[1])
            self.assertNotIn("Cache-restore audit", self.run_main(0, "", ["--quiet"])[1])

    def test_quiet_does_not_hide_warnings_or_change_failure(self) -> None:
        status, out, calls = self.run_main(0, "warning: retained\n", ["--quiet"])
        self.assertEqual((status, calls), (1, ["Demo/Base.lean"]))
        self.assertNotIn("Cache-restore audit", out)
        self.assertIn("FAIL  Demo/Base.lean", out)
        self.assertIn("warning: retained", out)
        self.assertIn("Audit elapsed", out)

    def test_cancellation_does_not_continue_or_report_completion(self) -> None:
        self.trace("DemoTests/Client", synthetic=True, log=[])
        out = io.StringIO()
        with patch.object(c, "elaborate", side_effect=KeyboardInterrupt) as run, \
             redirect_stdout(out), self.assertRaises(KeyboardInterrupt):
            c.main(["--progress", "--jobs", "1"], self.root)
        self.assertEqual(run.call_count, 1)
        self.assertIn("[1/2]: Demo/Base.lean", out.getvalue())
        self.assertNotIn("[2/2]", out.getvalue())
        self.assertNotIn("cleanly", out.getvalue())

    def test_parallel_cancellation_terminates_active_children_and_skips_rest(self) -> None:
        for i in range(4):
            self.write(f"Demo/Extra{i}.lean", f"def e{i} := {i}\n")
            self.trace(f"Demo/Extra{i}", synthetic=True, log=[])
        both_started = threading.Barrier(2, timeout=5)
        calls: list[str] = []

        class FakePopen:
            def __init__(self_proc, cmd, **kwargs):
                self_proc.pid = 99999
                self_proc.returncode = 0
                self_proc._rel = cmd[-1].removeprefix("./")
                self_proc._killed = threading.Event()

            def __enter__(self_proc):
                return self_proc

            def __exit__(self_proc, *args):
                return False

            def communicate(self_proc):
                calls.append(self_proc._rel)
                both_started.wait()
                if self_proc._rel == "Demo/Base.lean":
                    raise KeyboardInterrupt
                self.assertTrue(self_proc._killed.wait(timeout=5))
                self_proc.returncode = -9
                return "", None

            def wait(self_proc):
                return self_proc.returncode

        out = io.StringIO()
        with patch.object(c.subprocess, "Popen", side_effect=FakePopen), \
             patch.object(c, "terminate_process", side_effect=lambda p: p._killed.set()) as term, \
             redirect_stdout(out), self.assertRaises(KeyboardInterrupt):
            c.main(["--progress", "--jobs", "2"], self.root)
        self.assertEqual(sorted(calls), ["Demo/Base.lean", "Demo/Extra0.lean"])
        self.assertEqual(term.call_count, 2)
        self.assertNotIn("cleanly", out.getvalue())

    def test_jobs_flag_env_override_and_validation(self) -> None:
        with patch.dict(os.environ, {}, clear=False):
            os.environ.pop(c.JOBS_ENV, None)
            os.environ.pop("LEAN_NUM_THREADS", None)
            with patch.object(c, "available_cpus", return_value=64):
                self.assertEqual(c.resolve_jobs(None), c.DEFAULT_JOBS_CAP)
                self.assertEqual(c.resolve_jobs(None, {"LEAN_NUM_THREADS": "2"}), 2)
                self.assertEqual(c.resolve_jobs(None, {"LEAN_NUM_THREADS": "16"}),
                                 c.DEFAULT_JOBS_CAP)
            with patch.object(c, "available_cpus", return_value=3):
                self.assertEqual(c.resolve_jobs(None), 3)
            with patch.object(c, "available_cpus", return_value=1):
                self.assertEqual(c.resolve_jobs(None), 1)
        with patch.dict(os.environ, {c.JOBS_ENV: "4", "LEAN_NUM_THREADS": "2"}):
            self.assertEqual(c.resolve_jobs(None), 4)
            self.assertEqual(c.resolve_jobs(3), 3)
        with patch.dict(os.environ, {c.JOBS_ENV: "  ", "LEAN_NUM_THREADS": ""}):
            with patch.object(c, "available_cpus", return_value=5):
                self.assertEqual(c.resolve_jobs(None), 5)
        for bad_cli in (0, -3):
            err = io.StringIO()
            with redirect_stderr(err):
                self.assertEqual(c.main(["--jobs", str(bad_cli)], self.root), 1)
            self.assertIn("--jobs must be >= 1", err.getvalue())
        for bad_env in ("0", "-1", "many"):
            err = io.StringIO()
            with patch.dict(os.environ, {c.JOBS_ENV: bad_env}), redirect_stderr(err):
                self.assertEqual(c.main([], self.root), 1)
            self.assertIn(c.JOBS_ENV, err.getvalue())
            self.assertNotIn("--jobs must be", err.getvalue())

    def test_worker_env_bounds_lean_threads_and_cleans_temp_setup_dir(self) -> None:
        parent_tmp = tempfile.TemporaryDirectory()
        self.addCleanup(parent_tmp.cleanup)
        seen: list[tuple[str | None, Path]] = []
        seen_lock = threading.Lock()

        class FakePopen:
            def __init__(self_proc, cmd, *, cwd, env, text, stdout, stderr):
                tmpdir = Path(env["TMPDIR"])
                self.assertTrue(tmpdir.is_dir())
                self.assertEqual(tmpdir.parent, Path(parent_tmp.name))
                self.assertEqual(env["TEMP"], str(tmpdir))
                self.assertEqual(env["TMP"], str(tmpdir))
                (tmpdir / "tmp.setup").write_text("{}")
                with seen_lock:
                    seen.append((env.get("LEAN_NUM_THREADS"), tmpdir))
                self_proc.returncode = 0

            def __enter__(self_proc):
                return self_proc

            def __exit__(self_proc, *args):
                return False

            def communicate(self_proc):
                return "", None

            def wait(self_proc):
                return 0

        with patch.dict(os.environ, {"LEAN_NUM_THREADS": "8", "TMPDIR": parent_tmp.name}), \
             patch.object(c.subprocess, "Popen", side_effect=FakePopen), \
             redirect_stdout(io.StringIO()):
            # Single restored file: `workers == 1`, so `LEAN_NUM_THREADS=8` is preserved.
            self.assertEqual(c.main(["--jobs", "4", "--quiet"], self.root), 0)
            # Two restored files with `--jobs 4`: `workers == 2`, so `LEAN_NUM_THREADS=1` is set.
            self.trace("DemoTests/Client", synthetic=True, log=[])
            self.assertEqual(c.main(["--jobs", "4", "--quiet"], self.root), 0)
            # Explicit `--jobs 1` on two restored files: `workers == 1`, keeping `8`.
            self.assertEqual(c.main(["--jobs", "1", "--quiet"], self.root), 0)
        self.assertEqual([threads for threads, _ in seen], ["8", "1", "1", "8", "8"])
        for _, tmpdir in seen:
            self.assertFalse(tmpdir.exists())

    def test_invalid_scope_fails_instead_of_becoming_an_empty_check(self) -> None:
        for contents in ('{"files": []}', '[1]', '["missing.lean"]', 'null', 'not JSON'):
            with self.subTest(contents=contents):
                scope = self.root / "scope.json"
                scope.write_text(contents)
                with redirect_stderr(io.StringIO()):
                    self.assertEqual(c.main(["--files-from", str(scope)], self.root), 1)

    def test_explicit_json_scope_excludes_unaffected_restores(self) -> None:
        self.trace("DemoTests/Client", synthetic=True, log=[])
        scope = self.root / "scope.json"
        scope.write_text(json.dumps(["DemoTests/Client.lean"]))
        with patch.object(c, "elaborate", return_value=subprocess.CompletedProcess([], 0, "")) as run, \
             redirect_stdout(io.StringIO()):
            self.assertEqual(c.main(["--files-from", str(scope)], self.root), 0)
        self.assertEqual(run.call_args.args, (self.root, "DemoTests/Client.lean"))


class InterruptReadinessTests(ProcessAssertions, Fixture):
    def test_delayed_second_child_does_not_use_up_cleanup_budget(self) -> None:
        self.write("slowa.pid", "101")
        self.write("slowb.pid", "partial")
        watcher = InterruptReadiness(self.root, signal.SIGTERM)
        clock = [0.0]

        def delayed_child(_timeout):
            self.assertIn("ValueError", watcher.diagnostics())
            self.assertEqual(watcher.pids, {101})
            clock[0] = 12.0  # A cold start longer than the old ten-second watchdog.
            self.write("slowb.pid", "102")

        with patch.object(time, "monotonic", side_effect=lambda: clock[0]), \
             patch.object(watcher.cancelled, "wait", side_effect=delayed_child), \
             patch.object(c, "_process_state", return_value="S"), \
             patch.object(os, "kill") as kill:
            watcher.run()
        self.assertTrue(watcher.ready)
        self.assertFalse(watcher.timed_out)
        self.assertEqual(watcher.cleanup_elapsed(12.5), 0.5)
        kill.assert_called_once_with(os.getpid(), signal.SIGTERM)

    def test_never_ready_retains_partial_pid_errors_and_process_state(self) -> None:
        self.write("slowa.pid", "101")
        self.write("slowb.pid", "partial")
        watcher = InterruptReadiness(self.root, signal.SIGTERM)
        clock = [0.0]

        def expire(_timeout):
            clock[0] = 61.0

        with patch.object(time, "monotonic", side_effect=lambda: clock[0]), \
             patch.object(watcher.cancelled, "wait", side_effect=expire), \
             patch.object(c, "_process_state", return_value="S"), \
             patch.object(os, "kill") as kill:
            watcher.run()
        self.assertTrue(watcher.timed_out)
        self.assertFalse(watcher.ready)
        self.assertEqual(watcher.pids, {101})
        for evidence in ("partial", "ValueError", "'state': 'S'"):
            self.assertIn(evidence, watcher.diagnostics())
        kill.assert_called_once_with(os.getpid(), signal.SIGINT)

    def test_dead_child_does_not_satisfy_readiness(self) -> None:
        self.write("slowa.pid", "101")
        self.write("slowb.pid", "102")
        watcher = InterruptReadiness(self.root, signal.SIGTERM)
        with patch.object(c, "_process_state", side_effect=["S", "Z"]):
            self.assertFalse(watcher.observe())
        self.assertEqual(watcher.observations["slowb.pid"]["state"], "Z")

    def test_same_pid_in_both_files_is_not_two_ready_children(self) -> None:
        self.write("slowa.pid", "101")
        self.write("slowb.pid", "101")
        watcher = InterruptReadiness(self.root, signal.SIGTERM)
        with patch.object(c, "_process_state", return_value="S"):
            self.assertFalse(watcher.observe())

    def test_cancelled_watcher_joins_without_signalling(self) -> None:
        watcher = InterruptReadiness(self.root, signal.SIGTERM)
        with patch.object(os, "kill") as kill:
            watcher.thread.start()
            watcher.stop()
        self.assertFalse(watcher.thread.is_alive())
        kill.assert_not_called()

    def test_early_audit_return_keeps_output_and_cancels_watcher(self) -> None:
        def fail_early(*_args):
            result = subprocess.run([sys.executable, "-c", "print('launcher diagnostic')"],
                                    capture_output=True, text=True, check=True)
            print(result.stdout)
            print("launcher failed before PID handshake")
            return 1

        with patch.object(c, "main", side_effect=fail_early), \
             patch.object(os, "kill") as kill, \
             self.assertRaisesRegex(AssertionError, "audit returned 1.*launcher failed") as error:
            RealLakeTests._assert_interrupt_cleans_up_descendants(self, signal.SIGTERM)
        kill.assert_not_called()
        self.assertIn("'returncode': 0", str(error.exception))
        self.assertIn("launcher diagnostic", str(error.exception))

    def test_early_audit_failure_reaps_its_live_owned_launcher(self) -> None:
        for mode in ("return", "raise"):
            with self.subTest(mode=mode):
                children = []

                def fail_early(*_args):
                    child = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(120)"])
                    children.append(child)
                    self.assertIsNone(child.poll(), "the control must leave a live owned child")
                    print("intentional live-launcher failure")
                    if mode == "raise":
                        raise RuntimeError("intentional audit exception")
                    return 1

                error_type = RuntimeError if mode == "raise" else AssertionError
                message = "intentional audit exception" if mode == "raise" else "audit returned 1"
                try:
                    with patch.object(c, "main", side_effect=fail_early), \
                         self.assertRaisesRegex(error_type, message) as error:
                        RealLakeTests._assert_interrupt_cleans_up_descendants(self, signal.SIGTERM)
                    self.assertIsNotNone(children[0].returncode, "fixture must reap its launcher")
                    self.assert_processes_stopped([children[0].pid])
                    # The diagnostic records the pre-rescue failure, not the cleaned-up state.
                    notes = "\n".join(getattr(error.exception, "__notes__", []))
                    self.assertIn("'returncode': None", str(error.exception) + notes)
                finally:
                    # Protect the test runner even when the regression is reintroduced.
                    for child in children:
                        if child.poll() is None:
                            child.kill()
                        child.wait(timeout=2)

    def test_timeout_fails_with_partial_diagnostics_and_joins_watcher(self) -> None:
        self.write("slowa.pid", "101")
        self.write("slowb.pid", "partial")
        interrupted = threading.Event()
        watchers = []
        watcher_class = InterruptReadiness

        def make_watcher(root, sig):
            watcher = watcher_class(root, sig, timeout=0.02)
            watchers.append(watcher)
            return watcher

        def audit(*_args):
            print("worker startup diagnostics")
            self.assertTrue(interrupted.wait(1), "watchdog failed to interrupt the owned audit")
            raise KeyboardInterrupt

        with patch.object(sys.modules[__name__], "InterruptReadiness", side_effect=make_watcher), \
             patch.object(c, "main", side_effect=audit), \
             patch.object(c, "_process_state", side_effect=lambda _pid:
                          None if interrupted.is_set() else "S"), \
             patch.object(os, "kill", side_effect=lambda *_args: interrupted.set()), \
             self.assertRaisesRegex(AssertionError, "readiness timeout.*partial.*worker startup"):
            RealLakeTests._assert_interrupt_cleans_up_descendants(self, signal.SIGTERM)
        self.assertFalse(watchers[0].thread.is_alive())


class IsolatedLakeFixture(Fixture):
    """A dependency-free project using the installed toolchain and a private artifact cache.

    CI's "Test Python tooling" step runs before Lean is installed, so CI skips this test; it runs
    in a local `scripts/check.sh` or `python3 -m unittest` with the repository's toolchain.
    """

    def setUp(self) -> None:
        # CI runs Python tests before installing Lean.
        if not shutil.which("lake"):
            self.skipTest("installed Lean toolchain unavailable")
        toolchain = (REPO / "lean-toolchain").read_text().strip()
        if shutil.which("elan"):
            listed = subprocess.run(["elan", "toolchain", "list"], capture_output=True, text=True)
            if toolchain not in listed.stdout:
                self.skipTest("repository Lean toolchain not installed")
        version = subprocess.run(["lake", "--version"], cwd=REPO, capture_output=True, text=True)
        if version.returncode or f"Lean version {toolchain.rsplit(':v', 1)[-1]})" not in version.stdout:
            self.skipTest("repository Lean toolchain not installed")
        super().setUp()
        self.write("lean-toolchain", toolchain + "\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        # A private artifact cache, so the test neither reads nor fills the machine's shared one.
        cache = tempfile.TemporaryDirectory()
        self.addCleanup(cache.cleanup)
        environment = patch.dict(os.environ, {"LAKE_CACHE_DIR": cache.name})
        environment.start()
        self.addCleanup(environment.stop)

    def lake(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(["lake", *args], cwd=self.root, capture_output=True, text=True,
                              timeout=120)


class RealLakeTests(ProcessAssertions, IsolatedLakeFixture):
    """Lake restores a warned module without its messages; the warning audit catches it."""

    def test_warning_dropped_by_a_cache_restore_is_reported(self) -> None:
        self.write("Demo/Base.lean", "theorem dropped : 1 = 2 := by sorry\n")
        first = self.lake("build", "--wfail", "--iofail", "Demo.Base")
        self.assertNotEqual(first.returncode, 0, first.stdout + first.stderr)
        for output in (self.root / ".lake/build").rglob("Base.*"):
            output.unlink()
        self.lake("build", "--wfail", "--iofail", "Demo.Base")  # restores from the cache
        trace = self.root / ".lake/build/lib/lean/Demo/Base.trace"
        if not c.restored(trace):
            self.skipTest("this Lake rebuilt the module instead of restoring it")
        out = io.StringIO()
        with redirect_stdout(out), redirect_stderr(out):
            self.assertEqual(c.main([], self.root), 1)
        self.assertIn("sorry", out.getvalue())

    def test_changed_import_makes_unchanged_restored_client_warn_in_full_and_quick_checks(self) -> None:
        self.write("Demo/Base.lean", "def value : Nat := 1\ndef oldValue : Nat := value\n")
        self.write("DemoTests/Client.lean", "import Demo.Base\nexample : Nat := oldValue\n")
        self.assert_unchanged_warning(
            'def value : Nat := 1\n@[deprecated value (since := "2026-11-11")]\n'
            'def oldValue : Nat := value\n', "DemoTests/Client.lean")

    def test_unchanged_aggregate_import_warning_is_checked(self) -> None:
        self.write("DemoTests/Client.lean", "import Demo\nexample : Nat := value\n")
        self.assert_unchanged_warning(
            'def value : Nat := 1\ndeprecated_module (since := "2026-11-11")\n', "Demo.lean")

    def assert_unchanged_warning(self, edited_base: str, warning_file: str) -> None:
        """A changed import can hide a warning in any unchanged source on a built client's path."""
        # Run quick mode's actual subprocess audit in this private project, stopping at its failure.
        for name in ("quick_check.py", "check_progress.py", "check_cache_restores.py", "QuickImports.lean"):
            self.write(f"scripts/{name}", (REPO / "scripts" / name).read_text())
        baseline = self.lake("build", "--wfail", "--iofail", "DemoTests.Client")
        self.assertEqual(baseline.returncode, 0, baseline.stdout + baseline.stderr)
        self.commit()  # include the generated manifest before measuring the Lean-only change
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        self.write("Demo/Base.lean", edited_base)
        populate = self.lake("build", "DemoTests.Client")
        self.assertEqual(populate.returncode, 0, populate.stdout + populate.stderr)
        self.assertIn("deprecated", populate.stdout + populate.stderr)
        self.assertEqual(self.git("diff", "--name-only"), "Demo/Base.lean")
        shutil.rmtree(self.root / ".lake/build")  # only this fixture's disposable outputs
        restored = self.lake("build", "--wfail", "--iofail", "DemoTests.Client")
        self.assertEqual(restored.returncode, 0, restored.stdout + restored.stderr)
        self.assertTrue(c.restored(self.root / ".lake/build/lib/lean/DemoTests/Client.trace"))
        for check in (c.main, quick.main):
            with self.subTest(check=check.__module__):
                out = io.StringIO()
                with redirect_stdout(out), redirect_stderr(out):
                    self.assertEqual(check([], self.root), 1, out.getvalue())
                self.assertIn("deprecated", out.getvalue())
                self.assertIn(f"FAIL  {warning_file}", out.getvalue())

    def test_parallel_real_lake_elaborates_concurrently_and_orders_failures(self) -> None:
        for index, peer in ((0, 1), (1, 0)):
            self.write(f"Demo/P{index}.lean", f"""import Lean.Elab.Command
#eval show Lean.Elab.Command.CommandElabM Unit from do
  if ← (System.FilePath.mk "barrier.arm").pathExists then
    let childTmp := (← IO.getEnv "TMPDIR").getD ""
    IO.FS.writeFile "p{index}.ready" childTmp
    let mut ready := false
    for _ in [:500] do
      if ← (System.FilePath.mk "p{peer}.ready").pathExists then
        ready := true
        break
      IO.sleep 20
    unless ready do
      Lean.logError "concurrent elaboration barrier timed out"
""")
        self.write("Demo.lean", "import Demo.P0\nimport Demo.P1\n")
        first = self.lake("build", "--wfail", "--iofail", "Demo.P0", "Demo.P1")
        self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
        shutil.rmtree(self.root / ".lake/build")
        restored = self.lake("build", "--wfail", "--iofail", "Demo.P0", "Demo.P1")
        self.assertEqual(restored.returncode, 0, restored.stdout + restored.stderr)
        for index in (0, 1):
            trace = self.root / f".lake/build/lib/lean/Demo/P{index}.trace"
            if not c.restored(trace):
                self.skipTest("this Lake rebuilt the module instead of restoring it")

        # Negative control: with `--jobs 1`, `P0` cannot rendezvous with `P1`.
        self.write("Demo/P0_short.lean", (self.root / "Demo/P0.lean").read_text().replace(
            "[:500]", "[:15]"))
        self.write("Demo/P1_short.lean", (self.root / "Demo/P1.lean").read_text().replace(
            "[:500]", "[:15]"))
        self.trace("Demo/P0_short", synthetic=True, log=[])
        self.trace("Demo/P1_short", synthetic=True, log=[])
        self.write("barrier.arm", "")
        short_scope = self.root / "short.json"
        short_scope.write_text(json.dumps(["Demo/P0_short.lean", "Demo/P1_short.lean"]))
        serial_out = io.StringIO()
        with redirect_stdout(serial_out), redirect_stderr(serial_out):
            self.assertEqual(
                c.main(["--files-from", str(short_scope), "--jobs", "1", "--quiet"], self.root), 1)
        self.assertIn("concurrent elaboration barrier timed out", serial_out.getvalue())
        for name in ("p0.ready", "p1.ready", "Demo/P0_short.lean", "Demo/P1_short.lean"):
            (self.root / name).unlink(missing_ok=True)
        for name in ("P0_short.trace", "P1_short.trace"):
            (self.root / ".lake/build/lib/lean/Demo" / name).unlink(missing_ok=True)

        # Positive parallel check: `P0` and `P1` elaborate simultaneously with no lock output
        # and leave no temporary `--setup` files behind.
        tmpdir = tempfile.TemporaryDirectory()
        self.addCleanup(tmpdir.cleanup)
        pair_scope = self.root / "pair.json"
        pair_scope.write_text(json.dumps(["Demo/P0.lean", "Demo/P1.lean"]))
        parallel_out = io.StringIO()
        with patch.dict(os.environ, {"TMPDIR": tmpdir.name}), \
             redirect_stdout(parallel_out), redirect_stderr(parallel_out):
            self.assertEqual(
                c.main(["--files-from", str(pair_scope), "--jobs", "2", "--quiet"], self.root), 0,
                parallel_out.getvalue())
        self.assertTrue((self.root / "p0.ready").is_file())
        self.assertTrue((self.root / "p1.ready").is_file())
        for index in (0, 1):
            recorded = Path((self.root / f"p{index}.ready").read_text())
            self.assertEqual(recorded.parent, Path(tmpdir.name))
            self.assertFalse(recorded.exists())
        self.assertEqual(list(Path(tmpdir.name).iterdir()), [])

        # Deterministic failure ordering across concurrent real Lake elaborations.
        self.write("Demo/WarnA.lean", """import Lean.Elab.Command
#eval show Lean.Elab.Command.CommandElabM Unit from do IO.sleep 150
theorem warnA : 1 = 2 := by sorry
""")
        self.write("Demo/WarnB.lean", "theorem warnB : 1 = 2 := by sorry\n")
        self.trace("Demo/WarnA", synthetic=True, log=[])
        self.trace("Demo/WarnB", synthetic=True, log=[])
        warn_scope = self.root / "warn.json"
        warn_scope.write_text(json.dumps(["Demo/WarnA.lean", "Demo/WarnB.lean"]))
        warn_out = io.StringIO()
        with redirect_stdout(warn_out), redirect_stderr(io.StringIO()):
            self.assertEqual(
                c.main(["--files-from", str(warn_scope), "--jobs", "2", "--quiet"], self.root), 1)
        self.assertLess(warn_out.getvalue().index("FAIL  Demo/WarnA.lean"),
                        warn_out.getvalue().index("FAIL  Demo/WarnB.lean"))

    def _assert_interrupt_cleans_up_descendants(self, sig: signal.Signals) -> None:
        for name in ("SlowA", "SlowB"):
            self.write(f"Demo/{name}.lean", f"""import Lean.Elab.Command
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let pid ← IO.Process.getPID
  IO.FS.writeFile "{name.lower()}.pid" (toString pid)
  IO.sleep 120000
""")
            self.trace(f"Demo/{name}", synthetic=True, log=[])
        scope = self.root / "slow_scope.json"
        scope.write_text(json.dumps(["Demo/SlowA.lean", "Demo/SlowB.lean"]))

        watcher = InterruptReadiness(self.root, sig)
        worker_results: dict[str, dict[str, object]] = {}
        launchers: list[subprocess.Popen] = []
        original_elaborate = c.elaborate
        original_popen = c.subprocess.Popen

        def record_launcher(*args, **kwargs):
            proc = original_popen(*args, **kwargs)
            launchers.append(proc)
            return proc

        def record_elaboration(root, rel, **kwargs):
            started = time.monotonic()
            worker_results[rel] = {"started_at": started}
            try:
                result = original_elaborate(root, rel, **kwargs)
            except BaseException as error:
                worker_results[rel].update(exception=repr(error),
                                           elapsed=time.monotonic() - started)
                raise
            worker_results[rel].update(returncode=result.returncode, output=result.stdout,
                                       elapsed=time.monotonic() - started)
            return result

        output = io.StringIO()
        failure: BaseException | None = None
        audit_result = None
        try:
            try:
                watcher.thread.start()
                with patch.object(c, "elaborate", side_effect=record_elaboration), \
                     patch.object(c.subprocess, "Popen", side_effect=record_launcher), \
                     redirect_stdout(output), redirect_stderr(output):
                    try:
                        audit_result = c.main(
                            ["--files-from", str(scope), "--jobs", "2", "--quiet"], self.root)
                    except BaseException as error:
                        failure = error
                finished = time.monotonic()
            finally:
                watcher.stop()
            launcher_states = {proc.pid: {"command": proc.args, "state": c._process_state(proc.pid),
                                         "returncode": proc.poll()} for proc in launchers}
            diagnostics = (f"{watcher.diagnostics()}; launchers={launcher_states!r}; "
                           f"worker results={worker_results!r}; "
                           f"audit output={output.getvalue()!r}")
            self.assertFalse(watcher.thread.is_alive(), diagnostics)
            if failure is not None and not isinstance(failure, KeyboardInterrupt):
                failure.add_note(diagnostics)
                raise failure
            self.assertIsInstance(failure, KeyboardInterrupt,
                                  f"audit returned {audit_result!r} before signal: {diagnostics}")
            self.assert_processes_stopped(sorted(watcher.pids | set(launcher_states)))
            self.assertTrue(watcher.ready,
                            f"readiness timeout before two live Lean children: {diagnostics}")
            elapsed = watcher.cleanup_elapsed(finished)
            self.assertLess(elapsed, 6.0, f"post-signal cleanup took {elapsed:.2f}s: {diagnostics}")
        finally:
            # Assess the audit before rescuing it: a production cleanup failure must still fail.
            # Only retained launcher handles (and their descendants) are cleanup targets, never
            # arbitrary integers read from PID files.
            original_error = sys.exc_info()[1]
            rescue_errors = []
            for proc in launchers:
                try:
                    if proc.poll() is None:
                        c.terminate_process(proc)
                    proc.wait(timeout=2)
                except Exception as error:
                    rescue_errors.append(f"launcher {proc.pid}: {error!r}")
            if rescue_errors:
                message = f"fixture-owned launcher rescue failed: {rescue_errors!r}"
                if original_error is not None:
                    original_error.add_note(message)
                else:
                    self.fail(message)

    def test_interrupt_watcher_is_cancelled_after_early_failure(self) -> None:
        with patch.object(c, "main", side_effect=RuntimeError("early failure")), \
             patch.object(os, "kill") as kill, \
             self.assertRaisesRegex(RuntimeError, "early failure"):
            self._assert_interrupt_cleans_up_descendants(signal.SIGTERM)
        kill.assert_not_called()

    @unittest.skipUnless(sys.platform == "linux", "Linux /proc required for descendant inspection")
    def test_parallel_real_lake_sigint_cleans_up_descendant_process_tree(self) -> None:
        self._assert_interrupt_cleans_up_descendants(signal.SIGINT)

    @unittest.skipUnless(sys.platform == "linux", "Linux /proc required for descendant inspection")
    def test_parallel_real_lake_sigterm_cleans_up_descendant_process_tree(self) -> None:
        self._assert_interrupt_cleans_up_descendants(signal.SIGTERM)


if __name__ == "__main__":
    unittest.main()
