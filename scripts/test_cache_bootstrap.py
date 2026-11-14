"""Cache-first build/check dispatch and retry behavior, without Lean or network access."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

REPO = Path(__file__).resolve().parent.parent
FAKE_FETCH = r'''#!/usr/bin/env python3
import json, os, sys
with open(os.environ["BOOTSTRAP_LOG"], "a") as log:
    log.write(json.dumps({"kind": "fetch", "cwd": os.getcwd()}) + "\n")
sys.exit(int(os.environ.get("BOOTSTRAP_FETCH_EXIT", "0")))
'''
# Stands in for scripts/full_check.py, whose steps test_full_check.py covers: it records its
# arguments and returns the status of one build, so a failing gate still fails check.sh.
FAKE_FULL_CHECK = r'''#!/usr/bin/env python3
import json, os, subprocess, sys
with open(os.environ["BOOTSTRAP_LOG"], "a") as log:
    log.write(json.dumps({"kind": "full", "args": sys.argv[1:]}) + "\n")
sys.exit(1 if subprocess.run(["lake", "build", "--wfail", "--iofail"]).returncode else 0)
'''
FAKE_LAKE = r'''#!/usr/bin/env python3
import json, os, pathlib, re, sys
args = sys.argv[1:]
with open(os.environ["BOOTSTRAP_LOG"], "a") as log:
    log.write(json.dumps({"kind": "lake", "args": args, "cwd": os.getcwd()}) + "\n")
if args[:3] == ["env", "lean", "--run"]:
    paths = json.load(sys.stdin)
    print(json.dumps([{"path": p, "imports": re.findall(r"^import (\S+)",
                     pathlib.Path(p).read_text(), re.M)} for p in paths]))
sys.exit(int(os.environ.get("BOOTSTRAP_BUILD_EXIT", "0")) if args[0] == "build" else 0)
'''


@unittest.skipUnless(shutil.which("git"), "git is required")
class CacheBootstrapTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="cache bootstrap ")
        self.addCleanup(temp.cleanup)
        self.temp = Path(temp.name).resolve()
        self.root = self.temp / "checkout"
        self.root.mkdir()
        self.log = self.temp / "events.jsonl"
        self.env = {k: v for k, v in os.environ.items()
                    if not k.startswith(("GIT_", "COMPLEXITYLIB_CACHE_", "BOOTSTRAP_"))
                    and k != "LAKE_CACHE_DIR"}
        self.env.update({"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
                         "GIT_AUTHOR_NAME": "Bootstrap fixture",
                         "GIT_COMMITTER_NAME": "Bootstrap fixture",
                         "GIT_AUTHOR_EMAIL": "bootstrap@example.invalid",
                         "GIT_COMMITTER_EMAIL": "bootstrap@example.invalid",
                         "BOOTSTRAP_LOG": str(self.log)})
        self.git("init", "-q")
        for name in ("scripts/build.sh", "scripts/check.sh", "scripts/quick_check.py",
                     "scripts/check_progress.py",
                     "scripts/cache/ensure.sh", "scripts/cache/bounded.py", "scripts/cache/restore.py", "scripts/cache/windows_job.py"):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(REPO / name, path)
        # These mini-checkouts exercise cache dispatch with only a Demo library. The real
        # manual preflight and its failure behavior are covered in test_quick_check.py, and the
        # cache-restore audit in test_check_cache_restores.py.
        for name in ("scripts/check_operator_manual.py", "scripts/test_operator_manual.py",
                     "scripts/check_vm_map_count.py", "scripts/check_cache_restores.py"):
            self.write(name, "raise SystemExit(0)\n")
        self.write("scripts/full_check.py", FAKE_FULL_CHECK)
        self.write("scripts/cache/get.sh", FAKE_FETCH).chmod(0o755)
        self.write(".gitignore", ".lake/\n__pycache__/\n")
        self.write("lean-toolchain", "leanprover/lean4:v4.36.0-rc1\n")
        self.write("lake-manifest.json", '{"packages": []}\n')
        self.write("lakefile.toml", 'name = "fixture"\n[[lean_lib]]\nname = "Demo"\n')
        self.write("Demo.lean", "import Demo.Base\nimport Demo.Client\n")
        self.write("Demo/Base.lean", "def value := 1\n")
        self.write("Demo/Client.lean", "import Demo.Base\ndef client := value\n")
        self.commit()
        self.git("update-ref", "refs/remotes/origin/main", "HEAD")
        bin_dir = self.temp / "bin"
        bin_dir.mkdir()
        lake = bin_dir / "lake"
        lake.write_text(FAKE_LAKE)
        lake.chmod(0o755)
        self.env["PATH"] = str(bin_dir) + os.pathsep + os.environ["PATH"]
        self.stamp = self.root / ".lake/cache-bootstrap/attempt.json"

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root,
                                       env=self.env, text=True).strip()

    def commit(self):
        self.git("add", ".")
        self.git("commit", "-qm", "fixture")

    def run_script(self, name, *args, **env):
        return subprocess.run([str(self.root / "scripts" / name), *args], cwd=self.temp,
                              env={**self.env, **env}, capture_output=True, text=True)

    def events(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()] \
            if self.log.exists() else []

    def fetch_count(self):
        return sum(event["kind"] == "fetch" for event in self.events())

    def assert_success(self, result):
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_build_restores_first_and_preserves_arguments_cwd_and_exit_status(self):
        arguments = ["--wfail", "--iofail", "+Demo.Client", "-Kexample=two words"]
        result = self.run_script("build.sh", *arguments, BOOTSTRAP_BUILD_EXIT="23")
        self.assertEqual(result.returncode, 23)
        fetch, build = self.events()
        self.assertEqual(fetch["kind"], "fetch")
        self.assertEqual(build["args"], ["build", *arguments])
        self.assertEqual(build["cwd"], str(self.root))

    def test_repeat_build_then_full_validation_reuses_attempt(self):
        self.assert_success(self.run_script("build.sh"))
        self.assert_success(self.run_script("build.sh", "Demo.Client"))
        self.assert_success(self.run_script("check.sh"))
        self.assertEqual(self.fetch_count(), 1)
        self.assertEqual([(e["kind"], e["args"]) for e in self.events()
                          if e["kind"] in ("full", "lake")][-2:], [
            ("full", ["--base", "origin/main"]), ("lake", ["build", "--wfail", "--iofail"])])

    def test_quick_check_restores_before_lean_header_inspection_and_build(self):
        self.write("Demo/Base.lean", "def value := 2\n")
        self.assert_success(self.run_script("check.sh", "--quick"))
        fetch, headers, build, aggregate = self.events()
        self.assertEqual(fetch["kind"], "fetch")
        self.assertEqual(headers["args"][:3], ["env", "lean", "--run"])
        self.assertTrue({"Demo.Base", "Demo.Client"} <= set(build["args"]))
        self.assertEqual(aggregate["args"], ["exe", "mk_all", "--check"])

    def test_quick_fallback_restores_once_and_preserves_failed_gate(self):
        self.write("README.md", "forces full validation\n")
        result = self.run_script("check.sh", "--quick", BOOTSTRAP_BUILD_EXIT="23")
        self.assertEqual(result.returncode, 1)
        self.assertIn("falls back", result.stdout)
        self.assertEqual(self.fetch_count(), 1)
        self.assertEqual([(e["kind"], e["args"]) for e in self.events()
                          if e["kind"] in ("full", "lake")][-2:], [
            ("full", ["--base", "origin/main"]), ("lake", ["build", "--wfail", "--iofail"])])

    def test_configuration_revision_endpoint_and_cache_directory_each_invalidate(self):
        self.assert_success(self.run_script("cache/ensure.sh"))
        count = 1
        for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", "lakefile.lean"):
            with self.subTest(name=name):
                path = self.root / name
                self.write(name, (path.read_text() if path.exists() else "") + "\n")
                self.assert_success(self.run_script("cache/ensure.sh"))
                count += 1
                self.assertEqual(self.fetch_count(), count)
        self.commit()
        self.assert_success(self.run_script("cache/ensure.sh"))
        count += 1
        self.assertEqual(self.fetch_count(), count)
        overrides = {}
        for key, value in (("COMPLEXITYLIB_CACHE_URLS", "https://mit.example.invalid https://gcp.example.invalid"),
                           ("COMPLEXITYLIB_CACHE_ORIGIN_TIMEOUT", "90"),
                           ("CACHE_RECOVERY_GENERATION", "recovery-1"),
                           ("COMPLEXITYLIB_CACHE_URL", "https://cache.example.invalid"),
                           ("LAKE_CACHE_DIR", str(self.temp / "other cache"))):
            overrides[key] = value
            self.assert_success(self.run_script("cache/ensure.sh", **overrides))
            count += 1
            self.assertEqual(self.fetch_count(), count)

    def test_working_proof_edits_do_not_trigger_another_download(self):
        initial = self.run_script("cache/ensure.sh")
        self.assert_success(initial)
        self.assertIn("attempting optional downloads", initial.stdout)
        self.assertIn("attempt finished in", initial.stdout)
        self.assertIn("does not certify a cache hit", initial.stdout)
        self.write("Demo/Base.lean", "def value := 2\n")
        repeated = self.run_script("cache/ensure.sh")
        self.assert_success(repeated)
        self.assertIn("skipping repeated attempt", repeated.stdout)
        self.assertIn("previous fetch exit 0", repeated.stdout)
        self.assertIn("does not certify a cache hit", repeated.stdout)
        self.assertEqual(self.fetch_count(), 1)

    def test_force_and_ten_minute_expiry_retry_same_checkout(self):
        self.assert_success(self.run_script("cache/ensure.sh"))
        self.assert_success(self.run_script("cache/ensure.sh", "--refresh"))
        self.assertEqual(self.fetch_count(), 2)
        stamp = json.loads(self.stamp.read_text())
        stamp["attempted_at"] -= 601
        self.stamp.write_text(json.dumps(stamp))
        self.assert_success(self.run_script("cache/ensure.sh"))
        self.assertEqual(self.fetch_count(), 3)

    def test_failed_fetch_falls_back_and_can_be_retried_explicitly(self):
        self.assert_success(self.run_script("build.sh", BOOTSTRAP_FETCH_EXIT="17"))
        repeated = self.run_script("build.sh", BOOTSTRAP_FETCH_EXIT="17")
        self.assert_success(repeated)
        self.assertIn("previous fetch exit 17", repeated.stdout)
        self.assertIn("does not certify a cache hit", repeated.stdout)
        self.assertEqual(self.fetch_count(), 1)
        self.assertEqual(json.loads(self.stamp.read_text())["fetch_exit_code"], 17)
        self.assert_success(self.run_script("cache/ensure.sh", "--refresh"))
        self.assertEqual(self.fetch_count(), 2)

    def test_opt_out_does_not_prevent_a_later_attempt(self):
        self.assert_success(self.run_script("build.sh", COMPLEXITYLIB_CACHE_AUTO="0"))
        self.assertEqual(self.fetch_count(), 0)
        self.assertFalse(self.stamp.exists())
        self.assert_success(self.run_script("build.sh"))
        self.assertEqual(self.fetch_count(), 1)

    def test_bootstrap_deadline_falls_back_to_the_strict_build(self):
        self.write("scripts/cache/get.sh", "#!/usr/bin/env python3\nimport time\ntime.sleep(30)\n").chmod(0o755)
        started = time.monotonic()
        result = self.run_script("build.sh", COMPLEXITYLIB_CACHE_BOOTSTRAP_TIMEOUT=".5",
                                 BOOTSTRAP_BUILD_EXIT="23")
        self.assertEqual(result.returncode, 23, result.stdout + result.stderr)
        self.assertLess(time.monotonic() - started, 6)
        self.assertEqual(json.loads(self.stamp.read_text())["fetch_exit_code"], 124)

    def test_unconfirmed_shutdown_never_overlaps_a_source_build(self):
        result = self.run_script("build.sh", BOOTSTRAP_FETCH_EXIT="125")
        self.assertEqual(result.returncode, 125, result.stdout + result.stderr)
        self.assertFalse(any(event["kind"] == "lake" for event in self.events()))

    @unittest.skipIf(sys.platform == "cygwin", "Windows job cancellation terminates all descendants atomically")
    def test_nested_shutdown_failure_survives_the_outer_bootstrap_deadline(self):
        self.write("scripts/cache/get.sh", '''#!/usr/bin/env python3
import os, pathlib, signal, sys, time
def stop(*_):
    pathlib.Path(os.environ["COMPLEXITYLIB_CACHE_SHUTDOWN_MARKER"]).touch()
    sys.exit(125)
signal.signal(signal.SIGTERM, stop)
time.sleep(30)
''').chmod(0o755)
        result = self.run_script("build.sh", COMPLEXITYLIB_CACHE_BOOTSTRAP_TIMEOUT=".5")
        self.assertEqual(result.returncode, 125, result.stdout + result.stderr)
        self.assertFalse(any(event["kind"] == "lake" for event in self.events()))

    def test_recovery_switch_skips_fetch_without_recording_a_stamp(self):
        self.assert_success(self.run_script("build.sh", DISABLE_CACHE_RESTORE="true"))
        self.assertEqual(self.fetch_count(), 0)
        self.assertFalse(self.stamp.exists())

    def test_invalid_arguments_do_not_fetch(self):
        for name in ("cache/ensure.sh", "check.sh"):
            with self.subTest(name=name):
                result = self.run_script(name, "--unknown")
                self.assertEqual(result.returncode, 2)
        self.assertEqual(self.events(), [])

    def test_ensure_checkout_flag_targets_external_worktree_without_local_scripts(self):
        external = self.temp / "external-worktree"
        external.mkdir()
        subprocess.check_call(["git", "init", "-q"], cwd=external, env=self.env)
        for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
            shutil.copy(self.root / name, external / name)
        subprocess.check_call(["git", "add", "."], cwd=external, env=self.env)
        subprocess.check_call(["git", "commit", "-qm", "ext"], cwd=external, env=self.env)
        self.assert_success(self.run_script("cache/ensure.sh", "--checkout", str(external)))
        events = self.events()
        self.assertEqual(len(events), 1)
        self.assertEqual(events[0]["kind"], "fetch")
        self.assertEqual(Path(events[0]["cwd"]).resolve(), external.resolve())
        self.assertTrue((external / ".lake/cache-bootstrap/attempt.json").is_file())
        self.assertFalse(self.stamp.exists())


if __name__ == "__main__":
    unittest.main()
