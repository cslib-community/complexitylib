"""Exercise bounded optional-cache retries using subprocesses, without Lean or network access."""

import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

REPO = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("get_mathlib", REPO / "scripts/cache/get_mathlib.py")
cache = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cache)

FAKE_LAKE = r'''#!/usr/bin/env python3
import json, os, pathlib, sys, time
args = sys.argv[1:]
artifacts = pathlib.Path(os.environ["MATHLIB_TEST_CACHE"])
artifacts.mkdir(exist_ok=True)
with open(os.environ["MATHLIB_TEST_LOG"], "a") as target:
    target.write(json.dumps({"args": args, "url": os.environ.get("MATHLIB_CACHE_GET_URL"),
                            "cwd": os.getcwd(), "existing": sorted(p.name for p in artifacts.iterdir())}) + "\n")
if args == ["exe", "cache", "get"]:
    mode = os.environ.get("MATHLIB_TEST_MODE", "success")
    if mode == "partial":
        first = artifacts / "first.ltar"
        if not first.exists():
            first.write_text("completed first archive")
            sys.exit(1)
        (artifacts / "second.ltar").write_text("completed second archive")
    elif mode == "fail":
        sys.exit(17)
    elif mode == "hang":
        time.sleep(30)
elif args[:1] == ["build"]:
    sys.exit(23)
'''


@unittest.skipUnless(os.name == "posix", "subprocess fixtures require POSIX executable scripts")
class MathlibCacheTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="mathlib-cache-retry-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.log = self.root / "events.jsonl"
        self.artifacts = self.root / "archives"
        bin_dir = self.root / "bin"
        bin_dir.mkdir()
        lake = bin_dir / "lake"
        lake.write_text(FAKE_LAKE)
        lake.chmod(0o755)
        self.env = {k: v for k, v in os.environ.items()
                    if not k.startswith(("MATHLIB_CACHE_", "COMPLEXITYLIB_CACHE_", "GIT_"))}
        self.env.update(PATH=str(bin_dir) + os.pathsep + os.environ["PATH"],
                        MATHLIB_TEST_LOG=str(self.log), MATHLIB_TEST_CACHE=str(self.artifacts),
                        GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")

    def events(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()]

    def restore(self, *, lean_action=False, **changes):
        with patch.object(cache, "RETRY_SECONDS", 0):
            return cache.restore(self.root, {**self.env, **changes}, lean_action)

    def test_partial_download_is_kept_and_only_ordinary_get_is_retried(self):
        self.assertTrue(self.restore(MATHLIB_TEST_MODE="partial"))
        events = self.events()
        self.assertEqual(len(events), 2)
        self.assertEqual([e["args"] for e in events], [["exe", "cache", "get"]] * 2)
        self.assertEqual([e["existing"] for e in events], [[], ["first.ltar"]])
        self.assertEqual((self.artifacts / "first.ltar").read_text(), "completed first archive")
        self.assertEqual((self.artifacts / "second.ltar").read_text(), "completed second archive")
        self.assertTrue(all(Path(e["cwd"]) == self.root for e in events))

    def test_success_does_not_retry(self):
        self.assertTrue(self.restore())
        self.assertEqual(len(self.events()), 1)

    def test_exhausted_failures_stop_after_three_attempts(self):
        self.assertFalse(self.restore(MATHLIB_TEST_MODE="fail"))
        self.assertEqual(len(self.events()), 3)

    def test_action_url_unset_empty_and_explicit_match_the_action(self):
        for supplied, expected in ((None, "https://cache.mathlib.org/mathlib4"),
                                   ("", None), ("https://cache.example.invalid", "https://cache.example.invalid")):
            with self.subTest(supplied=supplied):
                changes = {} if supplied is None else {"MATHLIB_CACHE_GET_URL": supplied}
                self.assertTrue(self.restore(lean_action=True, **changes))
                self.assertEqual(self.events()[-1]["url"], expected)

    def test_local_url_environment_is_unchanged(self):
        for supplied in (None, "", "https://cache.example.invalid"):
            with self.subTest(supplied=supplied):
                changes = {} if supplied is None else {"MATHLIB_CACHE_GET_URL": supplied}
                env = {**self.env, **changes, "COMPLEXITYLIB_CACHE_CHECKOUT": str(self.root),
                       "COMPLEXITYLIB_CACHE_URL": ""}
                result = subprocess.run([str(REPO / "scripts/cache/get.sh")], cwd=self.root,
                                        env=env, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(self.events()[-1]["url"], supplied)

    def test_get_script_keeps_relative_checkout_overrides(self):
        env = {**self.env, "COMPLEXITYLIB_CACHE_CHECKOUT": self.root.name,
               "COMPLEXITYLIB_CACHE_URL": ""}
        result = subprocess.run([str(REPO / "scripts/cache/get.sh")], cwd=self.root.parent,
                                env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(Path(self.events()[-1]["cwd"]), self.root)

    def test_timeout_stops_each_owned_process_before_retrying(self):
        created = []
        original = subprocess.Popen
        def start(*args, **kwargs):
            process = original(*args, **kwargs)
            created.append(process)
            return process
        with patch.object(cache, "ATTEMPT_SECONDS", .1), patch.object(cache.subprocess, "Popen", side_effect=start):
            self.assertFalse(self.restore(MATHLIB_TEST_MODE="hang"))
        self.assertEqual(len(created), 3)
        self.assertTrue(all(p.poll() is not None for p in created))

    @unittest.skipUnless(shutil.which("git"), "git is required for the real build wrapper")
    def test_cache_failure_still_runs_and_preserves_the_strict_build_failure(self):
        for name in ("scripts/build.sh", "scripts/cache/ensure.sh", "scripts/cache/get.sh",
                     "scripts/cache/get_mathlib.py"):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(REPO / name, target)
        for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
            (self.root / name).write_text("fixture\n")
        subprocess.run(["git", "init", "-q"], cwd=self.root, env=self.env, check=True)
        subprocess.run(["git", "-c", "user.name=Cache fixture", "-c",
                        "user.email=cache@example.invalid", "commit", "--allow-empty", "-qm", "fixture"],
                       cwd=self.root, env=self.env, check=True)
        env = {**self.env, "MATHLIB_TEST_MODE": "fail", "COMPLEXITYLIB_CACHE_URL": ""}
        result = subprocess.run([str(self.root / "scripts/build.sh"), "--wfail", "--iofail"],
                                cwd=self.root, env=env, capture_output=True, text=True)
        self.assertEqual(result.returncode, 23, result.stdout + result.stderr)
        self.assertIn("will compile missing outputs", result.stderr)
        self.assertEqual([e["args"] for e in self.events()],
                         [["exe", "cache", "get"]] * 3 + [["build", "--wfail", "--iofail"]])


class WorkflowWiringTests(unittest.TestCase):
    def test_only_optional_cache_step_is_relaxed_and_validation_remains(self):
        for name in ("lean_action_ci.yml", "docs.yml", "comparator.yml"):
            with self.subTest(workflow=name):
                text = (REPO / ".github/workflows" / name).read_text()
                action = text.split("      - uses: leanprover/lean-action@v1\n", 1)[1].split("      - ", 1)[0]
                self.assertRegex(action, r"use-mathlib-cache: [\"']false[\"']")
                self.assertNotIn("continue-on-error", action)
                step = text.split("      - name: Restore Mathlib cache with retries\n", 1)[1].split("      - ", 1)[0]
                self.assertIn("continue-on-error: true", step)
                self.assertIn("timeout-minutes: 10", step)
                self.assertIn("python3 -B scripts/cache/get_mathlib.py --lean-action", step)
        ci = (REPO / ".github/workflows/lean_action_ci.yml").read_text()
        for command in ("lake build --wfail --iofail", "lake test --wfail --iofail", "lake lint",
                        "lake exe mk_all --check", "lake exe lint-style", "lake exe checkInitImports"):
            self.assertIn(command, ci)
        docs = (REPO / ".github/workflows/docs.yml").read_text()
        self.assertLess(docs.index("run: scripts/cache/get-missing.sh"),
                        docs.index("      - name: Generate API documentation"))
        self.assertIn("DISABLE_EQUATIONS=1 lake -d docbuild build Complexity:docs", docs)

    def test_comparator_restores_before_strict_contracts_and_tracks_its_helper(self):
        text = (REPO / ".github/workflows/comparator.yml").read_text()
        self.assertLess(text.index("      - uses: leanprover/lean-action@v1"),
                        text.index("      - name: Restore Mathlib cache with retries"))
        self.assertLess(text.index("      - name: Restore Mathlib cache with retries"),
                        text.index("run: scripts/cache/get-missing.sh"))
        self.assertLess(text.index("run: scripts/cache/get-missing.sh"),
                        text.index("      - name: Compare all reviewed contracts"))
        contract_step = text.split("      - name: Compare all reviewed contracts", 1)[1]
        self.assertIn("run: python3 scripts/check_comparator.py basic automation sat --negative-control",
                      contract_step)
        self.assertNotIn("continue-on-error", contract_step)
        for event, following in (("pull_request", "push"), ("push", "workflow_dispatch")):
            with self.subTest(event=event):
                trigger = text.split(f"  {event}:\n", 1)[1].split(f"  {following}:", 1)[0]
                for dependency in ("scripts/cache/get_mathlib.py", "scripts/test_mathlib_cache.py"):
                    self.assertIn(f"      - '{dependency}'", trigger)


if __name__ == "__main__":
    unittest.main()
