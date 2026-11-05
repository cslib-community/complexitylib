"""Tiny filesystem fixtures only: this suite never activates a study or runs Lean."""

import datetime as dt
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from urllib.error import HTTPError

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))
import cache_handoff_measurement as study

NOW = dt.datetime(2026, 11, 1, 12, tzinfo=dt.timezone.utc)


def plan(**changes):
    return {"mode": "paired", "start": "2026-11-01T00:00:00Z", "end": "2026-11-08T00:00:00Z",
            "seed": "prespecified", "sample_denominator": 1, "max_samples": 4,
            "max_bytes": 1024 * 1024, "max_seconds": 30, **changes}


class Fixture(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="handoff-measurement-test-")
        self.addCleanup(self.temp.cleanup)
        # Tiny fixtures do not allocate the production handoff reserve. Simulate capacity;
        # the insufficient-space test overrides this default explicitly.
        disk = patch.object(study.shutil, "disk_usage",
                            return_value=shutil._ntuple_diskusage(64 << 30, 0, 64 << 30))
        disk.start()
        self.addCleanup(disk.stop)
        self.base = Path(self.temp.name)
        self.root, self.cache, self.runner = [self.base / name for name in ("checkout", "cache", "runner")]
        for path in (self.root, self.cache, self.runner):
            path.mkdir()
        self.git("init", "-q")
        self.git("config", "user.name", "Fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
            (self.root / name).write_text("fixture\n")
        (self.root / "lake-manifest.json").write_text('{"packages": []}\n')
        self.git("add", ".")
        self.git("commit", "-qm", "Ancestor")
        self.ancestor = self.git("rev-parse", "HEAD").strip()
        (self.root / "source.txt").write_text("target")
        self.git("add", ".")
        self.git("commit", "-qm", "Target")
        self.sha = self.git("rev-parse", "HEAD").strip()
        self.lake = self.root / ".lake"
        self.dep = self.lake / "packages/dependency/.lake/build/module"
        for file in (self.lake / "build/module", self.dep, self.cache / "artifacts/ancestor"):
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_text("ancestor")
        self.env = {**os.environ, "GITHUB_REPOSITORY": study.REPOSITORY, "GITHUB_EVENT_NAME": "push",
                    "GITHUB_REF": "refs/heads/main", "GITHUB_SHA": self.sha,
                    "GITHUB_RUN_ID": "101", "GITHUB_RUN_ATTEMPT": "1", "RUNNER_OS": "Linux",
                    "RUNNER_ARCH": "X64", "ImageOS": "ubuntu24", "ImageVersion": "fixture",
                    "RUNNER_TEMP": str(self.runner), "GITHUB_OUTPUT": str(self.base / "output"),
                    "GITHUB_ENV": str(self.base / "environment"), "LAKE_CACHE_DIR": str(self.cache),
                    "HANDOFF_MEASUREMENT_ACTIONS_KEY": "lake-fixture-" + self.ancestor,
                    "HANDOFF_MEASUREMENT_PLAN": json.dumps(plan())}
        self.state = study.location(self.env)

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, text=True, stderr=subprocess.DEVNULL)

    def report(self):
        return json.loads((self.state / "report.json").read_text())

    def prepared(self, order="BT", mode="paired"):
        self.state.mkdir()
        (self.state / "bootstrap.log").write_text(f"Remote cache: {self.ancestor} (1 commits back in git rev-list HEAD) has outputs for 1 modules\n")
        data = {"status": "prepared", "run_id": 101, "plan": plan(mode=mode), "context": study.context(self.root, self.env),
                "selection": {"order": order, "assignment": "bypass"}, "arms": []}
        study.save(self.state / "report.json", data)

    def snapshot(self):
        self.state.mkdir(exist_ok=True)
        return study.Snapshot(self.root, self.cache, self.state, plan(), time.monotonic() + 30)

    def test_default_disabled_has_no_side_effects(self):
        with patch.object(study, "context", side_effect=AssertionError("Git accessed")), patch.object(study, "published", side_effect=AssertionError("Network accessed")):
            study.prepare(self.root, {})
            study.prepare(self.root, {"HANDOFF_MEASUREMENT_PLAN": '{"mode":"disabled"}'})
        self.assertFalse(self.state.exists())

    def test_expiry_and_budgets_fail_before_selection(self):
        for change in ({"max_samples": 17}, {"max_seconds": True}, {"max_bytes": study.MAX_BYTES + 1},
                       {"end": "2026-11-16T00:00:00Z"}, {"start": "2026-10-01T00:00:00Z"},
                       {"sample_denominator": 0}, {"seed": "shell\ninput"}):
            with self.subTest(change=change), self.assertRaises(study.handoff.Rejected):
                study.plan_of(json.dumps(plan(**change)), NOW)
        with self.assertRaises(study.handoff.Rejected):
            study.plan_of(json.dumps(plan()), NOW + dt.timedelta(days=10))

    def test_dispatch_reruns_dirty_sources_and_kill_switch_are_rejected(self):
        for changes in ({"GITHUB_EVENT_NAME": "workflow_dispatch"}, {"GITHUB_RUN_ATTEMPT": "2"},
                        {"GITHUB_REF": "refs/heads/other"}, {"DISABLE_BUILD_HANDOFF": "1"},
                        {"GITHUB_SHA": "f" * 40}, {"GITHUB_REPOSITORY": "someone/fork"}):
            with self.subTest(changes=changes), self.assertRaises(study.handoff.Rejected):
                study.context(self.root, {**self.env, **changes})
        (self.root / "source.txt").write_text("dirty")
        with self.assertRaises(study.handoff.Rejected):
            study.context(self.root, self.env)

    def test_prepare_records_exact_context_without_cache_mutation(self):
        run = {"id": 101, "head_sha": self.sha, "event": "push", "head_branch": "main", "run_attempt": 1,
               "created_at": "2026-11-01T12:00:00Z", "path": ".github/workflows/lean_action_ci.yml",
               "repository": {"full_name": study.REPOSITORY}}
        def api(path, paginate=False):
            return [{"total_count": 1, "workflow_runs": [run]}] if paginate else run
        original = study.tree(self.lake, 1024 * 1024)
        with patch.object(study, "published"):
            study.prepare(self.root, self.env, NOW, api)
        self.assertEqual(self.report()["context"]["source_sha"], self.sha)
        self.assertEqual(self.report()["status"], "prepared")
        self.assertEqual(study.tree(self.lake, 1024 * 1024), original)
        self.assertIn("selected=true", (self.base / "output").read_text())

    def test_population_hard_cap_includes_cancelled_and_fast_cases(self):
        runs = [{"id": i, "created_at": f"2026-11-01T12:00:{i:02d}Z", "conclusion": "cancelled" if i == 1 else "success"} for i in range(1, 7)]
        pages = [{"total_count": 6, "workflow_runs": list(reversed(runs))}]
        p = plan(max_samples=2)
        self.assertEqual(study.selection(p, runs[0], pages)["sampled_run_ids"], [1, 2])
        self.assertFalse(study.selection(p, runs[-1], pages)["selected"])
        self.assertEqual(study.selection(p, runs[0], pages), study.selection(p, runs[0], pages))
        with self.assertRaises(study.handoff.Rejected):
            study.selection(p, runs[0], [{"total_count": 7, "workflow_runs": runs}])
        boundary = {"id": 10, "created_at": p["end"]}
        at_end = study.selection(p, boundary, [{"total_count": 1, "workflow_runs": [boundary]}])
        self.assertFalse(at_end["selected"])
        self.assertEqual(at_end["population_count"], 0)

    def test_published_target_and_unknown_cache_status_are_exclusions(self):
        for status in (200, 503):
            response = unittest.mock.MagicMock()
            response.__enter__.return_value.status = status
            with patch.object(study, "urlopen", return_value=response), self.assertRaises(study.handoff.Rejected):
                study.published(self.root, self.env)
        with patch.object(study, "urlopen", side_effect=HTTPError("https://example.invalid", 404, "missing", {}, None)):
            study.published(self.root, self.env)

    def test_initial_ancestor_and_actions_key_are_both_checked(self):
        self.prepared()
        self.assertEqual(study.initial(self.root, self.env, self.state, self.sha)["remote_revision"], self.ancestor)
        with self.assertRaises(study.handoff.Rejected):
            study.initial(self.root, {**self.env, "HANDOFF_MEASUREMENT_ACTIONS_KEY": "lake-" + self.sha}, self.state, self.sha)
        (self.state / "bootstrap.log").write_text(f"Remote cache: {self.sha} (0 commits back in git rev-list HEAD)\n")
        with self.assertRaises(study.handoff.Rejected):
            study.initial(self.root, self.env, self.state, self.sha)

    def test_reset_removes_root_dependency_and_artifact_cache_poison(self):
        snap = self.snapshot()
        self.addCleanup(snap.close)
        for attempt in range(2):
            snap.reset()
            for live in snap.live:
                (live / "baseline-only").write_text("poison")
            self.dep.write_text("baseline dependency")
            (snap.live[1] / "artifacts/ancestor").write_text("baseline cached output")
            snap.reset()
            self.assertEqual([study.tree(p, plan()["max_bytes"]) for p in snap.live], snap.expected)
            self.assertFalse(any((p / "baseline-only").exists() for p in snap.live))
            self.assertEqual(self.dep.read_text(), "ancestor")
        self.assertEqual((self.cache / "artifacts/ancestor").read_text(), "ancestor")

    def test_external_links_and_special_entries_are_rejected(self):
        link = self.lake / "outside"
        link.symlink_to(self.cache)
        with self.assertRaises(study.handoff.Rejected):
            self.snapshot()
        link.unlink()
        fifo = self.lake / "fifo"
        os.mkfifo(fifo)
        with self.assertRaises(study.handoff.Rejected):
            self.snapshot()

    def test_pinned_default_cache_layout_and_explicit_override(self):
        self.assertEqual(study.cache_path(self.env), self.cache)
        env = {k: v for k, v in self.env.items() if k != "LAKE_CACHE_DIR"}
        with patch.object(study.subprocess, "check_output", return_value="/toolchains/rc2/bin/lake\n"):
            self.assertEqual(study.cache_path(env), Path("/toolchains/rc2/lake/cache"))
        with self.assertRaises(study.handoff.Rejected):
            study.cache_path({**self.env, "LAKE_CACHE_DIR": ""})

    def test_git_control_files_and_recursive_snapshot_locations_are_excluded(self):
        marker = self.dep.parent.parent.parent / ".git"
        marker.write_text("gitdir: /foreign/control\n")
        with self.assertRaises(study.handoff.Rejected):
            self.snapshot()
        marker.unlink()
        nested = self.lake / "measurement"
        nested.mkdir()
        with self.assertRaises(study.handoff.Rejected):
            study.Snapshot(self.root, self.cache, nested, plan(), time.monotonic() + 30)

    def test_root_hardlinks_are_detached_before_first_arm(self):
        linked = self.lake / "build/shared"
        os.link(self.cache / "artifacts/ancestor", linked)
        snap = self.snapshot()
        self.addCleanup(snap.close)
        snap.reset()
        linked.write_text("baseline write")
        self.assertEqual((self.cache / "artifacts/ancestor").read_text(), "ancestor")
        self.assertEqual((snap.live[1] / "artifacts/ancestor").read_text(), "ancestor")

    def test_partial_constructor_copy_is_cleaned_without_live_mutation(self):
        self.state.mkdir()
        original = study.shutil.copytree
        def fail(src, dst, *args, **kwargs):
            if str(dst).endswith("initial-cache"):
                Path(dst).mkdir()
                raise OSError("fixture snapshot copy failure")
            return original(src, dst, *args, **kwargs)
        with patch.object(study.shutil, "copytree", side_effect=fail), self.assertRaises(OSError):
            self.snapshot()
        self.assertFalse((self.state / "initial-lake").exists())
        self.assertFalse((self.state / "initial-cache").exists())
        self.assertEqual(self.dep.read_text(), "ancestor")

    def test_budget_failure_never_starts_copy(self):
        self.state.mkdir()
        with patch.object(study.shutil, "copytree", side_effect=AssertionError("copy started")):
            with self.assertRaises(study.handoff.Rejected):
                study.Snapshot(self.root, self.cache, self.state, plan(max_bytes=1), time.monotonic() + 30)
            with patch.object(study.shutil, "disk_usage", return_value=shutil._ntuple_diskusage(10, 9, 1)), self.assertRaises(study.handoff.Rejected):
                study.Snapshot(self.root, self.cache, self.state, plan(), time.monotonic() + 30)

    def test_partial_snapshot_and_reset_failures_preserve_live_state(self):
        snap = self.snapshot()
        self.addCleanup(snap.close)
        snap.reset()
        (self.lake / "baseline-only").write_text("current")
        before = [study.tree(p, plan()["max_bytes"]) for p in snap.live]
        original = study.shutil.copytree
        def fail_second(src, dst, *args, **kwargs):
            if str(dst).endswith("next-1"):
                Path(dst).mkdir()
                raise OSError("fixture disk failure")
            return original(src, dst, *args, **kwargs)
        with patch.object(study.shutil, "copytree", side_effect=fail_second), self.assertRaises(OSError):
            snap.reset()
        self.assertEqual([study.tree(p, plan()["max_bytes"]) for p in snap.live], before)
        self.assertFalse((self.state / "next-0").exists())
        self.assertFalse((self.state / "next-1").exists())

    def test_reset_deadline_preserves_live_state_and_allows_recovery(self):
        snap = self.snapshot()
        self.addCleanup(snap.close)
        snap.reset()
        self.dep.write_text("unfinished arm")
        before = [study.tree(p, plan()["max_bytes"]) for p in snap.live]
        original = study.shutil.copy2
        with patch.object(study.time, "monotonic", return_value=0) as clock:
            def expire_after_copy(src, dst):
                result = original(src, dst)
                clock.return_value = 2
                return result
            with patch.object(study.shutil, "copy2", side_effect=expire_after_copy), self.assertRaises(study.handoff.Rejected):
                snap.reset(deadline=1)
        self.assertEqual([study.tree(p, plan()["max_bytes"]) for p in snap.live], before)
        self.assertFalse((self.state / "next-0").exists())
        self.assertFalse((self.state / "next-1").exists())
        snap.reset()
        self.assertEqual(self.dep.read_text(), "ancestor")

    def test_expired_arm_reset_excludes_trial_before_commands_and_recovers(self):
        self.prepared()
        resets = []
        original = study.Snapshot.reset
        def expired(snapshot, deadline=None):
            resets.append(deadline)
            return original(snapshot, 0 if deadline is not None else None)
        with patch.object(study, "published"), patch.object(study, "observe_producer", return_value={}), patch.object(study.Snapshot, "reset", expired), patch.object(study, "command", side_effect=AssertionError("validation started after expiry")):
            study.measure(self.root, self.env, now=NOW)
        self.assertEqual(self.report()["status"], "excluded")
        self.assertIn("time budget exceeded", self.report()["reason"])
        self.assertEqual(len(resets), 2)
        self.assertIsNotNone(resets[0])
        self.assertIsNone(resets[1])
        self.assertNotIn("recovery_error", self.report())
        self.assertEqual(self.dep.read_text(), "ancestor")

    def test_both_orders_start_each_arm_from_identical_initial_state(self):
        for order in ("BT", "TB"):
            with self.subTest(order=order):
                self.prepared(order)
                starts = []
                def command(args, root, env, deadline, log=None):
                    cache = Path(env["LAKE_CACHE_DIR"])
                    if log:
                        self.assertFalse((root / ".lake/baseline-only").exists())
                        self.assertEqual(self.dep.read_text(), "ancestor")
                        self.assertEqual((cache / "artifacts/ancestor").read_text(), "ancestor")
                        return {"returncode": 0, "log": "Build handoff restored from run 900 attempt 1; normal build and checks still run"}
                    if args == study.CHECKS[0]:
                        starts.append((self.dep.read_text(), (cache / "artifacts/ancestor").read_text()))
                        (root / ".lake/baseline-only").write_text("poison")
                        self.dep.write_text("poison")
                        (cache / "artifacts/ancestor").write_text("poison")
                    return {"returncode": 0}
                with patch.object(study, "published"), patch.object(study, "observe_producer", return_value={"id": 900, "run_attempt": 1}), patch.object(study, "command", side_effect=command):
                    study.measure(self.root, self.env, now=NOW)
                self.assertEqual(self.report()["status"], "paired_complete")
                self.assertEqual(starts, [("ancestor", "ancestor")] * 2)
                self.assertEqual(self.dep.read_text(), "ancestor")
                self.assertFalse((self.lake / "baseline-only").exists())
                shutil.rmtree(self.state)

    def test_failed_arm_is_recorded_and_initial_state_recovered(self):
        self.prepared()
        def failed(*args, **kwargs):
            self.dep.write_text("failed baseline output")
            return {"returncode": 1}
        with patch.object(study, "published"), patch.object(study, "observe_producer", return_value={}), patch.object(study, "command", side_effect=failed):
            study.measure(self.root, self.env, now=NOW)
        self.assertEqual(self.report()["status"], "excluded")
        self.assertFalse(self.report()["arms"][0]["success"])
        self.assertEqual(self.report()["arms"][1]["status"], "not_run")
        self.assertEqual(self.dep.read_text(), "ancestor")
        self.assertNotIn("bypass_restore=true", (self.base / "output").read_text() if (self.base / "output").exists() else "")

    def test_randomized_assignment_never_snapshots_or_runs_validation(self):
        self.prepared(mode="randomized")
        with patch.object(study, "published"), patch.object(study, "observe_producer", return_value={}), patch.object(study, "Snapshot", side_effect=AssertionError("snapshot")), patch.object(study, "command", side_effect=AssertionError("validation")):
            study.measure(self.root, self.env, now=NOW)
        self.assertEqual(self.report()["status"], "randomized_assignment")
        self.assertIn("bypass_restore=true", (self.base / "output").read_text())

    def test_randomized_missing_producer_is_retained_not_resampled(self):
        self.prepared(mode="randomized")
        with patch.object(study, "published"), patch.object(study, "observe_producer", side_effect=study.handoff.Rejected("no producer")):
            study.measure(self.root, self.env, now=NOW)
        self.assertEqual(self.report()["status"], "randomized_assignment")
        self.assertEqual(self.report()["producer"]["status"], "unknown")
        self.assertIn("bypass_restore=true", (self.base / "output").read_text())

    def test_current_producer_attempt_is_recorded_and_foreign_identity_rejected(self):
        from test_cache_handoff import API
        api = API(self.sha)
        api.current = {**api.runs[0], "run_attempt": 2, "status": "in_progress", "conclusion": None}
        observed = study.observe_producer(study.context(self.root, self.env), api)
        self.assertEqual((observed["run_attempt"], observed["status"]), (2, "in_progress"))
        api.current["head_repository"] = {"id": 10, "full_name": "someone/fork"}
        with self.assertRaises(study.handoff.Rejected):
            study.observe_producer(study.context(self.root, self.env), api)

    def test_child_timeout_is_bounded_to_its_own_process(self):
        with self.assertRaises(subprocess.TimeoutExpired):
            study.command([sys.executable, "-c", "import time; time.sleep(5)"], self.root, self.env, time.monotonic() + .05)


class WorkflowContract(unittest.TestCase):
    def test_dormant_hook_and_production_validation_wiring(self):
        text = (SCRIPTS.parent / ".github/workflows/lean_action_ci.yml").read_text()
        sections = {}
        for section in text.split("      - name: ")[1:]:
            name = section.splitlines()[0].strip('"')
            sections[name] = section
        self.assertIn("vars.HANDOFF_MEASUREMENT_PLAN != ''", sections["Prepare optional handoff measurement"])
        restore = sections["Restore validated merge-group build outputs"]
        for expected in ("github.event_name == 'push'", "github.ref == 'refs/heads/main'", "vars.DISABLE_BUILD_HANDOFF != '1'", "vars.DISABLE_BUILD_HANDOFF != 'true'"):
            self.assertIn(expected, restore)
        for name in ("lake build", "lake test", "lake lint", "lake exe mk_all --check", "lake exe lint-style", "checkInitImports"):
            self.assertNotIn("handoff-measurement", sections[name])
        self.assertIn("path: ${{ steps.handoff-measurement.outputs.report }}", sections["Record optional handoff measurement"])
        self.assertNotIn("RUNNER_TEMP", sections["Record optional handoff measurement"])
        commands = []
        for line in text.splitlines():
            line = line.strip().removeprefix("run: ")
            if line.startswith(("lake ", "python3 ")):
                commands.append(shlex.split(line))
        for command in study.CHECKS:
            self.assertIn(command, commands)


if __name__ == "__main__":
    unittest.main()
