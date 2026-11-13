"""Exercise the merge-queue cleanup's selection of stale merge-group runs without the GitHub API."""
import importlib.util
import io
import subprocess
import unittest
from contextlib import redirect_stdout
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "cancel_stale_merge_groups", ROOT / "scripts/ci/cancel_stale_merge_groups.py")
sweep = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sweep)

BRANCH = "gh-readonly-queue/main/pr-4903-269ed430f8633c2a0c0051325e46096a0a6689ec"
LISTED = "2026-11-13T07:30:00Z"


def run(**overrides):
    return {"id": 1, "event": "merge_group", "status": "in_progress", "head_branch": BRANCH,
            "head_sha": "aaa", "created_at": "2026-11-13T05:58:05Z", **overrides}


class StaleRuns(unittest.TestCase):
    def stale(self, runs, queue=None, main_sha="main"):
        return [r["id"] for r in sweep.stale_runs(runs, queue or {}, LISTED, main_sha)]

    def test_run_whose_queue_branch_is_gone_is_stale(self):
        for status in ("queued", "in_progress", "waiting", "pending", "requested"):
            with self.subTest(status=status):
                self.assertEqual(self.stale([run(status=status)]), [1])

    def test_run_whose_branch_was_rebuilt_on_another_commit_is_stale(self):
        self.assertEqual(self.stale([run()], {BRANCH: "bbb"}), [1])

    def test_live_entry_is_kept(self):
        self.assertEqual(self.stale([run()], {BRANCH: "aaa"}), [])

    def test_runs_created_after_the_branch_listing_are_kept(self):
        self.assertEqual(self.stale([run(created_at="2026-11-13T07:30:01Z")]), [])

    def test_current_main_commit_and_other_runs_are_kept(self):
        for other in (run(head_sha="main"), run(status="completed"), run(event="push"),
                      run(head_branch="main"), run(head_branch=None)):
            with self.subTest(other=other):
                self.assertEqual(self.stale([other]), [])

    def test_stale_runs_are_listed_oldest_first(self):
        runs = [run(id=2, created_at="2026-11-13T06:00:00Z"), run(id=3, created_at="2026-11-11T20:24:40Z")]
        self.assertEqual(self.stale(runs), [3, 2])


class Main(unittest.TestCase):
    def fake_gh(self, cancel_error=False):
        calls = []

        def gh(endpoint, *, method="GET", items=None):
            calls.append((method, endpoint))
            if "matching-refs" in endpoint:
                return [{"ref": "refs/heads/" + BRANCH + "x", "object": {"sha": "ccc"}}]
            if endpoint.endswith("commits/main"):
                return {"sha": "main"}
            if "/runs?" in endpoint:
                return [run(id=7)] if "status=in_progress" in endpoint else []
            if cancel_error:
                raise subprocess.CalledProcessError(1, "gh", stderr="HTTP 409")
            return None
        return gh, calls

    def main(self, *args, cancel_error=False):
        gh, calls = self.fake_gh(cancel_error)
        output = io.StringIO()
        with mock.patch.object(sweep, "gh", gh), redirect_stdout(output):
            code = sweep.main(["--repo", "o/r", *args])
        return code, output.getvalue(), calls

    def test_dry_run_reports_without_cancelling(self):
        code, output, calls = self.main()
        self.assertEqual(code, 0)
        self.assertIn("1 live queue branches; 1 stale merge-group runs", output)
        self.assertIn("would cancel 7 in_progress", output)
        self.assertNotIn("POST", [method for method, _ in calls])

    def test_apply_cancels_and_tolerates_finished_runs(self):
        code, output, calls = self.main("--apply")
        self.assertEqual((code, calls[-1]), (0, ("POST", "repos/o/r/actions/runs/7/cancel")))
        self.assertIn("cancelled 7", output)
        code, output, _ = self.main("--apply", cancel_error=True)
        self.assertEqual(code, 0)
        self.assertIn("::warning::could not cancel 7", output)


if __name__ == "__main__":
    unittest.main()
