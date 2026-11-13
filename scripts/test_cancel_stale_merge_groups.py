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
LISTED = sweep.timestamp("2026-11-13T07:30:00Z")


def run(**overrides):
    return {"id": 1, "event": "merge_group", "status": "in_progress", "head_branch": BRANCH,
            "head_sha": "aaa", "created_at": "2026-11-13T05:58:05Z", **overrides}


NOT_FOUND = subprocess.CalledProcessError(1, "gh", stderr="gh: Not Found (HTTP 404)\n")
SERVER_ERROR = subprocess.CalledProcessError(1, "gh", stderr="gh: Server Error (HTTP 502)\n")


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

    def test_runs_younger_than_the_minimum_age_are_kept(self):
        self.assertEqual(self.stale([run(created_at="2026-11-13T07:25:00Z")]), [1])
        for young in ("2026-11-13T07:25:01Z", "2026-11-13T07:30:00Z", "2026-11-13T07:31:00Z"):
            with self.subTest(created_at=young):
                self.assertEqual(self.stale([run(created_at=young)]), [])

    def test_current_main_commit_and_other_runs_are_kept(self):
        for other in (run(head_sha="main"), run(status="completed"), run(event="push"),
                      run(head_branch="main"), run(head_branch=None)):
            with self.subTest(other=other):
                self.assertEqual(self.stale([other]), [])

    def test_stale_runs_are_listed_oldest_first(self):
        runs = [run(id=2, created_at="2026-11-13T06:00:00Z"), run(id=3, created_at="2026-11-11T20:24:40Z")]
        self.assertEqual(self.stale(runs), [3, 2])


class BranchHead(unittest.TestCase):
    def head(self, outcome):
        def gh(endpoint, **_):
            self.assertEqual(endpoint, f"repos/o/r/git/ref/heads/{BRANCH}")
            if isinstance(outcome, Exception):
                raise outcome
            return {"object": {"sha": outcome}}
        with mock.patch.object(sweep, "gh", gh):
            return sweep.branch_head("o/r", BRANCH)

    def test_only_http_404_means_missing(self):
        self.assertEqual(self.head("aaa"), "aaa")
        self.assertIsNone(self.head(NOT_FOUND))
        with self.assertRaises(subprocess.CalledProcessError):
            self.head(SERVER_ERROR)


class Main(unittest.TestCase):
    """`main` with a fake API whose bulk listing omits BRANCH, as a short listing would."""

    def fake_gh(self, ref, cancel_error=None):
        calls = []

        def gh(endpoint, *, method="GET", items=None):
            calls.append((method, endpoint))
            if "matching-refs" in endpoint:
                return [{"ref": "refs/heads/" + BRANCH + "x", "object": {"sha": "ccc"}}]
            if endpoint.endswith("commits/main"):
                return {"sha": "main"}
            if "/runs?" in endpoint:
                return [run(id=7)] if "status=in_progress" in endpoint else []
            if endpoint == f"repos/o/r/git/ref/heads/{BRANCH}":
                if isinstance(ref, Exception):
                    raise ref
                return {"ref": "refs/heads/" + BRANCH, "object": {"sha": ref}}
            if cancel_error:
                raise cancel_error
            return None
        return gh, calls

    def main(self, *args, ref=NOT_FOUND, cancel_error=None):
        gh, calls = self.fake_gh(ref, cancel_error)
        output = io.StringIO()
        with mock.patch.object(sweep, "gh", gh), redirect_stdout(output):
            code = sweep.main(["--repo", "o/r", *args])
        self.assertEqual(code, 0)
        return output.getvalue(), [call for call in calls if call[0] == "POST"]

    def test_dry_run_reports_without_cancelling(self):
        output, posts = self.main()
        self.assertIn("1 live queue branches; 1 candidate merge-group runs", output)
        self.assertIn("would cancel 7 in_progress", output)
        self.assertIn("(branch missing)", output)
        self.assertEqual(posts, [])

    def test_missing_or_moved_branch_is_cancelled(self):
        for ref, seen in ((NOT_FOUND, "branch missing"), ("bbb", "branch now at bbb")):
            with self.subTest(seen=seen):
                output, posts = self.main("--apply", ref=ref)
                self.assertEqual(posts, [("POST", "repos/o/r/actions/runs/7/cancel")])
                self.assertIn(f"cancelled 7 in_progress since 2026-11-13T05:58:05Z {BRANCH} ({seen})",
                              output)

    def test_branch_still_live_on_a_fresh_read_is_kept(self):
        output, posts = self.main("--apply", ref="aaa")
        self.assertEqual(posts, [])
        self.assertIn("::warning::kept 7", output)
        self.assertIn("branch still live", output)

    def test_branch_read_errors_keep_the_run(self):
        errors = (SERVER_ERROR, subprocess.TimeoutExpired("gh", 60), OSError("gh not found"))
        for error in errors:
            with self.subTest(error=error):
                output, posts = self.main("--apply", ref=error)
                self.assertEqual(posts, [])
                self.assertIn("::warning::kept 7", output)
                self.assertIn("could not read its branch", output)
        output, _ = self.main("--apply", ref=errors[0])
        self.assertIn("HTTP 502", output)

    def test_cancel_failures_are_warnings(self):
        for error in (subprocess.CalledProcessError(1, "gh", stderr="HTTP 409"),
                      subprocess.TimeoutExpired("gh", 60)):
            with self.subTest(error=error):
                output, posts = self.main("--apply", cancel_error=error)
                self.assertEqual(len(posts), 1)
                self.assertIn("::warning::could not cancel 7", output)


if __name__ == "__main__":
    unittest.main()
