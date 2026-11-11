"""Offline tests for the precondition checks in scripts/queue_pr.py."""

from __future__ import annotations

import contextlib
import io
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import queue_pr  # noqa: E402

SHA = "a" * 40


def check_run(name: str = "ci-checks", status: str = "COMPLETED",
              conclusion: str | None = "SUCCESS", started: str = "2026-11-07T10:00:00Z",
              app: int = 15368) -> dict:
    return {"name": name, "status": status, "conclusion": conclusion, "startedAt": started,
            "checkSuite": {"app": {"databaseId": app}}}


def pr(*checks: dict, committed: str = "2026-11-07T09:00:00Z", retargeted: str | None = None,
       **fields) -> dict:
    return {"id": "PR_1", "state": "OPEN", "isDraft": False, "baseRefName": "main",
            "headRefOid": SHA, "mergeable": "MERGEABLE", "mergeQueueEntry": None,
            "timelineItems": {"nodes": [{"createdAt": retargeted}] if retargeted else []},
            "commits": {"nodes": [{"commit": {"oid": SHA, "committedDate": committed,
                                              "statusCheckRollup": {
                                                  "contexts": {"nodes": list(checks)}}}}]},
            **fields}


class AssessTests(unittest.TestCase):
    def test_green_approved_head_is_ready(self) -> None:
        self.assertEqual(queue_pr.assess(pr(check_run(), check_run("HTTP cache origin")), SHA),
                         ("ready", []))

    def test_moved_head_is_refused(self) -> None:
        status, reasons = queue_pr.assess(pr(check_run(), headRefOid="b" * 40), SHA)
        self.assertEqual(status, "refused")
        self.assertIn("not the approved", reasons[0])

    def test_already_queued_is_reported(self) -> None:
        entry = {"position": 2, "state": "AWAITING_CHECKS"}
        self.assertEqual(queue_pr.assess(pr(check_run(), mergeQueueEntry=entry), SHA)[0],
                         "queued")

    def test_draft_stacked_and_conflicting_prs_are_refused(self) -> None:
        status, reasons = queue_pr.assess(
            pr(check_run(), isDraft=True, baseRefName="feat/lower", mergeable="CONFLICTING"), SHA)
        self.assertEqual(status, "refused")
        self.assertEqual(len(reasons), 3)

    def test_failed_required_check_is_refused(self) -> None:
        status, reasons = queue_pr.assess(pr(check_run(conclusion="FAILURE")), SHA)
        self.assertEqual(status, "refused")
        self.assertIn("ci-checks", reasons[0])

    def test_running_or_missing_required_check_is_pending(self) -> None:
        self.assertEqual(queue_pr.assess(pr(check_run(status="IN_PROGRESS", conclusion=None)),
                                         SHA)[0], "pending")
        self.assertEqual(queue_pr.assess(pr(check_run("HTTP cache origin")), SHA)[0], "pending")

    def test_only_the_latest_run_of_a_check_counts(self) -> None:
        cancelled = check_run(conclusion="CANCELLED", started="2026-11-07T09:00:00Z")
        self.assertEqual(queue_pr.assess(pr(cancelled, check_run()), SHA)[0], "ready")
        rerun = check_run(status="IN_PROGRESS", conclusion=None, started="2026-11-07T11:00:00Z")
        self.assertEqual(queue_pr.assess(pr(check_run(), rerun), SHA)[0], "pending")

    def test_unknown_mergeability_is_pending(self) -> None:
        status, reasons = queue_pr.assess(pr(check_run(), mergeable="UNKNOWN"), SHA)
        self.assertEqual(status, "pending")
        self.assertIn("merges cleanly", reasons[0])

    def test_check_from_another_app_does_not_count(self) -> None:
        self.assertEqual(queue_pr.assess(pr(check_run(app=1)), SHA)[0], "pending")

    def test_retargeted_head_must_merge_main_first(self) -> None:
        status, reasons = queue_pr.assess(pr(check_run(), retargeted="2026-11-07T09:30:00Z"), SHA)
        self.assertEqual(status, "refused")
        self.assertIn("base changed", reasons[0])
        later = pr(check_run(), retargeted="2026-11-07T08:00:00Z")
        self.assertEqual(queue_pr.assess(later, SHA)[0], "ready")

    def test_stale_latest_commit_is_refused(self) -> None:
        stale = pr(check_run())
        stale["commits"]["nodes"][0]["commit"]["oid"] = "c" * 40
        self.assertEqual(queue_pr.assess(stale, SHA)[0], "refused")

    def test_closed_pr_is_refused(self) -> None:
        self.assertEqual(queue_pr.assess(pr(check_run(), state="MERGED"), SHA)[0], "refused")


class ArgumentTests(unittest.TestCase):
    def test_abbreviated_sha_and_bad_repo_are_rejected(self) -> None:
        for argv in (["12", "abc1234"], ["12", SHA, "--repo", "complexitylib"]):
            with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
                queue_pr.main(argv)


if __name__ == "__main__":
    unittest.main()
