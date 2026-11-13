"""Offline tests for the precondition checks in scripts/queue_pr.py."""

from __future__ import annotations

import contextlib
import io
import json
import pathlib
import subprocess
import sys
import unittest
from unittest.mock import call, patch

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import queue_pr  # noqa: E402

SHA = "a" * 40
COMMIT_ID = "COMMIT_1"


def check_run(name: str = "ci-checks", status: str = "COMPLETED",
              conclusion: str | None = "SUCCESS", started: str = "2026-11-07T10:00:00Z",
              app: int = 15368) -> dict:
    return {"name": name, "status": status, "conclusion": conclusion, "startedAt": started,
            "checkSuite": {"app": {"databaseId": app}}}


def connection(*checks: dict, cursor: str | None = None) -> dict:
    return {"nodes": list(checks), "pageInfo": {"endCursor": cursor,
                                                "hasNextPage": cursor is not None}}


def pr(*checks: dict, committed: str = "2026-11-07T09:00:00Z", retargeted: str | None = None,
       **fields) -> dict:
    commit = {"id": COMMIT_ID, "oid": SHA, "committedDate": committed,
              "statusCheckRollup": {"contexts": connection(*checks)}}
    return {"id": "PR_1", "state": "OPEN", "isDraft": False, "baseRefName": "main",
            "headRefOid": SHA, "mergeable": "MERGEABLE", "mergeQueueEntry": None,
            "timelineItems": {"nodes": [{"createdAt": retargeted}] if retargeted else []},
            "commits": {"nodes": [{"commit": commit}]}, **fields}


def first_page(*checks: dict, cursor: str | None = "page-1", **fields) -> dict:
    result = pr(**fields)
    result["commits"]["nodes"][0]["commit"]["statusCheckRollup"]["contexts"] = connection(
        *checks, cursor=cursor)
    return {"repository": {"pullRequest": result}}


def later_page(*checks: dict, cursor: str | None = None, oid: str = SHA) -> dict:
    return {"node": {"oid": oid, "statusCheckRollup": {
        "contexts": connection(*checks, cursor=cursor)}}}


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
        for argv in (["12", "abc1234"], ["12", SHA, "--repo", "cslib-frontier"]):
            with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
                queue_pr.main(argv)


class PaginationTests(unittest.TestCase):
    def run_main(self, *responses: dict | Exception, wait: str = "0"):
        out = io.StringIO()
        with patch.object(queue_pr, "gh_graphql", side_effect=responses) as graphql, \
             patch.object(queue_pr.time, "sleep"), contextlib.redirect_stdout(out), \
             contextlib.redirect_stderr(out):
            status = queue_pr.main(["12", SHA, "--wait", wait])
        return status, out.getvalue(), graphql.call_args_list

    def test_required_attempt_after_first_hundred_can_fail_or_be_pending(self) -> None:
        first = [check_run(), *(check_run(f"other-{i}") for i in range(99))]
        for latest in (check_run(conclusion="FAILURE", started="2026-11-07T11:00:00Z"),
                       check_run(status="IN_PROGRESS", conclusion=None,
                                 started="2026-11-07T11:00:00Z")):
            with self.subTest(latest=latest):
                status, out, calls = self.run_main(first_page(*first), later_page(latest))
                self.assertEqual(status, 1, out)
                self.assertEqual([c.args[0] for c in calls],
                                 [queue_pr.QUERY, queue_pr.CONTEXTS_QUERY])

    def test_required_check_on_third_page_queues_the_exact_head(self) -> None:
        other = [check_run(f"other-{i}") for i in range(100)]
        entry = {"enqueuePullRequest": {"mergeQueueEntry": {"position": 3, "state": "QUEUED"}}}
        status, out, calls = self.run_main(first_page(*other),
                                            later_page(*other, cursor="page-2"),
                                            later_page(check_run()), entry)
        self.assertEqual(status, 0, out)
        self.assertEqual(calls, [
            call(queue_pr.QUERY, owner="cslib-community", name="cslib-frontier", number=12),
            call(queue_pr.CONTEXTS_QUERY, id=COMMIT_ID, after="page-1"),
            call(queue_pr.CONTEXTS_QUERY, id=COMMIT_ID, after="page-2"),
            call(queue_pr.ENQUEUE, id="PR_1", sha=SHA)])

    def test_later_page_still_requires_the_configured_app(self) -> None:
        status, _, calls = self.run_main(first_page(check_run("other")),
                                          later_page(check_run(app=1)))
        self.assertEqual(status, 1)
        self.assertEqual(len(calls), 2)

    def test_later_page_does_not_override_a_newer_first_page_failure(self) -> None:
        status, _, calls = self.run_main(
            first_page(check_run(conclusion="FAILURE", started="2026-11-07T11:00:00Z")),
            later_page(check_run()))
        self.assertEqual(status, 1)
        self.assertEqual(len(calls), 2)

    def test_wrong_or_missing_commit_cannot_supply_a_later_page(self) -> None:
        for page in ({"node": None}, later_page(check_run(), oid="b" * 40)):
            with self.subTest(page=page):
                status, out, calls = self.run_main(first_page(check_run()), page)
                self.assertEqual(status, 2, out)
                self.assertIn("matching commit", out)
                self.assertEqual(len(calls), 2)

    def test_push_during_pagination_cannot_enqueue_a_replacement_head(self) -> None:
        # Page two is still fetched by the immutable old commit ID. A concurrent push makes
        # GitHub reject enqueue's unchanged expectedHeadOid, rather than queueing the new head.
        status, out, calls = self.run_main(first_page(check_run("other")),
                                            later_page(check_run()),
                                            queue_pr.GhError("head changed before enqueue"))
        self.assertEqual(status, 2, out)
        self.assertEqual(calls[1], call(queue_pr.CONTEXTS_QUERY, id=COMMIT_ID, after="page-1"))
        self.assertEqual(calls[2], call(queue_pr.ENQUEUE, id="PR_1", sha=SHA))

    def test_null_rollup_on_first_page_is_pending(self) -> None:
        first = first_page()
        commit = first["repository"]["pullRequest"]["commits"]["nodes"][0]["commit"]
        commit["statusCheckRollup"] = None
        self.assertEqual(self.run_main(first)[0], 1)

    def test_null_or_incomplete_later_page_is_an_error(self) -> None:
        for rollup in (None, {"contexts": None}, {"contexts": {"nodes": []}},
                       {"contexts": {"nodes": [None], "pageInfo": {"hasNextPage": False}}}):
            with self.subTest(rollup=rollup):
                page = {"node": {"oid": SHA, "statusCheckRollup": rollup}}
                status, out, calls = self.run_main(first_page(check_run()),
                                                    page)
                self.assertEqual(status, 2, out)
                self.assertIn("incomplete check-context page", out)
                self.assertEqual(len(calls), 2)

    def test_missing_or_repeated_cursor_stops_without_enqueuing(self) -> None:
        for cursor in (None, ""):
            with self.subTest(cursor=cursor):
                first = first_page(check_run())
                info = first["repository"]["pullRequest"]["commits"]["nodes"][0]["commit"]
                info["statusCheckRollup"]["contexts"]["pageInfo"]["endCursor"] = cursor
                self.assertEqual(self.run_main(first)[0], 2)
        status, out, calls = self.run_main(first_page(check_run()),
                                            later_page(check_run(), cursor="page-1"))
        self.assertEqual(status, 2, out)
        self.assertEqual(len(calls), 2)

    def test_graphql_failure_on_later_page_stops_without_enqueuing(self) -> None:
        status, out, calls = self.run_main(first_page(check_run()), queue_pr.GhError("API error"))
        self.assertEqual(status, 2)
        self.assertIn("API error", out)
        self.assertEqual(len(calls), 2)

    def test_mergeability_retry_fetches_all_pages_again(self) -> None:
        status, out, calls = self.run_main(
            first_page(check_run(), mergeable="UNKNOWN"), later_page(check_run("other")),
            first_page(check_run()),
            later_page(check_run(conclusion="FAILURE", started="2026-11-07T11:00:00Z")))
        self.assertEqual(status, 1, out)
        self.assertEqual([c.args[0] for c in calls],
                         [queue_pr.QUERY, queue_pr.CONTEXTS_QUERY] * 2)

    def test_waiting_for_checks_fetches_fresh_pages(self) -> None:
        entry = {"enqueuePullRequest": {"mergeQueueEntry": {"position": 1, "state": "QUEUED"}}}
        status, out, calls = self.run_main(
            first_page(check_run("other")),
            later_page(check_run(status="IN_PROGRESS", conclusion=None)),
            first_page(check_run("other")), later_page(check_run()), entry, wait="1")
        self.assertEqual(status, 0, out)
        self.assertEqual([c.args[0] for c in calls],
                         [queue_pr.QUERY, queue_pr.CONTEXTS_QUERY] * 2 + [queue_pr.ENQUEUE])


class GraphqlResponseTests(unittest.TestCase):
    def test_invalid_json_null_data_and_graphql_errors_raise_gh_error(self) -> None:
        for output in ("not JSON", "null", '{"data": null}',
                       json.dumps({"data": None, "errors": [{"message": "denied"}]})):
            with self.subTest(output=output), \
                 patch.object(queue_pr.subprocess, "run",
                              return_value=subprocess.CompletedProcess([], 0, output, "")), \
                 self.assertRaises(queue_pr.GhError):
                queue_pr.gh_graphql(queue_pr.QUERY)


if __name__ == "__main__":
    unittest.main()
