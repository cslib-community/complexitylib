"""Offline tests for the precondition checks in scripts/queue_pr.py."""

from __future__ import annotations

import contextlib
import copy
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
             patch.object(queue_pr, "fetch_discussion", return_value=("unchanged",)), \
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


def discussion_comment(identity: str = "C1", body: str = "approve", **fields) -> dict:
    return {"id": identity, "body": body, "updatedAt": "2026-11-13T11:16:09Z", **fields}


def discussion_page() -> dict:
    return {"node": {"id": "PR_1", "body": "PR scope", "comments": connection(),
                     "reviews": connection(), "reviewThreads": connection()}}


def discussion_thread(identity: str = "T1", **fields) -> dict:
    return {"id": identity, "isResolved": True, "comments": connection(
        discussion_comment("RC1", state="SUBMITTED")), **fields}


class DiscussionTests(unittest.TestCase):
    def snapshot(self, *pages):
        with patch.object(queue_pr, "gh_graphql", side_effect=pages) as api:
            result = queue_pr.fetch_discussion("PR_1")
        return result, api.call_args_list

    def test_body_comments_reviews_and_inline_changes_are_observable(self) -> None:
        initial = discussion_page()
        node = initial["node"]
        node["comments"] = connection(discussion_comment())
        node["reviews"] = connection(discussion_comment(
            "R1", state="APPROVED", submittedAt="2026-11-13T11:16:09Z"))
        node["reviewThreads"] = connection(discussion_thread())
        baseline, _ = self.snapshot(initial)
        # The old comment is edited without advancing its second-resolution timestamp.
        changes = [lambda p: p.update(body="human review required"),
                   lambda p: p["comments"]["nodes"].append(discussion_comment("C2", "hold")),
                   lambda p: p["comments"]["nodes"][0].update(body="hold"),
                   lambda p: p["comments"]["nodes"].clear(),
                   lambda p: p["reviews"]["nodes"][0].update(body="approval held"),
                   lambda p: p["reviews"]["nodes"][0].update(state="DISMISSED"),
                   lambda p: p["reviews"]["nodes"].append(discussion_comment(
                       "R2", state="CHANGES_REQUESTED", submittedAt="2026-11-13T11:17:49Z")),
                   lambda p: p["reviewThreads"]["nodes"][0].update(isResolved=False),
                   lambda p: p["reviewThreads"]["nodes"][0]["comments"]["nodes"][0].update(
                       body="still broken"),
                   lambda p: p["reviewThreads"]["nodes"][0]["comments"]["nodes"].append(
                       discussion_comment("RC2", "hold", state="SUBMITTED"))]
        for index, change in enumerate(changes):
            with self.subTest(change=index):
                changed = copy.deepcopy(initial)
                change(changed["node"])
                self.assertNotEqual(self.snapshot(changed)[0], baseline)

    def test_order_ci_events_reactions_and_unpublished_drafts_do_not_change_snapshot(self) -> None:
        initial = discussion_page()
        initial["node"]["comments"] = connection(discussion_comment(), discussion_comment("C2"))
        baseline, _ = self.snapshot(initial)
        changed = copy.deepcopy(initial)
        node = changed["node"]
        node.update(updatedAt="later", statusCheckRollup="new CI event")
        node["comments"]["nodes"].reverse()
        node["comments"]["nodes"][0]["reactions"] = ["THUMBS_UP"]
        node["reviews"] = connection(discussion_comment("R1", state="PENDING", submittedAt=None))
        node["reviewThreads"] = connection(discussion_thread(comments=connection(
            discussion_comment("RC1", state="PENDING"))))
        self.assertEqual(self.snapshot(changed)[0], baseline)

    def test_all_three_connections_and_nested_comments_are_paginated_by_owner(self) -> None:
        first = discussion_page()
        first["node"].update(comments=connection(discussion_comment(), cursor="c1"),
                             reviews=connection(cursor="r1"),
                             reviewThreads=connection(cursor="t1"))
        thread = discussion_thread(comments=connection(cursor="rc1"))
        result, calls = self.snapshot(
            first,
            {"node": {"id": "PR_1", "comments": connection(discussion_comment("C2"), cursor="c2")}},
            {"node": {"id": "PR_1", "comments": connection(discussion_comment("C3", "hold"))}},
            {"node": {"id": "PR_1", "reviews": connection(discussion_comment(
                "R1", state="DISMISSED", submittedAt="2026-11-13T11:16:09Z"))}},
            {"node": {"id": "PR_1", "reviewThreads": connection(thread)}},
            {"node": {"id": "T1", "comments": connection(
                discussion_comment("RC1", state="SUBMITTED"))}})
        self.assertEqual(len(result[1]), 3)
        self.assertEqual(result[1][-1][1], "hold")
        self.assertEqual(result[2][0][3], "DISMISSED")
        self.assertEqual(len(result[3][0][2]), 1)
        self.assertEqual([c.kwargs for c in calls], [
            {"id": "PR_1"}, {"id": "PR_1", "after": "c1"},
            {"id": "PR_1", "after": "c2"}, {"id": "PR_1", "after": "r1"},
            {"id": "PR_1", "after": "t1"}, {"id": "T1", "after": "rc1"}])
        self.assertIn("... on PullRequestReviewThread", calls[-1].args[0])

    def test_missing_pr_identity_or_body_is_an_error(self) -> None:
        for node in (None, {}, {"id": "another"}, {"id": "PR_1", "body": None}):
            with self.subTest(node=node), self.assertRaises(queue_pr.GhError):
                self.snapshot({"node": node})

    def test_null_malformed_or_incomplete_connections_are_errors(self) -> None:
        bad = (None, [], "bad", {}, {"nodes": [], "pageInfo": {}},
               {"nodes": [None], "pageInfo": {"hasNextPage": False}})
        for field in ("comments", "reviews", "reviewThreads", "inline"):
            for connection_value in bad:
                with self.subTest(field=field, value=connection_value), \
                     self.assertRaises(queue_pr.GhError):
                    page = discussion_page()
                    if field == "inline":
                        page["node"]["reviewThreads"] = connection(
                            discussion_thread(comments=connection_value))
                    else:
                        page["node"][field] = connection_value
                    self.snapshot(page)

    def test_missing_text_review_time_and_thread_states_are_errors(self) -> None:
        for field, item in (
                ("comments", discussion_comment(body=None)),
                ("comments", discussion_comment(updatedAt=None)),
                ("reviews", discussion_comment("R1", state="APPROVED", submittedAt=None)),
                ("reviews", discussion_comment("R1", state=[])),
                ("reviewThreads", discussion_thread(isResolved=None)),
                ("reviewThreads", discussion_thread(comments=connection(
                    discussion_comment("RC1", state=None))))):
            with self.subTest(field=field, item=item), self.assertRaises(queue_pr.GhError):
                page = discussion_page()
                page["node"][field] = connection(item)
                self.snapshot(page)

    def test_later_pages_require_matching_owner_valid_cursor_and_distinct_ids(self) -> None:
        initial = discussion_page()
        initial["node"]["comments"] = connection(discussion_comment(), cursor="c1")
        for later in ({"node": None}, {"node": {"id": "another"}},
                      {"node": {"id": "PR_1", "comments": connection(discussion_comment())}},
                      {"node": {"id": "PR_1", "comments": connection({"body": "no ID"})}},
                      {"node": {"id": "PR_1", "comments": connection(cursor="c1")}},
                      queue_pr.GhError("API failed")):
            with self.subTest(later=later), self.assertRaises(queue_pr.GhError):
                self.snapshot(copy.deepcopy(initial), later)
        for cursor in (None, ""):
            with self.subTest(cursor=cursor), self.assertRaises(queue_pr.GhError):
                malformed = copy.deepcopy(initial)
                malformed["node"]["comments"]["pageInfo"]["endCursor"] = cursor
                self.snapshot(malformed)


class WaitingDiscussionTests(unittest.TestCase):
    def run_main(self, prs, discussions=("same", "same"), wait="1"):
        out, events = io.StringIO(), []
        def snapshot(_):
            events.append("discussion")
            response = next(snapshots)
            if isinstance(response, Exception):
                raise response
            return response
        snapshots = iter(discussions)
        with patch.object(queue_pr, "fetch_pr", side_effect=prs), \
             patch.object(queue_pr, "fetch_discussion", side_effect=snapshot) as discussion, \
             patch.object(queue_pr.time, "sleep", side_effect=lambda _: events.append("sleep")), \
             patch.object(queue_pr, "gh_graphql", return_value={
                 "enqueuePullRequest": {"mergeQueueEntry": {"position": 1}}}) as api, \
             contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
            result = queue_pr.main(["5134", SHA, "--wait", wait])
        return result, out.getvalue(), events, discussion, api

    def test_hold_posted_during_wait_refuses_without_enqueuing(self) -> None:
        pending = pr(check_run(status="IN_PROGRESS", conclusion=None))
        result, out, events, _, api = self.run_main(
            [pending, pr(check_run())], ("source approval", "final material review held"))
        self.assertEqual(result, 1, out)
        self.assertIn("discussion changed", out)
        self.assertIn("reread", out)
        self.assertEqual(events, ["discussion", "sleep", "discussion"])
        api.assert_not_called()

    def test_unchanged_discussion_is_read_only_twice_and_queues_expected_head(self) -> None:
        pending = pr(check_run(status="IN_PROGRESS", conclusion=None))
        result, out, events, _, api = self.run_main([pending, pending, pr(check_run())])
        self.assertEqual(result, 0, out)
        self.assertEqual(events, ["discussion", "sleep", "sleep", "discussion"])
        api.assert_called_once_with(queue_pr.ENQUEUE, id="PR_1", sha=SHA)

    def test_automatic_mergeability_wait_is_guarded_even_without_wait_option(self) -> None:
        result, out, events, _, api = self.run_main(
            [pr(check_run(), mergeable="UNKNOWN"), pr(check_run())],
            ("approved", "hold"), wait="0")
        self.assertEqual(result, 1, out)
        self.assertEqual(events, ["discussion", "sleep", "discussion"])
        api.assert_not_called()

    def test_instant_ready_or_no_sleep_pending_does_not_read_discussion(self) -> None:
        for initial, expected in ((pr(check_run()), 0), (pr(), 1)):
            with self.subTest(expected=expected):
                result, out, events, discussion, _ = self.run_main([initial], wait="0")
                self.assertEqual(result, expected, out)
                self.assertEqual(events, [])
                discussion.assert_not_called()

    def test_already_queued_does_not_read_discussion_or_mutate_even_after_wait(self) -> None:
        queued = pr(check_run(), mergeQueueEntry={"position": 2, "state": "QUEUED"})
        for prs in ([queued], [pr(check_run(), mergeable="UNKNOWN"), queued]):
            with self.subTest(prs=prs):
                result, out, events, _, api = self.run_main(prs, ("baseline",))
                self.assertEqual(result, 0, out)
                self.assertEqual(events.count("discussion"), len(prs) - 1)
                api.assert_not_called()

    def test_incomplete_initial_or_final_snapshot_prevents_enqueue(self) -> None:
        pending = pr(check_run(), mergeable="UNKNOWN")
        for discussions in ((queue_pr.GhError("incomplete discussion"),),
                            ("baseline", queue_pr.GhError("incomplete discussion"))):
            with self.subTest(discussions=discussions):
                result, out, _, _, api = self.run_main([pending, pr(check_run())], discussions)
                self.assertEqual(result, 2, out)
                self.assertIn("incomplete discussion", out)
                api.assert_not_called()

    def test_failed_check_or_changed_head_still_prevents_enqueue(self) -> None:
        pending = pr(check_run(status="IN_PROGRESS", conclusion=None))
        for final in (pr(check_run(conclusion="FAILURE")), pr(check_run(), headRefOid="b" * 40)):
            with self.subTest(final=final):
                result, out, events, _, api = self.run_main([pending, final], ("baseline",))
                self.assertEqual(result, 1, out)
                self.assertEqual(events.count("discussion"), 1)
                api.assert_not_called()


if __name__ == "__main__":
    unittest.main()
