#!/usr/bin/env python3
"""Add a pull request to the merge queue at exactly the approved head.

Usage: python3 scripts/queue_pr.py PR SHA [--wait MINUTES] [--repo OWNER/NAME]

This is the queueing half of approve-and-queue (AGENTS.md, "Approve and queue"). It refuses
unless the pull request is open, not a draft, based on `main`, has head SHA, and merges cleanly
into its base, and the required check (`REQUIRED_CHECKS`) has succeeded at SHA. All pages of check
contexts are read from the same commit before selecting each required check's latest attempt.
While that check is still running it waits up to `--wait` minutes (default 0: report and stop);
it always waits briefly for GitHub to compute mergeability. It then enqueues with
`expectedHeadOid` = SHA, so a push after the approval can never be queued in its place.
If it sleeps, it snapshots the PR discussion before the first sleep and rereads it just before
enqueueing. A changed body, comment, submitted review or inline thread stops the waiting enqueue
so the reviewer can reread and rerun. Check events and reactions are not discussion changes.

It does not judge the approval itself, a hold named in it, or a request for human review in the
PR or its issue; the reviewer checks those before running it. The discussion read is not atomic
with enqueue and does not inspect linked issues. Its retarget check (a base change
newer than the head's commit date) only catches the common mistake of queueing a stacked PR before
it merges `main`; `scripts/check_restack.py` is what verifies a restacked head.

Exit status: 0 when the PR is queued (or already was), 1 when it is refused or the check is still
running, 2 on a `gh` error. Requires an authenticated `gh` with write access to the repository.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import time

REPO = "cslib-community/cslib-frontier"
# The checks the `main` ruleset requires (Settings → Rules → main), each with the GitHub App that
# must report it (15368 is GitHub Actions), as the ruleset pins them; keep in sync with it.
REQUIRED_CHECKS = {"ci-checks": 15368}
POLL_SECONDS = 30
# GitHub computes mergeability lazily, so the first query can return UNKNOWN; re-ask this often.
MERGEABLE_RETRIES, MERGEABLE_SECONDS = 10, 3

QUERY = """
query($owner: String!, $name: String!, $number: Int!) {
  repository(owner: $owner, name: $name) {
    pullRequest(number: $number) {
      id state isDraft baseRefName headRefOid mergeable
      mergeQueueEntry { position state }
      timelineItems(last: 1, itemTypes: [BASE_REF_CHANGED_EVENT,
                                         AUTOMATIC_BASE_CHANGE_SUCCEEDED_EVENT]) {
        nodes {
          ... on BaseRefChangedEvent { createdAt }
          ... on AutomaticBaseChangeSucceededEvent { createdAt }
        }
      }
      commits(last: 1) { nodes { commit { id oid committedDate
        statusCheckRollup { contexts(first: 100) {
          nodes {
            ... on CheckRun { name status conclusion startedAt checkSuite { app { databaseId } } }
          }
          pageInfo { endCursor hasNextPage }
        } } } } }
    }
  }
}"""

CONTEXTS_QUERY = """
query($id: ID!, $after: String!) {
  node(id: $id) {
    ... on Commit { oid
      statusCheckRollup { contexts(first: 100, after: $after) {
        nodes {
          ... on CheckRun { name status conclusion startedAt checkSuite { app { databaseId } } }
        }
        pageInfo { endCursor hasNextPage }
      } }
    }
  }
}"""

PAGE_INFO = "pageInfo { endCursor hasNextPage }"
COMMENT_FIELDS = "id body updatedAt"
INLINE_FIELDS = f"{COMMENT_FIELDS} state"
REVIEW_FIELDS = f"{COMMENT_FIELDS} state submittedAt"
THREAD_FIELDS = (f"id isResolved comments(first: 100) {{ nodes {{ {INLINE_FIELDS} }} "
                 f"{PAGE_INFO} }}")
DISCUSSION_QUERY = f"""
query($id: ID!) {{
  node(id: $id) {{
    ... on PullRequest {{ id body
      comments(first: 100) {{ nodes {{ {COMMENT_FIELDS} }} {PAGE_INFO} }}
      reviews(first: 100) {{ nodes {{ {REVIEW_FIELDS} }} {PAGE_INFO} }}
      reviewThreads(first: 100) {{ nodes {{ {THREAD_FIELDS} }} {PAGE_INFO} }}
    }}
  }}
}}"""

ENQUEUE = """
mutation($id: ID!, $sha: GitObjectID!) {
  enqueuePullRequest(input: {pullRequestId: $id, expectedHeadOid: $sha}) {
    mergeQueueEntry { position state }
  }
}"""


class GhError(Exception):
    pass


def gh_graphql(query: str, **variables: str | int) -> dict:
    command = ["gh", "api", "graphql", "-f", f"query={query}"]
    for key, value in variables.items():
        command += ["-F" if isinstance(value, int) else "-f", f"{key}={value}"]
    result = subprocess.run(command, capture_output=True, text=True)
    if result.returncode != 0:
        raise GhError(result.stderr.strip() or result.stdout.strip())
    try:
        data = json.loads(result.stdout)
    except ValueError as error:
        raise GhError("GitHub returned invalid JSON") from error
    if not isinstance(data, dict):
        raise GhError("GitHub returned no GraphQL response object")
    if data.get("errors"):
        raise GhError("; ".join(error.get("message", str(error)) for error in data["errors"]))
    if not isinstance(data.get("data"), dict):
        raise GhError("GitHub returned no GraphQL data")
    return data["data"]


def fetch_pr(owner: str, name: str, number: int) -> dict:
    """Read the PR and every check page, pinned to its initial commit's node ID and OID.

    Querying `commits(last: 1)` again during pagination could mix two heads after a push. The
    immutable commit node keeps these pages together; enqueue's `expectedHeadOid` still rejects
    a push after this read. Null or incomplete later pages must never make an old success usable.
    """
    repository = gh_graphql(QUERY, owner=owner, name=name, number=number).get("repository")
    pr = (repository or {}).get("pullRequest")
    if not isinstance(pr, dict):
        raise GhError(f"no pull request #{number} in {owner}/{name}")
    commits = (pr.get("commits") or {}).get("nodes")
    if not isinstance(commits, list):
        raise GhError("GitHub returned no commit list for the pull request")
    if not commits:
        return pr  # `assess` refuses a PR without a latest commit.
    commit = (commits[0] or {}).get("commit")
    if not isinstance(commit, dict) or not commit.get("id") or not commit.get("oid"):
        raise GhError("GitHub returned no latest commit identity")
    if commit.get("statusCheckRollup") is None:
        return pr  # No checks have been reported yet.
    page, contexts, seen = commit, [], set()
    while True:
        connection = (page.get("statusCheckRollup") or {}).get("contexts")
        nodes = (connection or {}).get("nodes")
        info = (connection or {}).get("pageInfo")
        if (not isinstance(nodes, list) or any(not isinstance(node, dict) for node in nodes)
                or not isinstance(info, dict) or not isinstance(info.get("hasNextPage"), bool)):
            raise GhError("GitHub returned an incomplete check-context page")
        contexts.extend(nodes)
        if not info["hasNextPage"]:
            break
        cursor = info.get("endCursor")
        if not isinstance(cursor, str) or not cursor or cursor in seen:
            raise GhError("GitHub returned a missing or repeated check-context cursor")
        seen.add(cursor)
        page = gh_graphql(CONTEXTS_QUERY, id=commit["id"], after=cursor).get("node")
        if not isinstance(page, dict) or page.get("oid") != commit["oid"]:
            raise GhError("GitHub returned no matching commit for the next check-context page")
    commit["statusCheckRollup"]["contexts"] = {"nodes": contexts, "pageInfo": info}
    return pr


def discussion_nodes(owner: dict, kind: str, field: str, fields: str) -> list[dict]:
    """Read every page of one discussion connection, pinned to its owning node ID."""
    page, nodes, cursors, identities = owner, [], set(), set()
    while True:
        connection = page.get(field)
        batch = connection.get("nodes") if isinstance(connection, dict) else None
        info = connection.get("pageInfo") if isinstance(connection, dict) else None
        if (not isinstance(batch, list) or any(not isinstance(n, dict) for n in batch)
                or not isinstance(info, dict) or not isinstance(info.get("hasNextPage"), bool)):
            raise GhError(f"GitHub returned an incomplete discussion {field} page")
        for node in batch:
            identity = node.get("id")
            if not isinstance(identity, str) or not identity or identity in identities:
                raise GhError(f"GitHub returned a missing or repeated discussion {field} ID")
            identities.add(identity)
        nodes.extend(batch)
        if not info["hasNextPage"]:
            return nodes
        cursor = info.get("endCursor")
        if not isinstance(cursor, str) or not cursor or cursor in cursors:
            raise GhError(f"GitHub returned a missing or repeated discussion {field} cursor")
        cursors.add(cursor)
        query = f"""
query($id: ID!, $after: String!) {{
  node(id: $id) {{
    ... on {kind} {{ id
      {field}(first: 100, after: $after) {{ nodes {{ {fields} }} {PAGE_INFO} }}
    }}
  }}
}}"""
        page = gh_graphql(query, id=owner["id"], after=cursor).get("node")
        if not isinstance(page, dict) or page.get("id") != owner["id"]:
            raise GhError(f"GitHub returned no matching node for discussion {field} pagination")


def discussion_text(node: dict) -> tuple[str, str, str]:
    """Keep exact text as well as its edit time, including edits within the same second."""
    if (not isinstance(node.get("body"), str) or not isinstance(node.get("updatedAt"), str)
            or not node["updatedAt"]):
        raise GhError("GitHub returned incomplete discussion text")
    return node["id"], node["body"], node["updatedAt"]


def fetch_discussion(pr_id: str) -> tuple:
    """Snapshot visible discussion, without interpreting approvals or hold prose.

    Use explicit reviewThreads: timelineItems does not reliably return inline threads. Read
    all comments, not just the newest, so edits/deletions of older holds are observable. Draft
    reviews and unpublished inline comments do not change the submitted discussion. GitHub has
    no expected-discussion lease; this read and the enqueue mutation still have a bounded race.
    """
    pr = gh_graphql(DISCUSSION_QUERY, id=pr_id).get("node")
    if not isinstance(pr, dict) or pr.get("id") != pr_id or not isinstance(pr.get("body"), str):
        raise GhError("GitHub returned no matching pull request discussion")
    comments = [discussion_text(c) for c in discussion_nodes(
        pr, "PullRequest", "comments", COMMENT_FIELDS)]
    reviews = []
    for review in discussion_nodes(pr, "PullRequest", "reviews", REVIEW_FIELDS):
        text = discussion_text(review)
        state, submitted = review.get("state"), review.get("submittedAt")
        if (not isinstance(state, str)
                or state not in {"PENDING", "APPROVED", "CHANGES_REQUESTED", "COMMENTED",
                                 "DISMISSED"}):
            raise GhError("GitHub returned an incomplete discussion review state")
        if state != "PENDING":
            if not isinstance(submitted, str) or not submitted:
                raise GhError("GitHub returned no submitted discussion review time")
            reviews.append((*text, state, submitted))
    threads = []
    for thread in discussion_nodes(pr, "PullRequest", "reviewThreads", THREAD_FIELDS):
        if not isinstance(thread.get("isResolved"), bool):
            raise GhError("GitHub returned an incomplete discussion thread state")
        inline = []
        for comment in discussion_nodes(
                thread, "PullRequestReviewThread", "comments", INLINE_FIELDS):
            text = discussion_text(comment)
            if comment.get("state") not in ("PENDING", "SUBMITTED"):
                raise GhError("GitHub returned an incomplete inline discussion comment state")
            if comment["state"] == "SUBMITTED":
                inline.append(text)
        if inline:
            threads.append((thread["id"], thread["isResolved"], tuple(sorted(inline))))
    return pr["body"], tuple(sorted(comments)), tuple(sorted(reviews)), tuple(sorted(threads))


def check_state(pr: dict) -> tuple[str, list[str]]:
    """Combined state of the required checks on the PR's latest commit, with failing names.

    Only check runs from the app the ruleset names count, and, like branch protection, only the
    most recent run of each check (an earlier run of the same commit may have been cancelled or
    failed). `success` when every required check's latest run succeeded, `pending` while one is
    missing or running, `failure` otherwise.
    """
    commits = pr["commits"]["nodes"]
    rollup = commits[0]["commit"].get("statusCheckRollup") if commits else None
    contexts = rollup["contexts"]["nodes"] if rollup else []
    pending, failed = False, []
    for name, app in REQUIRED_CHECKS.items():
        runs = [c for c in contexts if c.get("name") == name
                and ((c.get("checkSuite") or {}).get("app") or {}).get("databaseId") == app]
        if not runs:
            pending = True
            continue
        latest = max(runs, key=lambda c: c.get("startedAt") or "~")
        if latest.get("status") != "COMPLETED":
            pending = True
        elif latest.get("conclusion") != "SUCCESS":
            failed.append(name)
    if failed:
        return "failure", failed
    return ("pending" if pending else "success"), []


def assess(pr: dict, sha: str) -> tuple[str, list[str]]:
    """`queued`, `ready`, `pending` or `refused`, with reasons for a refusal or wait."""
    if pr["state"] != "OPEN":
        return "refused", [f"the pull request is {pr['state'].lower()}"]
    if pr["headRefOid"] != sha:
        return "refused", [f"its head is {pr['headRefOid']}, not the approved {sha}; "
                           "review the new head (or run scripts/check_restack.py) first"]
    if pr.get("mergeQueueEntry"):
        return "queued", []
    commits = pr["commits"]["nodes"]
    if not commits or commits[0]["commit"]["oid"] != sha:
        return "refused", ["GitHub's latest commit for it is not the approved head; retry shortly"]
    reasons = []
    retargets = [e["createdAt"] for e in pr["timelineItems"]["nodes"] if e.get("createdAt")]
    if retargets and retargets[-1] > commits[0]["commit"]["committedDate"]:
        reasons.append("its base changed after the approved head was committed (a stacked PR "
                       "retargeted when its lower PR landed); merge `main` into it, run "
                       "scripts/check_restack.py, and queue the new head")
    if pr["isDraft"]:
        reasons.append("it is a draft")
    if pr["baseRefName"] != "main":
        reasons.append(f"it is based on `{pr['baseRefName']}`, not `main`; queue it once the "
                       "lower PR lands and GitHub retargets it")
    if pr["mergeable"] == "CONFLICTING":
        reasons.append("it conflicts with `main`; merge `main` into it first")
    state, failed = check_state(pr)
    if state == "failure":
        reasons.append(f"required checks failed at the approved head: {', '.join(failed)}")
    if reasons:
        return "refused", reasons
    waiting = []
    if pr["mergeable"] != "MERGEABLE":
        waiting.append("GitHub has not yet determined whether it merges cleanly")
    if state == "pending":
        waiting.append("required checks are still running at the approved head")
    return ("pending", waiting) if waiting else ("ready", [])


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("pr", type=int, help="pull request number")
    parser.add_argument("sha", help="the full approved head commit")
    parser.add_argument("--wait", type=float, default=0, metavar="MINUTES",
                        help="wait this long for running required checks (default 0)")
    parser.add_argument("--repo", default=REPO, help=f"OWNER/NAME (default {REPO})")
    args = parser.parse_args(argv)
    if not re.fullmatch(r"[0-9a-f]{40}", args.sha):
        parser.error("SHA must be the full 40-character commit hash")
    if not re.fullmatch(r"[^/\s]+/[^/\s]+", args.repo):
        parser.error("--repo must be OWNER/NAME")
    owner, name = args.repo.split("/", 1)
    deadline = time.monotonic() + 60 * args.wait
    retries = MERGEABLE_RETRIES
    discussion = None
    try:
        while True:
            pr = fetch_pr(owner, name, args.pr)
            status, reasons = assess(pr, args.sha)
            if status != "pending":
                break
            if pr["mergeable"] == "UNKNOWN" and retries > 0:
                retries -= 1
                delay = MERGEABLE_SECONDS
            elif time.monotonic() < deadline:
                delay = POLL_SECONDS
            else:
                break
            if discussion is None:
                discussion = fetch_discussion(pr["id"])
            time.sleep(delay)
        if status == "queued":
            entry = pr["mergeQueueEntry"]
            print(f"#{args.pr} is already queued at {args.sha[:12]} "
                  f"(position {entry['position']}, {entry['state'].lower()}).")
            return 0
        if status != "ready":
            verb = "not queued yet" if status == "pending" else "not queued"
            print(f"#{args.pr} {verb}: " + "; ".join(reasons) + ".")
            return 1
        if discussion is not None and fetch_discussion(pr["id"]) != discussion:
            print(f"#{args.pr} not queued: its review discussion changed while waiting; "
                  "reread the PR and any review holds, then rerun the helper.")
            return 1
        entry = (gh_graphql(ENQUEUE, id=pr["id"], sha=args.sha).get("enqueuePullRequest")
                 or {}).get("mergeQueueEntry")
    except GhError as error:
        print(f"queue_pr: {error}", file=sys.stderr)
        return 2
    if entry is None:
        print(f"queue_pr: GitHub returned no queue entry for #{args.pr}; check its state",
              file=sys.stderr)
        return 2
    print(f"#{args.pr} queued at {args.sha[:12]} (position {entry['position']}).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
