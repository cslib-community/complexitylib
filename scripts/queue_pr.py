#!/usr/bin/env python3
"""Add a pull request to the merge queue at exactly the approved head.

Usage: python3 scripts/queue_pr.py PR SHA [--wait MINUTES] [--repo OWNER/NAME]

This is the queueing half of approve-and-queue (AGENTS.md, "Approve and queue"). It refuses
unless the pull request is open, not a draft, based on `main`, has head SHA, and merges cleanly
into its base, and the required check (`REQUIRED_CHECKS`) has succeeded at SHA. While that check
is still running it waits up to `--wait` minutes (default 0: report and stop); it always waits
briefly for GitHub to compute mergeability. It then enqueues with `expectedHeadOid` = SHA, so a
push after the approval can never be queued in its place.

It does not judge the approval itself, a hold named in it, or a request for human review in the
PR or its issue; the reviewer checks those before running it. Its retarget check (a base change
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

REPO = "cslib-community/complexitylib"
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
      commits(last: 1) { nodes { commit { oid committedDate
        statusCheckRollup { contexts(first: 100) { nodes {
          ... on CheckRun { name status conclusion startedAt checkSuite { app { databaseId } } }
        } } } } } }
    }
  }
}"""

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
    data = json.loads(result.stdout)
    if data.get("errors"):
        raise GhError("; ".join(error.get("message", str(error)) for error in data["errors"]))
    return data["data"]


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
    try:
        while True:
            pr = (gh_graphql(QUERY, owner=owner, name=name, number=args.pr)["repository"]
                  or {}).get("pullRequest")
            if pr is None:
                raise GhError(f"no pull request #{args.pr} in {args.repo}")
            status, reasons = assess(pr, args.sha)
            if status != "pending":
                break
            if pr["mergeable"] == "UNKNOWN" and retries > 0:
                retries -= 1
                time.sleep(MERGEABLE_SECONDS)
            elif time.monotonic() < deadline:
                time.sleep(POLL_SECONDS)
            else:
                break
        if status == "queued":
            entry = pr["mergeQueueEntry"]
            print(f"#{args.pr} is already queued at {args.sha[:12]} "
                  f"(position {entry['position']}, {entry['state'].lower()}).")
            return 0
        if status != "ready":
            verb = "not queued yet" if status == "pending" else "not queued"
            print(f"#{args.pr} {verb}: " + "; ".join(reasons) + ".")
            return 1
        entry = (gh_graphql(ENQUEUE, id=pr["id"], sha=args.sha)["enqueuePullRequest"]
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
