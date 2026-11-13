#!/usr/bin/env python3
"""Cancel Lean CI merge-group runs whose merge-queue entry no longer exists.

The Lean workflow gives every merge-group run its own concurrency group, so that each queued entry
completes. GitHub does not cancel such a run when its entry leaves the queue: when the entry lands
inside a later group, or the group is rebuilt after an ejection, its `gh-readonly-queue/main/…`
branch is deleted, but the run keeps its runner until it finishes or times out.

A run is cancelled only when it is still queued or in progress, it started before the queue
branches were listed, and no queue branch with its name points at its head commit. No later work
needs such a run. A merge group lands only after its required checks succeed, so the `main` push
can only restore a build handoff from a completed successful run for the commit that landed
(`scripts/cache_handoff.py`). A run that is still going is for a commit that is now an ancestor of
`main` or that will never land. The current `main` commit is also skipped.

Dry run by default; `--apply` cancels. Needs `gh` authenticated with `actions: write`.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
from datetime import datetime, timezone

WORKFLOW = "lean_action_ci.yml"
QUEUE_PREFIX = "gh-readonly-queue/main/"
ACTIVE = ("queued", "in_progress", "waiting", "pending", "requested")


def gh(endpoint: str, *, method: str = "GET", items: str | None = None):
    """Call the REST API; with `items`, a jq path, return its values from every page."""
    command = ["gh", "api", "--method", method, "-H", "Accept: application/vnd.github+json",
               endpoint]
    if items:
        command += ["--paginate", "--jq", items]
    result = subprocess.run(command, check=True, capture_output=True, text=True, timeout=60)
    if items:
        return [json.loads(line) for line in result.stdout.splitlines() if line.strip()]
    return json.loads(result.stdout) if result.stdout.strip() else None


def stale_runs(runs: list[dict], queue: dict[str, str], listed_at: str, main_sha: str) -> list[dict]:
    """The active merge-group runs whose queue branch is gone or points at another commit."""
    stale = []
    for run in runs:
        branch = run.get("head_branch") or ""
        if (run.get("event") == "merge_group" and run.get("status") in ACTIVE
                and branch.startswith(QUEUE_PREFIX) and run.get("created_at", "") < listed_at
                and queue.get(branch) != run.get("head_sha") and run.get("head_sha") != main_sha):
            stale.append(run)
    return sorted(stale, key=lambda run: run["created_at"])


def queue_branches(repository: str) -> dict[str, str]:
    refs = gh(f"repos/{repository}/git/matching-refs/heads/{QUEUE_PREFIX}", items=".[]")
    return {ref["ref"].removeprefix("refs/heads/"): ref["object"]["sha"] for ref in refs}


def active_runs(repository: str) -> list[dict]:
    runs = {}
    for status in ACTIVE:
        runs.update((run["id"], run) for run in gh(
            f"repos/{repository}/actions/workflows/{WORKFLOW}/runs"
            f"?event=merge_group&status={status}&per_page=100", items=".workflow_runs[]"))
    return list(runs.values())


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY"), required=False)
    parser.add_argument("--apply", action="store_true", help="cancel the stale runs")
    args = parser.parse_args(argv)
    if not args.repo:
        parser.error("--repo OWNER/NAME is required outside GitHub Actions")
    listed_at = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    queue = queue_branches(args.repo)
    main_sha = gh(f"repos/{args.repo}/commits/main")["sha"]
    stale = stale_runs(active_runs(args.repo), queue, listed_at, main_sha)
    print(f"{len(queue)} live queue branches; {len(stale)} stale merge-group runs")
    for run in stale:
        line = f"{run['id']} {run['status']} since {run['created_at']} {run['head_branch']}"
        if not args.apply:
            print(f"would cancel {line}")
            continue
        try:
            gh(f"repos/{args.repo}/actions/runs/{run['id']}/cancel", method="POST")
            print(f"cancelled {line}")
        except subprocess.CalledProcessError as error:
            # A run that finished in the meantime can no longer be cancelled; the next sweep retries
            # any other failure.
            print(f"::warning::could not cancel {line}: {error.stderr.strip()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
