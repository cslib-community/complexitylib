#!/usr/bin/env python3
"""Cancel Lean CI merge-group runs whose merge-queue entry no longer exists.

The Lean workflow gives every merge-group run its own concurrency group, so that each queued entry
completes. GitHub does not cancel such a run when its entry leaves the queue: when the entry lands
inside a later group, or the group is rebuilt after an ejection, its `gh-readonly-queue/main/…`
branch is deleted, but the run keeps its runner until it finishes or times out.

A run is a candidate when it is still queued or in progress, it was created at least
`MIN_AGE` before the queue branches were listed, the listing has no queue branch with its name
pointing at its head commit, and its head commit is not the current `main` commit. Before
cancelling a candidate, the script reads its branch again and cancels only when GitHub reports the
branch missing (HTTP 404) or pointing at another commit. Any other error keeps the run, so a short
listing or an API failure cannot cancel a live entry.

No later work needs a cancelled run. A merge group lands only after its required checks succeed,
so the `main` push can only restore a build handoff from a completed successful run for the commit
that landed (`scripts/cache_handoff.py`). A run that is still going is for a commit that is now an
ancestor of `main` or that will never land.

Dry run by default; `--apply` cancels. Needs `gh` authenticated with `actions: write`.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
from collections.abc import Callable
from datetime import datetime, timedelta, timezone

WORKFLOW = "lean_action_ci.yml"
QUEUE_PREFIX = "gh-readonly-queue/main/"
ACTIVE = ("queued", "in_progress", "waiting", "pending", "requested")
# Stale runs are tens of minutes old; the margin absorbs clock skew and a just-created ref.
MIN_AGE = timedelta(minutes=5)

Error = (subprocess.SubprocessError, OSError, ValueError, KeyError, TypeError)


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


def timestamp(value: str) -> datetime:
    return datetime.fromisoformat(value.replace("Z", "+00:00"))


def stale_runs(runs: list[dict], queue: dict[str, str], listed_at: datetime,
               main_sha: str) -> list[dict]:
    """The old enough active merge-group runs whose listed queue branch is gone or moved."""
    cutoff = listed_at - MIN_AGE
    stale = []
    for run in runs:
        branch = run.get("head_branch") or ""
        if (run.get("event") == "merge_group" and run.get("status") in ACTIVE
                and branch.startswith(QUEUE_PREFIX) and timestamp(run["created_at"]) <= cutoff
                and queue.get(branch) != run.get("head_sha") and run.get("head_sha") != main_sha):
            stale.append(run)
    return sorted(stale, key=lambda run: run["created_at"])


def queue_branches(repository: str) -> dict[str, str]:
    refs = gh(f"repos/{repository}/git/matching-refs/heads/{QUEUE_PREFIX}", items=".[]")
    return {ref["ref"].removeprefix("refs/heads/"): ref["object"]["sha"] for ref in refs}


def branch_head(repository: str, branch: str) -> str | None:
    """The commit `branch` points at, or None when GitHub reports it missing; raises otherwise."""
    try:
        return gh(f"repos/{repository}/git/ref/heads/{branch}")["object"]["sha"]
    except subprocess.CalledProcessError as error:
        if "(HTTP 404)" in (error.stderr or ""):
            return None
        raise


def reason(error: Exception) -> str:
    stderr = getattr(error, "stderr", None)
    return stderr.strip() if isinstance(stderr, str) and stderr.strip() else str(error)


def confirmed_stale(run: dict, read_head: Callable[[str], str | None]) -> tuple[bool, str]:
    """Whether a fresh read shows the run's branch missing or moved, and what was seen."""
    try:
        head = read_head(run["head_branch"])
    except Error as error:
        return False, f"could not read its branch: {reason(error)}"
    if head is None:
        return True, "branch missing"
    if head != run["head_sha"]:
        return True, f"branch now at {head}"
    return False, "branch still live"


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
    listed_at = datetime.now(timezone.utc)
    queue = queue_branches(args.repo)
    main_sha = gh(f"repos/{args.repo}/commits/main")["sha"]
    stale = stale_runs(active_runs(args.repo), queue, listed_at, main_sha)
    print(f"{len(queue)} live queue branches; {len(stale)} candidate merge-group runs")
    for run in stale:
        line = f"{run['id']} {run['status']} since {run['created_at']} {run['head_branch']}"
        confirmed, seen = confirmed_stale(run, lambda branch: branch_head(args.repo, branch))
        if not confirmed:
            print(f"::warning::kept {line}: {seen}")
            continue
        if not args.apply:
            print(f"would cancel {line} ({seen})")
            continue
        try:
            gh(f"repos/{args.repo}/actions/runs/{run['id']}/cancel", method="POST")
            print(f"cancelled {line} ({seen})")
        except Error as error:
            # A run that finished in the meantime can no longer be cancelled; the next sweep retries
            # any other failure.
            print(f"::warning::could not cancel {line}: {reason(error)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
