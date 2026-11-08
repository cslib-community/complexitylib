#!/usr/bin/env python3
"""Restack many pull requests across the module-root rename: the flag-day batch.

    python3 scripts/flagday_restack.py [--dry-run] [--tsv FILE] [--trailer LINE] PR [PR ...]

Run it from any checkout of a clone whose `origin` is the GitHub repository, after the rename
commit has landed on `main`. Nothing in the checkout changes and no Lean build runs. For each pull
request, ordered so that a stacked one follows the pull request it is based on, it

1. fetches `+pull/N/head` into `refs/flagday/pr/N` and checks that it is the head GitHub reports;
2. restacks it with `rename_module_root.compute_restack` onto the rename commit (`--onto`), or,
   when it is based on another listed pull request, onto that one's restacked head. A restack only
   merges (it never rebases), so the new head descends from the old one;
3. unless `--dry-run`, pushes the new head to the pull request's branch with an ordinary push, never
   a forced one. A fork's branch needs "Allow edits by maintainers"; a refused push is recorded and
   the run goes on;
4. checks that the new head makes the old head's change, converted (`--verify-carry`);
5. writes `number, old head, new head, status, carry` as one TSV line (to `--tsv`, default
   standard output).

Status is `clean` (restacked; pushed unless `--dry-run`), `up-to-date` (it already contains the
rename), `conflict` (left untouched), `push-failed`, `blocked` (its base pull request was not
restacked, or its base branch is neither `main` nor post-rename) or `error`. Carry is `OK`, `DIFF`
or `n.a.`. Details go to standard error.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import rename_module_root as rmr  # noqa: E402

DEFAULT_REPOSITORY = "cslib-community/cslib-frontier"
FIELDS = ("number", "headRefName", "headRefOid", "baseRefName", "isCrossRepository",
          "headRepositoryOwner", "headRepository", "maintainerCanModify", "state")


def log(message: str) -> None:
    print(message, file=sys.stderr, flush=True)


def pr_info(repository: str, number: int) -> dict:
    out = subprocess.run(["gh", "pr", "view", str(number), "--repo", repository, "--json",
                          ",".join(FIELDS)], capture_output=True, text=True, check=True).stdout
    return json.loads(out)


def stack_order(infos: list[dict]) -> list[dict]:
    """The pull requests with every one after the listed pull request it is based on."""
    by_head = {info["headRefName"]: info for info in infos if not info["isCrossRepository"]}
    ordered, seen = [], set()

    def visit(info: dict, path: tuple[int, ...]) -> None:
        if info["number"] in seen or info["number"] in path:
            return
        lower = by_head.get(info["baseRefName"])
        if lower is not None and lower is not info:
            visit(lower, path + (info["number"],))
        seen.add(info["number"])
        ordered.append(info)

    for info in infos:
        visit(info, ())
    return ordered


def push_url(repository: str, info: dict) -> str | None:
    if not info["isCrossRepository"]:
        return f"https://github.com/{repository}.git"
    if not info.get("maintainerCanModify"):
        return None
    owner = info["headRepositoryOwner"]["login"]
    name = info["headRepository"]["name"]
    return f"https://github.com/{owner}/{name}.git"


def restack_one(repo: Path, info: dict, onto: str, *, dry_run: bool, repository: str,
                trailer: str) -> tuple[str, str, str, str]:
    """Restack one pull request; returns (old head, new head, status, carry)."""
    number = info["number"]
    ref = f"refs/flagday/pr/{number}"
    rmr.git(repo, "fetch", "-q", "--no-tags", "origin", f"+pull/{number}/head:{ref}")
    old = rmr.rev(repo, ref)
    if old != info["headRefOid"]:
        log(f"#{number}: fetched {old[:12]}, but GitHub reported {info['headRefOid'][:12]}")
    result = rmr.compute_restack(repo, old, onto, trailer)
    if result.status == "up-to-date":
        log(f"#{number}: already contains {onto[:12]}")
        return old, old, "up-to-date", "n.a."
    if result.status == "conflict":
        log(f"#{number}: conflicts while merging "
            f"{'the pre-rename main' if result.stage == 'pre' else 'the rename'}: "
            + ", ".join(result.conflicts))
        return old, "-", "conflict", "n.a."
    new = result.head
    if not rmr.is_ancestor(repo, old, new):
        raise rmr.ToolError(f"#{number}: {new[:12]} does not descend from {old[:12]}")
    ok, report = rmr.verify_carry(repo, old, new, onto, "origin/main")
    carry = "OK" if ok else "DIFF"
    if not ok:
        log(f"#{number}: carry-forward differences:\n" + "\n".join(report))
    status = "clean"
    if not dry_run:
        url = push_url(repository, info)
        if url is None:
            log(f"#{number}: fork without maintainer edits; push {new} to "
                f"{info['headRefName']} by hand")
            status = "push-failed"
        else:
            push = rmr.git(repo, "push", "-q", url, f"{new}:refs/heads/{info['headRefName']}",
                           check=False)
            if push.returncode != 0:
                log(f"#{number}: push refused: {push.stderr.strip()}")
                status = "push-failed"
            else:
                log(f"#{number}: pushed {new[:12]} to {info['headRefName']}")
    return old, new, status, carry


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("prs", nargs="+", type=int, metavar="PR")
    parser.add_argument("--dry-run", action="store_true", help="do everything except push")
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="a checkout of the clone")
    parser.add_argument("--repository", default=DEFAULT_REPOSITORY, help="GitHub OWNER/NAME")
    parser.add_argument("--onto", help="post-rename commit for PRs based on main "
                        "(default: the rename commit on origin/main)")
    parser.add_argument("--trailer", default="", help="a trailer for the merge commits")
    parser.add_argument("--tsv", type=Path, help="append the results here (default: stdout)")
    args = parser.parse_args(argv)
    repo = Path(rmr.git(args.repo, "rev-parse", "--show-toplevel").stdout.strip())
    rmr.git(repo, "fetch", "-q", "--no-tags", "origin", "main")
    onto_main = rmr.resolve_onto(repo, args.onto, "origin/main")
    log(f"rename commit {onto_main[:12]}; pre-rename main "
        f"{rmr.pre_rename_counterpart(repo, onto_main)[:12]}")
    out = args.tsv.open("a") if args.tsv else sys.stdout
    if not args.tsv or args.tsv.stat().st_size == 0:
        print("number\told_head\tnew_head\tstatus\tcarry", file=out, flush=True)
    infos = []
    for number in args.prs:
        try:
            infos.append(pr_info(args.repository, number))
        except subprocess.CalledProcessError as error:
            log(f"#{number}: cannot read the pull request: {error.stderr.strip()}")
            print(f"{number}\t-\t-\terror\tn.a.", file=out, flush=True)
    new_heads: dict[str, str] = {}
    by_head = {info["headRefName"]: info for info in infos if not info["isCrossRepository"]}
    failures = 0
    for info in stack_order(infos):
        number, base = info["number"], info["baseRefName"]
        line = (info["headRefOid"], "-", "error", "n.a.")
        try:
            if info["state"] != "OPEN":
                raise rmr.ToolError(f"#{number} is {info['state'].lower()}")
            if base == "main":
                onto = onto_main
            elif base in by_head:
                onto = new_heads.get(base)
            else:
                rmr.git(repo, "fetch", "-q", "--no-tags", "origin", base)
                candidate = rmr.rev(repo, "FETCH_HEAD")
                onto = candidate if rmr.has_path(repo, candidate, rmr.MARKER) else None
            if onto is None:
                log(f"#{number}: its base {base} has not been restacked")
                line = (info["headRefOid"], "-", "blocked", "n.a.")
            else:
                line = restack_one(repo, info, onto, dry_run=args.dry_run,
                                   repository=args.repository, trailer=args.trailer)
                if line[2] in ("clean", "up-to-date"):
                    new_heads[info["headRefName"]] = line[1]
        except (rmr.ToolError, subprocess.CalledProcessError) as error:
            log(f"#{number}: {getattr(error, 'stderr', '') or error}")
        failures += line[2] not in ("clean", "up-to-date")
        print("\t".join((str(number),) + line), file=out, flush=True)
    if args.tsv:
        out.close()
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
