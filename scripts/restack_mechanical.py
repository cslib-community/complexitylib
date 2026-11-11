#!/usr/bin/env python3
"""Restack a pull request whose only conflicts with `main` are in generated files.

Usage: python3 scripts/restack_mechanical.py PR --approved-head SHA [--approved-base REF]
                                             [--dry-run | --push] [--allow-clean]

GitHub ignores the local `leanagg` and `bibkeys` merge drivers (`.gitattributes`), so the merge
queue ejects a PR when `main` adds lines next to the PR's in the `mk_all` aggregates
(`CslibFrontier.lean`, `CslibFrontierResults.lean`) or in `references.bib`. This script makes
that restack one command. It runs no code from the PR: only Git, this script and `origin/main`'s
scripts. After fetching `origin/main` and the PR head, it

1. runs `origin/main`'s `scripts/check_restack.py APPROVED HEAD` (with `--approved-base`) from a
   temporary checkout of `origin/main`, and refuses unless the PR head is the approved change, or
   an earlier restack of it, so that nothing unreviewed is restacked;
2. lists the paths on which the head conflicts with `origin/main` under a plain text merge, as on
   GitHub, and refuses unless every one is an aggregate or `references.bib` (`--allow-clean` also
   restacks a PR with no conflict, for a lower PR that landed or a fix on `main` it needs);
3. merges `origin/main` into the head with `git merge-tree`, without a worktree, using the two
   drivers for that merge only: `origin/main`'s `scripts/resolve_aggregate_conflict.py` and
   `scripts/resolve_bib_conflict.py`, assigned by `origin/main`'s `.gitattributes`. A
   `references.bib` conflict that the driver refuses (both sides changed one entry) is refused;
4. writes each aggregate exactly as `lake exe mk_all` would for the merged tree, as
   `check_restack.py` derives it (from `lakefile.toml` and the module files, without running
   Lake), and commits the merge with `git commit-tree`, so no hook runs and no ref changes. CI's
   `lake exe mk_all --check` still pins the aggregates;
5. runs `origin/main`'s `scripts/check_restack.py APPROVED NEW` from that checkout, as AGENTS.md
   ("Restacks") requires, and prints its output;
6. with `--push`, and only when that check passes, pushes the merge to the PR's head branch, and
   only if the branch still points at the head it merged: the head GitHub reported must be the
   one fetched, `git ls-remote` must still show it, and the push carries
   `--force-with-lease=<branch>:<head>`. The new head is a merge commit whose first parent is the
   old head, so the push is a fast-forward; history is never rewritten.

The default is `--dry-run`: everything except the push. Apart from fetching `origin/main` into
`refs/remotes/origin/main`, a dry run leaves the caller's checkout and every local and remote
branch as they were; other fetches write only the temporary checkout's `FETCH_HEAD`, and the
merge commit exists only as an unreferenced object. The script never queues a PR and never posts
on GitHub: it prints the check's result line and the `scripts/queue_pr.py` command to run once CI
passes at the new head, and the caller decides what to post and who queues ("Approve and queue"
in AGENTS.md). A fork's branch needs "Allow edits by maintainers".

Exit status: 0 when the restack is done (pushed, or ready to push in a dry run) or not needed;
1 when it is refused or a check reports differences (nothing is pushed); 2 on a usage, `gh` or
Git error. Requires Git 2.42 or later and an authenticated `gh`.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_restack as cr  # noqa: E402

REPOSITORY = "cslib-community/cslib-frontier"
BIB = "references.bib"
# The only paths whose conflicts this script resolves.
GENERATED = frozenset((*cr.AGGREGATES, BIB))
PR_FIELDS = ("number", "state", "baseRefName", "headRefName", "headRefOid", "isCrossRepository",
             "headRepositoryOwner", "headRepository", "maintainerCanModify")


class Refused(Exception):
    """The restack is not mechanical, or not safe to publish; nothing is pushed."""


def log(message: str) -> None:
    print(f"restack_mechanical: {message}", flush=True)


def git(root: Path, *args: str, ok: tuple[int, ...] = (0,)) -> subprocess.CompletedProcess[bytes]:
    return cr.git(root, *args, ok=ok)


def out(root: Path, *args: str) -> str:
    return cr.out(root, *args)


def git_input(root: Path, data: bytes, *args: str) -> str:
    """Run git on `data` as standard input; returns its stripped output."""
    result = subprocess.run(["git", "-C", str(root), *args], input=data, capture_output=True,
                            env=cr.environment())
    if result.returncode != 0:
        raise cr.GitError(f"git {' '.join(args)}: "
                          + result.stderr.decode("utf-8", "replace").strip())
    return result.stdout.decode().strip()


def pr_info(repository: str, number: int) -> dict:
    """The pull request's state and head, from `gh`."""
    try:
        result = subprocess.run(["gh", "pr", "view", str(number), "--repo", repository, "--json",
                                 ",".join(PR_FIELDS)], capture_output=True, text=True, check=True)
    except (OSError, subprocess.CalledProcessError) as error:
        raise cr.GitError(f"cannot read PR #{number} with gh: "
                          f"{getattr(error, 'stderr', '') or error}".strip()) from None
    return json.loads(result.stdout)


def push_target(info: dict) -> str:
    """The remote to push the PR's branch to: `origin`, or the fork's URL."""
    if not info["isCrossRepository"]:
        return "origin"
    if not info.get("maintainerCanModify"):
        raise Refused("the PR's branch is in a fork that does not allow edits by maintainers; "
                      "ask its author to restack it")
    return (f"https://github.com/{info['headRepositoryOwner']['login']}/"
            f"{info['headRepository']['name']}.git")


def plain_conflicts(root: Path, head: str, main: str) -> set[str]:
    """The paths on which `head` and `main` conflict under a text merge with no attributes or
    drivers, as on GitHub, with `check_restack`'s merge settings."""
    empty = out(root, "hash-object", "-t", "tree", os.devnull)
    return cr.merge_tree(root, (f"--attr-source={empty}", "-c",
                                f"core.attributesFile={os.devnull}", *cr.MERGE_CONFIG),
                         head, main)[1]


def driver_merge(root: Path, head: str, main: str, scripts: Path) -> str:
    """The tree of `main` merged into `head` with `origin/main`'s attributes and the resolvers in
    `scripts`; refuses when a path other than an aggregate is left conflicted."""
    tree, conflicts = cr.merge_tree(root, (f"--attr-source={main}", "-c",
                                           f"core.attributesFile={os.devnull}", *cr.MERGE_CONFIG,
                                           *cr.driver_config(root, scripts)), head, main)
    if conflicts - set(cr.AGGREGATES):
        raise Refused("the merge drivers left conflicts in "
                      + ", ".join(sorted(conflicts - set(cr.AGGREGATES)))
                      + " (a `references.bib` entry both sides changed needs a person)")
    return tree


def write_aggregates(root: Path, tree: str, sides: tuple[str, str, str]) -> str:
    """`tree` with each aggregate replaced by what `lake exe mk_all` writes for it, as
    `check_restack` derives it; `sides` (merge base, `main`, head) settle the module style."""
    entries = cr.tree_entries(root, tree)
    try:
        roots = cr.library_roots(root, tree, entries)
        replaced = {}
        for path in cr.AGGREGATES:
            if path not in entries:
                continue
            if path not in roots or "/" in path:
                raise cr.Underivable("`lakefile.toml` names no library root that `mk_all` writes "
                                     "here")
            style, _ = cr.aggregate_style(tuple(cr.blob(root, side, path) for side in sides),
                                          cr.blob(root, tree, path) or b"")
            content = cr.canonical_aggregate(entries, *roots[path], style)
            replaced[path] = git_input(root, content, "hash-object", "-w", "--stdin")
    except cr.Underivable as error:
        raise Refused(f"cannot derive what `mk_all` writes: {error}") from None
    rows = []
    for row in git(root, "ls-tree", "-z", tree).stdout.split(b"\0"):
        if not row:
            continue
        info, name = row.split(b"\t", 1)
        path = name.decode("utf-8", "surrogateescape")
        if path in replaced:
            row = f"100644 blob {replaced[path]}\t{path}".encode()
        rows.append(row + b"\0")
    return git_input(root, b"".join(rows), "mktree", "-z")


def merge(root: Path, head: str, main: str, scripts: Path, branch: str) -> str:
    """Merge `main` into `head`, write the aggregates and commit; returns the merge commit."""
    tree = driver_merge(root, head, main, scripts)
    tree = write_aggregates(root, tree, (cr.merge_base(root, main, head), main, head))
    for path in (*cr.AGGREGATES, BIB):
        content = cr.blob(root, tree, path) or b""
        if any(cr.CONFLICT_MARKER.match(line) for line in content.splitlines()):
            raise Refused(f"{path} still has conflict markers")
    message = (f"Merge origin/main into {branch}\n\nRestacked with "
               "scripts/restack_mechanical.py: conflicts only in generated files.\n")
    new = git_input(root, message.encode(), "commit-tree", tree, "-p", head, "-p", main)
    if out(root, "rev-parse", f"{new}^1", f"{new}^2").split() != [head, main]:
        raise cr.GitError(f"the merge commit {new[:12]} does not have parents {head[:12]}, "
                          f"{main[:12]}")
    return new


def run_check(main_checkout: Path, approved: str, new: str, approved_base: str | None) -> int:
    """Run `origin/main`'s `check_restack.py` from its checkout and print its output."""
    command = [sys.executable, str(main_checkout / "scripts" / "check_restack.py"), approved, new]
    if approved_base:
        command += ["--approved-base", approved_base]
    result = subprocess.run(command, cwd=main_checkout, capture_output=True, text=True)
    output = (result.stdout + result.stderr).rstrip()
    if output:
        print(output, flush=True)
    return result.returncode


def remote_head(root: Path, remote: str, branch: str) -> str | None:
    listed = out(root, "ls-remote", "--heads", remote, f"refs/heads/{branch}")
    return listed.split()[0] if listed else None


def push(root: Path, remote: str, branch: str, old: str, new: str) -> None:
    """Push `new` to `branch` only if the remote branch still points at `old`."""
    if git(root, "merge-base", "--is-ancestor", old, new, ok=(0, 1)).returncode != 0:
        raise cr.GitError(f"{new[:12]} does not descend from {old[:12]}")
    current = remote_head(root, remote, branch)
    if current != old:
        raise Refused(f"{branch} now points at {(current or 'nothing')[:12]}, not the head "
                      f"{old[:12]} that was merged; rerun on the new head")
    result = git(root, "push", "--quiet", f"--force-with-lease=refs/heads/{branch}:{old}",
                 remote, f"{new}:refs/heads/{branch}", ok=(0, 1))
    if result.returncode != 0:
        raise Refused(f"the push to {branch} was refused (it may have moved): "
                      + result.stderr.decode("utf-8", "replace").strip())


def restack(args: argparse.Namespace, root: Path, tmp: Path) -> int:
    info = pr_info(args.repository, args.pr)
    number, branch, old = info["number"], info["headRefName"], info["headRefOid"]
    if info["state"] != "OPEN":
        raise Refused(f"PR #{number} is {info['state'].lower()}")
    if info["baseRefName"] != "main":
        raise Refused(f"PR #{number} is based on {info['baseRefName']}, not main; restack a "
                      "stacked PR once its lower PR has landed and GitHub retargets it")
    remote = push_target(info) if args.push else None
    cr.check_local_attributes(root)
    git(root, "fetch", "--quiet", "--no-tags", "--no-write-fetch-head", "origin",
        "+refs/heads/main:refs/remotes/origin/main")
    main = cr.resolve(root, "origin/main")
    main_checkout = tmp / "main"
    git(root, "worktree", "add", "--quiet", "--detach", str(main_checkout), main)
    # FETCH_HEAD is per worktree, so these fetches write only the temporary checkout's.
    approved = cr.resolve(main_checkout, args.approved_head)
    git(main_checkout, "fetch", "--quiet", "--no-tags", "origin", f"refs/pull/{number}/head")
    head = out(main_checkout, "rev-parse", "FETCH_HEAD^{commit}")
    if head != old:
        raise Refused(f"GitHub reports head {old[:12]} but {head[:12]} was fetched; the PR moved "
                      "during the run, so rerun it")
    log(f"checking that PR #{number}'s head {head[:12]} is the approved change")
    if run_check(main_checkout, approved, head, args.approved_base) != 0:
        raise Refused(f"the head {head[:12]} is not the approved change {approved[:12]}, so it "
                      "needs review before a restack; nothing was merged")
    if git(root, "merge-base", "--is-ancestor", main, head, ok=(0, 1)).returncode == 0:
        log(f"PR #{number} already contains origin/main {main[:12]}; nothing to restack")
        return 0
    conflicts = plain_conflicts(root, head, main)
    if conflicts - GENERATED:
        raise Refused("conflicts with main outside generated files: "
                      + ", ".join(sorted(conflicts - GENERATED)) + "; restack it by hand")
    if not conflicts and not args.allow_clean:
        log(f"PR #{number} merges into main without conflicts, so the queue does not need a "
            "restack; pass --allow-clean to merge main anyway")
        return 0
    log(f"PR #{number} ({branch}, head {head[:12]}) conflicts with origin/main {main[:12]} in: "
        + (", ".join(sorted(conflicts)) or "nothing"))
    new = merge(root, head, main, main_checkout / "scripts", branch)
    log(f"merged: new head {new}")
    if run_check(main_checkout, approved, new, args.approved_base) != 0:
        raise Refused("check_restack.py did not pass, so nothing is pushed; review its output")
    queue = f"python3 scripts/queue_pr.py {number} {new}"
    if not args.push:
        log(f"dry run: nothing pushed. With --push it would push {new[:12]} to {branch} "
            f"(only while it still points at {old[:12]}); then, once CI passes there: {queue}")
        return 0
    push(root, remote, branch, old, new)
    log(f"pushed {new} to {branch}. Once CI passes at that head, the queueing reviewer runs "
        f"the check's command again and then: {queue}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("pr", type=int, help="the pull request number")
    parser.add_argument("--approved-head", required=True, help="the head the approval names")
    parser.add_argument("--approved-base",
                        help="passed to check_restack.py: the base of a stacked approved head")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--dry-run", dest="push", action="store_false",
                      help="do everything except the push (the default)")
    mode.add_argument("--push", dest="push", action="store_true",
                      help="push the merge to the PR's branch if the check passes")
    parser.set_defaults(push=False)
    parser.add_argument("--allow-clean", action="store_true",
                        help="also restack a PR that does not conflict with main")
    parser.add_argument("--repository", default=REPOSITORY, help="GitHub OWNER/NAME")
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="a checkout of the clone")
    args = parser.parse_args(argv)
    try:
        root = Path(out(args.repo, "rev-parse", "--show-toplevel"))
        if out(root, "rev-parse", "--is-shallow-repository") == "true":
            raise cr.GitError("the repository is shallow; run `git fetch --unshallow origin` first")
        with tempfile.TemporaryDirectory(prefix="restack-mechanical-") as name:
            main_checkout = Path(name) / "main"
            try:
                return restack(args, root, Path(name))
            finally:
                if main_checkout.exists():
                    try:
                        git(root, "worktree", "remove", "--force", str(main_checkout))
                    except cr.GitError as error:
                        log(f"warning: could not remove the temporary checkout: {error}")
    except Refused as refusal:
        log(f"refused: {refusal}")
        return 1
    except cr.GitError as error:
        log(f"error: {error}")
        return 2


if __name__ == "__main__":
    sys.exit(main())
