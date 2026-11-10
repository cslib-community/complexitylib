#!/usr/bin/env python3
"""Restack a pull request whose only conflicts with `main` are in generated files.

Usage: python3 scripts/restack_mechanical.py PR --approved-head SHA [--approved-base REF]
                                             [--dry-run | --push] [--allow-clean]

GitHub ignores the local `leanagg` and `bibkeys` merge drivers (`.gitattributes`), so the merge
queue ejects a PR when `main` adds lines next to the PR's in the `mk_all` aggregates
(`CslibFrontier.lean`, `CslibFrontierResults.lean`) or in `references.bib`. This script makes
that restack one command. After `git fetch origin` it

1. lists the paths on which the PR head conflicts with `origin/main` under a plain text merge,
   and refuses unless every one is an aggregate or `references.bib` (`--allow-clean` also
   restacks a PR with no conflict, for a lower PR that landed or a fix on `main` it needs);
2. merges `origin/main` into the head in a temporary detached worktree, never the caller's
   checkout, with the two drivers configured for that merge only. The drivers are
   `origin/main`'s `scripts/resolve_aggregate_conflict.py` and `scripts/resolve_bib_conflict.py`,
   assigned by `origin/main`'s `.gitattributes`. A `references.bib` conflict the driver refuses
   (both sides changed one entry), or any other path left unmerged, is refused;
3. regenerates the aggregates with `lake exe mk_all`, requires `lake exe mk_all --check` to pass,
   and commits the merge. The temporary worktree borrows the caller's `.lake/packages` (or the
   primary checkout's) through a symbolic link, only when its `lake-manifest.json` and
   `lean-toolchain` equal the merged tree's;
4. runs `origin/main`'s `scripts/check_restack.py APPROVED NEW` from a temporary checkout of
   `origin/main`, as AGENTS.md ("Restacks") requires, and prints its output;
5. with `--push`, and only when the check passes, pushes the merge to the PR's head branch, and
   only if that branch still points at the head it merged: the head GitHub reported must be the
   one fetched, `git ls-remote` must still show it, and the push carries
   `--force-with-lease=<branch>:<head>`. The new head is a merge commit whose first parent is the
   old head, so the push is a fast-forward; history is never rewritten.

The default is `--dry-run`: everything except the push. A dry run leaves the caller's checkout,
every branch and every remote branch as they were; the merge commit exists only as an
unreferenced object. The script never queues a PR and never posts on GitHub: it prints the
check's result line and the `scripts/queue_pr.py` command to run once CI passes at the new head,
and the caller decides what to post and who queues ("Approve and queue" in AGENTS.md). A fork's
branch needs "Allow edits by maintainers".

Exit status: 0 when the restack is done (pushed, or ready to push in a dry run) or not needed;
1 when it is refused or the check reports differences (nothing is pushed); 2 on a usage, `gh`,
Git or Lake error. Requires Git 2.42 or later and an authenticated `gh`.
"""

from __future__ import annotations

import argparse
import json
import os
import shlex
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
# The command that regenerates the aggregates; `--check` is appended to verify them.
MK_ALL = ("lake", "exe", "mk_all")
# Files that must agree between the merged tree and the checkout whose `.lake/packages` is borrowed.
LAKE_PINS = ("lake-manifest.json", "lean-toolchain")
# `git status --porcelain` codes of a change that is staged and otherwise clean.
STAGED = ("M ", "A ", "D ", "R ", "T ")
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
    """The paths on which `head` and `main` conflict under a text merge with no attributes, as on
    GitHub, with `check_restack`'s merge settings."""
    empty = out(root, "hash-object", "-t", "tree", os.devnull)
    result = git(root, f"--attr-source={empty}", "-c", f"core.attributesFile={os.devnull}",
                 *cr.MERGE_CONFIG, "merge-tree", "--write-tree", "--name-only", "-z",
                 "--no-messages", main, head, ok=(0, 1))
    fields = result.stdout.split(b"\0")
    return {f.decode("utf-8", "surrogateescape") for f in fields[1:] if f}


def driver_options(root: Path, scripts: Path) -> list[str]:
    """`check_restack`'s pinned drivers, with `bibkeys` and `leanagg` running `scripts`' resolvers
    (those of `origin/main`) and every other configured driver reporting a conflict."""
    python, bib, aggregate = (shlex.quote(str(p)).replace("%", "%%") for p in (
        sys.executable, scripts / "resolve_bib_conflict.py",
        scripts / "resolve_aggregate_conflict.py"))
    return [*cr.driver_config(root),
            "-c", f"merge.{cr.BIB_DRIVER}.driver={python} {bib} --driver %O %A %B",
            "-c", f"merge.{cr.AGGREGATE_DRIVER}.driver={python} {aggregate} %O %A %B"]


def add_worktree(root: Path, path: Path, commit: str) -> Path:
    git(root, "worktree", "add", "--quiet", "--detach", str(path), commit)
    return path


def remove_worktree(root: Path, path: Path) -> None:
    link = path / ".lake" / "packages"
    if link.is_symlink():
        link.unlink()
    if path.exists():
        try:
            git(root, "worktree", "remove", "--force", str(path))
        except cr.GitError as error:
            log(f"warning: could not remove the temporary worktree {path}: {error}")


def packages_source(root: Path) -> Path | None:
    """The checkout whose `.lake/packages` the temporary worktree borrows: this checkout's, or the
    primary checkout's."""
    common = Path(out(root, "rev-parse", "--path-format=absolute", "--git-common-dir"))
    for checkout in (root, common.parent):
        if (checkout / ".lake" / "packages").is_dir():
            return checkout
    return None


def link_packages(root: Path, worktree: Path) -> None:
    """Give `worktree` the Lake packages of a checkout pinned to the same dependencies."""
    source = packages_source(root)
    if source is None:
        raise Refused("no checkout has `.lake/packages` to run `lake exe mk_all` with; "
                      "run `scripts/cache/ensure.sh` in this checkout first")
    for name in LAKE_PINS:
        mine, theirs = source / name, worktree / name
        if (mine.read_bytes() if mine.is_file() else None) != (
                theirs.read_bytes() if theirs.is_file() else None):
            raise Refused(f"the merged {name} differs from {mine}, whose `.lake/packages` would "
                          "be borrowed; update that checkout to current `main` and retry")
    (worktree / ".lake").mkdir(exist_ok=True)
    (worktree / ".lake" / "packages").symlink_to(source / ".lake" / "packages",
                                                 target_is_directory=True)


def run_mk_all(worktree: Path) -> None:
    """Regenerate the aggregates in `worktree`, then require `mk_all --check` to pass."""
    # `mk_all` exits with the number of files it changed, so only the check's status counts.
    output = []
    for command in (MK_ALL, (*MK_ALL, "--check")):
        try:
            result = subprocess.run(command, cwd=worktree, capture_output=True, text=True)
        except OSError as error:
            raise cr.GitError(f"cannot run `{' '.join(command)}`: {error}") from None
        output.append((result.stdout + result.stderr).strip())
    if result.returncode != 0:
        raise Refused(f"`{' '.join(MK_ALL)} --check` fails after regenerating the aggregates:\n"
                      + "\n".join(filter(None, output)))


def merge(root: Path, worktree: Path, main: str, scripts: Path, branch: str) -> str:
    """Merge `main` into the worktree's head with the drivers, regenerate the aggregates and commit;
    returns the merge commit."""
    head = out(worktree, "rev-parse", "HEAD")
    git(worktree, f"--attr-source={main}", "-c", f"core.attributesFile={os.devnull}",
        *cr.MERGE_CONFIG, *driver_options(root, scripts),
        "merge", "--quiet", "--no-ff", "--no-commit", main, ok=(0, 1))
    raw = git(worktree, "ls-files", "--unmerged", "-z").stdout.split(b"\0")
    unmerged = {row.split(b"\t", 1)[1].decode("utf-8", "surrogateescape") for row in raw if row}
    if unmerged - set(cr.AGGREGATES):
        raise Refused("the merge drivers left conflicts in " + ", ".join(sorted(unmerged - set(
            cr.AGGREGATES))) + " (a `references.bib` entry both sides changed needs a person)")
    link_packages(root, worktree)
    run_mk_all(worktree)
    present = [path for path in cr.AGGREGATES if (worktree / path).is_file()]
    git(worktree, "add", "--", *present)
    for path in (*present, BIB):
        file = worktree / path
        if file.is_file() and any(cr.CONFLICT_MARKER.match(line)
                                  for line in file.read_bytes().splitlines()):
            raise Refused(f"{path} still has conflict markers")
    # Only staged changes may remain: no unstaged edit, untracked file or unmerged path.
    dirty = git(worktree, "status", "--porcelain", "--untracked-files=all",
                "--ignore-submodules=none").stdout.decode("utf-8", "replace")
    unexpected = [line for line in dirty.splitlines() if line[:2] not in STAGED]
    if unexpected:
        raise Refused("the merge left unexpected changes:\n" + "\n".join(unexpected))
    git(worktree, "commit", "--quiet", "--no-edit", "-m", f"Merge origin/main into {branch}",
        "-m", "Restacked with scripts/restack_mechanical.py: conflicts only in generated files.")
    new = out(worktree, "rev-parse", "HEAD")
    if out(worktree, "rev-parse", f"{new}^1", f"{new}^2").split() != [head, main]:
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
    if not cr.git(root, "merge-base", "--is-ancestor", old, new, ok=(0, 1)).returncode == 0:
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
    approved = cr.resolve(root, args.approved_head)
    main_checkout = add_worktree(root, tmp / "main", main)
    # FETCH_HEAD is per worktree, so this fetch writes only the temporary worktree's.
    git(main_checkout, "fetch", "--quiet", "--no-tags", "origin", f"refs/pull/{number}/head")
    head = out(main_checkout, "rev-parse", "FETCH_HEAD^{commit}")
    if head != old:
        raise Refused(f"GitHub reports head {old[:12]} but {head[:12]} was fetched; the PR moved "
                      "during the run, so rerun it")
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
    new = merge(root, add_worktree(root, tmp / "pr", head), main, main_checkout / "scripts", branch)
    log(f"merged: new head {new}")
    status = run_check(main_checkout, approved, new, args.approved_base)
    if status != 0:
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
            tmp = Path(name)
            try:
                return restack(args, root, tmp)
            finally:
                for worktree in (tmp / "pr", tmp / "main"):
                    remove_worktree(root, worktree)
    except Refused as refusal:
        log(f"refused: {refusal}")
        return 1
    except cr.GitError as error:
        log(f"error: {error}")
        return 2


if __name__ == "__main__":
    sys.exit(main())
