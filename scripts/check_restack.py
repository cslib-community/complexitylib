#!/usr/bin/env python3
"""Check whether a restacked pull request still makes exactly the changes that were approved.

Usage: python3 scripts/check_restack.py APPROVED [NEW] [--base REF]
                                        [--approved-base REF] [--new-base REF]

A restack (merging `main` into a branch, or rebasing it) gives the PR a new head, and approvals
name heads. This compares the PR's own changes at the approved head with those at the new head
(default `HEAD`). Each delta is taken from the merge base of the head and its base ref (default
`origin/main`, or `--approved-base`/`--new-base`) to the head, as GitHub shows it. Per file, the
check compares the ordered removed lines, the ordered added lines, file creation, deletion and mode
changes, and the exact blobs for binary files. Context lines and line numbers are ignored, so
lines that `main` added around the PR's own, as in the sorted `Complexity.lean` import list, do not
count. Renames are compared as a deletion plus an addition.

Exit status: 0 when the deltas are identical, 1 when they differ (the differing lines are
printed), 2 on a usage or Git error. A missing commit is fetched from `origin` by its hash.

For a stacked PR whose lower PR has since landed, give `--approved-base` the lower PR's head at
approval time, so that the approved delta excludes the lower PR's changes.

Identical deltas mean that the restack only combined the approved change with newer `main`. The
merge queue tests that combination in any case, as it does for every approved PR that `main` has
moved past, so CI must still pass at the new head. The carry-forward rule is in AGENTS.md
("Restacks").
"""

from __future__ import annotations

import argparse
import difflib
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# At most this many lines of differences are printed per file.
MAX_DIFF_LINES = 60

HEADER = re.compile(r"^diff --git a/(.*) b/(.*)$")
INDEX = re.compile(r"^index ([0-9a-f]+)\.\.([0-9a-f]+)")
# Header lines that describe the change itself rather than the blobs on either side.
KIND = ("new file mode ", "deleted file mode ", "old mode ", "new mode ")


class GitError(Exception):
    pass


@dataclass
class FileDelta:
    """One file's part of a delta: everything that does not depend on surrounding lines."""

    kind: list[str] = field(default_factory=list)
    removed: list[str] = field(default_factory=list)
    added: list[str] = field(default_factory=list)
    binary: tuple[str, str] | None = None

    def key(self) -> tuple:
        return (tuple(self.kind), tuple(self.removed), tuple(self.added), self.binary)


def git(root: Path, *args: str) -> str:
    result = subprocess.run(["git", "-C", str(root), *args], capture_output=True, text=True,
                            encoding="utf-8", errors="surrogateescape")
    if result.returncode != 0:
        raise GitError(f"git {' '.join(args)}: {result.stderr.strip()}")
    return result.stdout


def resolve(root: Path, ref: str) -> str:
    """The commit `ref` names, fetching it from `origin` by hash when it is missing locally."""
    try:
        return git(root, "rev-parse", "--verify", "--quiet", f"{ref}^{{commit}}").strip()
    except GitError:
        if not re.fullmatch(r"[0-9a-f]{7,40}", ref):
            raise GitError(f"unknown revision `{ref}`") from None
    try:
        git(root, "fetch", "--no-tags", "--quiet", "origin", ref)
    except GitError as error:
        raise GitError(f"`{ref}` is not available locally and could not be fetched: {error}")
    return git(root, "rev-parse", "--verify", f"{ref}^{{commit}}").strip()


def merge_base(root: Path, base: str, head: str) -> str:
    try:
        return git(root, "merge-base", base, head).strip()
    except GitError:
        raise GitError(f"`{head}` has no merge base with `{base}`") from None


def parse(diff: str) -> dict[str, FileDelta]:
    """Split `git diff --unified=0 --full-index --no-renames` output into per-file deltas."""
    files: dict[str, FileDelta] = {}
    current: FileDelta | None = None
    blobs = ("", "")
    last: list[str] | None = None  # the list that received the previous `-` or `+` line
    in_hunk = False
    for line in diff.splitlines():
        match = HEADER.match(line)
        if match:
            current = files.setdefault(match.group(2), FileDelta())
            blobs, last, in_hunk = ("", ""), None, False
            continue
        if current is None:
            continue
        if line.startswith("@@"):
            in_hunk = True
        elif in_hunk and line.startswith(("-", "+")):
            last = current.removed if line[0] == "-" else current.added
            last.append(line[1:])
        elif in_hunk and line.startswith("\\") and last is not None:
            last.append(line)  # "\ No newline at end of file" marks the line before it
        elif not in_hunk:
            if line.startswith(KIND):
                current.kind.append(line)
            elif (index := INDEX.match(line)):
                blobs = (index.group(1), index.group(2))
            elif line.startswith("Binary files "):
                current.binary = blobs
    return files


def delta(root: Path, base: str, head: str) -> dict[str, FileDelta]:
    return parse(git(root, "diff", "--unified=0", "--full-index", "--no-renames", "--no-color",
                     "--no-ext-diff", "--no-textconv", base, head))


def compare(approved: dict[str, FileDelta], new: dict[str, FileDelta]) -> list[str]:
    """Report lines describing every file whose change differs; empty when the deltas agree."""
    report: list[str] = []
    for path in sorted(approved.keys() | new.keys()):
        old_delta, new_delta = approved.get(path), new.get(path)
        if old_delta is None:
            report.append(f"{path}: changed only at the new head")
            continue
        if new_delta is None:
            report.append(f"{path}: changed only at the approved head")
            continue
        if old_delta.key() == new_delta.key():
            continue
        report.append(f"{path}: the PR's change to this file differs")
        if old_delta.kind != new_delta.kind:
            report.append(f"  file mode or status: {old_delta.kind} -> {new_delta.kind}")
        if old_delta.binary != new_delta.binary:
            report.append(f"  binary blobs: {old_delta.binary} -> {new_delta.binary}")
        for label, old_lines, new_lines in (("removed", old_delta.removed, new_delta.removed),
                                            ("added", old_delta.added, new_delta.added)):
            if old_lines == new_lines:
                continue
            body = list(difflib.unified_diff(old_lines, new_lines, f"approved {label} lines",
                                             f"new {label} lines", n=1, lineterm=""))
            shown = body[:MAX_DIFF_LINES]
            report.extend("  " + line for line in shown)
            if len(body) > len(shown):
                report.append(f"  ... {len(body) - len(shown)} more lines")
    return report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("approved", help="the approved head commit")
    parser.add_argument("new", nargs="?", default="HEAD", help="the new head (default HEAD)")
    parser.add_argument("--base", default="origin/main",
                        help="base ref for both heads (default origin/main)")
    parser.add_argument("--approved-base", help="base ref for the approved head (stacked PRs)")
    parser.add_argument("--new-base", help="base ref for the new head")
    parser.add_argument("--root", type=Path, default=ROOT, help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    root = args.root
    try:
        approved = resolve(root, args.approved)
        new = resolve(root, args.new)
        approved_base = merge_base(root, resolve(root, args.approved_base or args.base), approved)
        new_base = merge_base(root, resolve(root, args.new_base or args.base), new)
        approved_delta = delta(root, approved_base, approved)
        new_delta = delta(root, new_base, new)
    except GitError as error:
        print(f"check_restack: {error}", file=sys.stderr)
        return 2
    added = sum(len(d.added) for d in new_delta.values())
    removed = sum(len(d.removed) for d in new_delta.values())
    heads = (f"approved {approved[:12]} (from {approved_base[:12]}), "
             f"new {new[:12]} (from {new_base[:12]})")
    report = compare(approved_delta, new_delta)
    if not report:
        print(f"Restack check: the PR's own changes are identical: {heads}; "
              f"{len(new_delta)} files, +{added} -{removed} lines.")
        return 0
    print(f"Restack check: the PR's own changes differ: {heads}.")
    print("\n".join(report))
    return 1


if __name__ == "__main__":
    sys.exit(main())
