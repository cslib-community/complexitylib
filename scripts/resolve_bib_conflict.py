#!/usr/bin/env python3
"""Merge `references.bib` entry by entry, keyed by citation key.

`references.bib` is sorted by key (`scripts/check_hygiene.py`). Two branches that add entries
between the same neighbours conflict as text, although the merge is mechanical: keep each side's
additions, changes and removals and restore key order. Entries are compared as whole blocks
keyed by citation key (case-insensitively, as BibTeX does). A key that only one side changed takes
that side's block, and identical changes on both sides agree. A key that both sides changed
differently, or an input that is not sorted with unique keys, is refused; a person resolves it.
Entry text is never rewritten.

Commit mode (default) merges BASE (default `origin/main`) into HEAD with `git merge-tree`,
without a checkout or worktree. Any configured `bibkeys` driver is replaced by a plain text
merge, so a local driver cannot hide a conflict that an ordinary merge reports. When the merge
is clean, nothing is written. When the only conflict is a content conflict in `references.bib`
that the entry merge resolves, the script writes a merge commit with parents HEAD and BASE and
prints its SHA. Anything else is refused with exit status 1 and no commit.
No ref is updated and nothing is pushed: publishing the commit to a branch (for example
`git push origin <sha>:refs/heads/<branch>`) is a separate, deliberate step for the branch's
author or a coordinator. This is a local plain-git check: hosted CI still runs on the result.

    python3 scripts/resolve_bib_conflict.py <head> [<base>]

Driver mode is an opt-in local git merge driver, so that an ordinary `git merge` resolves such
conflicts itself. `.gitattributes` names the driver for `references.bib`; enable it once per
clone with

    git config merge.bibkeys.driver 'python3 scripts/resolve_bib_conflict.py --driver %O %A %B'

When the entry merge refuses, the driver falls back to `git merge-file`, leaving the usual
conflict markers. Where the driver is not configured (on GitHub, or in another clone), git uses
its ordinary text merge.
"""

from __future__ import annotations

import argparse
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from check_hygiene import BIB_KEY_RE, check_bibliography  # noqa: E402

BIB = "references.bib"
# The driver that commit mode substitutes for `bibkeys` while it looks for conflicts.
TEXT_DRIVER = "git merge-file -L ours -L base -L theirs %A %O %B"


class Refusal(Exception):
    """The entry merge cannot decide; a person must resolve the conflict."""


def split_entries(text: str, side: str) -> tuple[str, dict[str, str]]:
    """The text before the first entry and each entry block by folded key, for a sorted file."""
    errors = check_bibliography(text, rel=f"{BIB} ({side})")
    if errors:
        raise Refusal("; ".join(errors))
    starts = [m.start() for m in BIB_KEY_RE.finditer(text)] + [len(text)]
    keys = [m.group(1).casefold() for m in BIB_KEY_RE.finditer(text)]
    blocks = {key: text[a:b].rstrip() for key, a, b in zip(keys, starts, starts[1:])}
    return text[:starts[0]], blocks


def pick(label: str, base: str | None, ours: str | None, theirs: str | None) -> str | None:
    """Three-way choice for one block: a one-sided change wins; identical changes agree."""
    if ours == theirs or theirs == base:
        return ours
    if ours == base:
        return theirs
    raise Refusal(f"both sides changed {label} differently")


def merge_bib(base: str, ours: str, theirs: str) -> str:
    """Merge three versions of a sorted bibliography, or raise `Refusal`."""
    (base_pre, base_blocks) = split_entries(base, "base")
    (ours_pre, ours_blocks) = split_entries(ours, "ours")
    (theirs_pre, theirs_blocks) = split_entries(theirs, "theirs")
    preamble = pick("the text before the first entry", base_pre, ours_pre, theirs_pre) or ""
    merged = []
    for key in sorted(base_blocks.keys() | ours_blocks.keys() | theirs_blocks.keys()):
        block = pick(f"entry `{key}`", base_blocks.get(key), ours_blocks.get(key),
                     theirs_blocks.get(key))
        if block is not None:
            merged.append(block)
    text = preamble + "\n\n".join(merged) + ("\n" if merged else "")
    errors = check_bibliography(text)
    if errors:  # Unreachable for sorted inputs; kept as a guard on the output.
        raise Refusal("; ".join(errors))
    return text


def driver(base_path: str, ours_path: str, theirs_path: str) -> int:
    """Git merge driver: write the merge to `ours_path`, else fall back to a text merge."""
    paths = [pathlib.Path(p) for p in (base_path, ours_path, theirs_path)]
    try:
        merged = merge_bib(*(p.read_text(encoding="utf-8") for p in paths))
    except (Refusal, UnicodeDecodeError) as err:
        print(f"resolve_bib_conflict: {err}; falling back to a text merge", file=sys.stderr)
        return subprocess.run(["git", "merge-file", "-L", "ours", "-L", "base", "-L", "theirs",
                               ours_path, base_path, theirs_path]).returncode
    paths[1].write_text(merged, encoding="utf-8")
    return 0


def git(cwd: pathlib.Path, *args: str, stdin: str | None = None) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *args], cwd=cwd, input=stdin, capture_output=True,
                          encoding="utf-8")


def rev(cwd: pathlib.Path, name: str) -> str:
    r = git(cwd, "rev-parse", "--verify", "--end-of-options", f"{name}^{{commit}}")
    if r.returncode:
        raise Refusal(f"cannot resolve `{name}`: {r.stderr.strip()}")
    return r.stdout.strip()


def resolve(head: str, base: str, cwd: pathlib.Path | None = None) -> str | None:
    """Commit mode: the SHA of the resolving merge commit, None if clean, or raise `Refusal`.

    Runs in the repository containing `cwd` (default: the current directory)."""
    cwd = cwd or pathlib.Path.cwd()
    head_sha, base_sha = rev(cwd, head), rev(cwd, base)
    r = git(cwd, "-c", f"merge.bibkeys.driver={TEXT_DRIVER}", "merge-tree", "--write-tree",
            "--no-messages", "-z", head_sha, base_sha)
    if r.returncode not in (0, 1):
        raise Refusal(f"git merge-tree failed: {r.stderr.strip()}")
    tree, *records = r.stdout.split("\0")
    if r.returncode == 0:
        return None
    stages: dict[int, str] = {}
    others = set()
    for record in filter(None, records):
        info, path = record.split("\t", 1)
        mode, oid, stage = info.split()
        if path == BIB and mode == "100644":
            stages[int(stage)] = oid
        else:
            others.add(path)
    if others or set(stages) != {1, 2, 3}:
        listed = ", ".join(sorted(others | ({BIB} if stages else set())))
        raise Refusal(f"conflicts other than a content conflict in {BIB}: {listed}")
    try:
        texts = [git(cwd, "cat-file", "blob", stages[s]).stdout for s in (1, 2, 3)]
    except UnicodeDecodeError as err:
        raise Refusal(f"{BIB} is not UTF-8: {err}") from err
    merged = merge_bib(*texts)
    blob = git(cwd, "hash-object", "-w", "--stdin", stdin=merged).stdout.strip()
    entries = git(cwd, "ls-tree", "-z", tree).stdout.split("\0")
    lines = [f"100644 blob {blob}\t{BIB}" if e.endswith(f"\t{BIB}") else e
             for e in filter(None, entries)]
    new_tree = git(cwd, "mktree", "-z", stdin="\0".join(lines) + "\0").stdout.strip()
    message = (f"Merge {base} into {head}\n\nResolve the {BIB} conflict entry by entry with "
               "scripts/resolve_bib_conflict.py.\n")
    c = git(cwd, "commit-tree", new_tree, "-p", head_sha, "-p", base_sha, "-m", message)
    if c.returncode:
        raise Refusal(f"git commit-tree failed: {c.stderr.strip()}")
    return c.stdout.strip()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--driver", nargs=3, metavar=("BASE", "OURS", "THEIRS"),
                        help="run as a git merge driver (%%O %%A %%B)")
    parser.add_argument("head", nargs="?", help="branch or commit to merge into")
    parser.add_argument("base", nargs="?", default="origin/main",
                        help="branch or commit to merge (default: origin/main)")
    args = parser.parse_args(argv)
    if args.driver:
        if args.head:
            parser.error("--driver takes no other arguments")
        return driver(*args.driver)
    if not args.head:
        parser.error("give the head branch or commit")
    try:
        sha = resolve(args.head, args.base)
    except Refusal as err:
        print(f"refused: {err}", file=sys.stderr)
        return 1
    if sha is None:
        print(f"{args.base} merges into {args.head} without conflicts; nothing written",
              file=sys.stderr)
        return 0
    print(sha)
    print(f"wrote merge commit {sha[:12]} ({args.base} into {args.head}); nothing pushed. "
          f"Check it, then publish it deliberately, e.g. "
          f"`git push origin {sha[:12]}:refs/heads/<branch>`.", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
