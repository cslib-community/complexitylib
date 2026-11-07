#!/usr/bin/env python3
"""Merge `references.bib` entry by entry, keyed by citation key.

`references.bib` is sorted by key (`scripts/check_hygiene.py`). Two branches that add entries
between the same neighbours conflict as text, although the merge is mechanical: keep each side's
additions, changes and removals and restore key order. Entries are compared as whole blocks
keyed by citation key (case-insensitively, as BibTeX does). A key that only one side changed takes
that side's block, and identical changes on both sides agree. A key that both sides changed
differently, or an input that is not sorted with unique keys, is refused; a person resolves it.
Entry text is never rewritten; the separators between entries become one blank line each.

Commit mode (default) merges BASE (default `origin/main`) into HEAD with `git merge-tree`,
without a checkout or worktree. That merge reads no attributes: tracked `.gitattributes`,
`core.attributesFile` and the system file are disabled, so neither the tracked `merge=union`
lines nor a configured `bibkeys` driver can resolve a conflict that a plain text merge reports.
The script refuses when `$GIT_DIR/info/attributes`, which git cannot disable, sets anything.
When the merge is clean, nothing is written. When git's report lists exactly one conflict, a
content conflict in `references.bib`, and the entry merge resolves it, the script writes a merge
commit with parents HEAD and BASE and prints its SHA. Anything else (another file, a rename or
directory conflict, an unrecognized message) is refused with exit status 1 and no commit.
No ref is updated and nothing is pushed: publishing the commit to a branch (for example
`git push origin <sha>:refs/heads/<branch>`) is a separate, deliberate step for the branch's
author or a coordinator. This is a local plain-git check: hosted CI still runs on the result.

    python3 scripts/resolve_bib_conflict.py <head> [<base>]

Driver mode is an opt-in local git merge driver, so that an ordinary `git merge` resolves such
conflicts itself. `.gitattributes` names the driver for `references.bib`; enable it once per
clone with

    git config merge.bibkeys.driver 'python3 scripts/resolve_bib_conflict.py --driver %O %A %B'

When the entry merge refuses or fails, the driver falls back to `git merge-file`, leaving the
usual conflict markers. Where the driver is not configured (on GitHub, or in another clone), git
uses its ordinary text merge.
"""

from __future__ import annotations

import argparse
import os
import pathlib
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

BIB = "references.bib"
# Git's defaults, pinned so that local configuration cannot change which conflicts are reported.
MERGE_CONFIG = ("merge.renames=true", "merge.directoryRenames=conflict", "merge.renormalize=false")


class Refusal(Exception):
    """The entry merge cannot decide; a person must resolve the conflict."""


def split_entries(text: str, side: str) -> tuple[str, dict[str, str]]:
    """The text before the first entry and each entry block by folded key, for a sorted file."""
    from check_hygiene import BIB_KEY_RE, check_bibliography

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
    from check_hygiene import check_bibliography

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
    """Git merge driver: write the merge to `ours_path`, else fall back to a text merge.

    Any failure of the entry merge, expected or not, falls back to `git merge-file`, so the
    driver never reports a clean merge it did not make."""
    try:
        texts = [pathlib.Path(p).read_bytes().decode("utf-8")
                 for p in (base_path, ours_path, theirs_path)]
        merged = merge_bib(*texts).encode("utf-8")
        ours = pathlib.Path(ours_path).resolve()
        fd, tmp = tempfile.mkstemp(dir=ours.parent, prefix=f".{ours.name}.")
        try:
            with os.fdopen(fd, "wb") as out:
                out.write(merged)
            os.replace(tmp, ours)
        except BaseException:
            pathlib.Path(tmp).unlink(missing_ok=True)
            raise
        return 0
    except Exception as err:  # noqa: BLE001 - every failure falls back to a text merge
        print(f"resolve_bib_conflict: {err}; falling back to a text merge", file=sys.stderr)
    status = subprocess.run(["git", "merge-file", "-L", "ours", "-L", "base", "-L", "theirs",
                             ours_path, base_path, theirs_path]).returncode
    return 0 if status == 0 else 1


def environment() -> dict[str, str]:
    """The caller's environment without attribute sources or object replacement."""
    env = {key: value for key, value in os.environ.items() if key != "GIT_ATTR_SOURCE"}
    env.update(GIT_ATTR_NOSYSTEM="1", GIT_NO_REPLACE_OBJECTS="1")
    return env


def git(cwd: pathlib.Path, *args: str, stdin: bytes | None = None, ok=(0,),
        config: tuple[str, ...] = ()) -> subprocess.CompletedProcess:
    """Run git on bytes; refuse when it exits with a status outside `ok`."""
    options = [arg for item in config for arg in ("-c", item)]
    r = subprocess.run(["git", *options, *args], cwd=cwd, input=stdin, capture_output=True,
                       env=environment())
    if r.returncode not in ok:
        stderr = r.stderr.decode("utf-8", "replace").strip()
        raise Refusal(f"git {args[0]} failed with status {r.returncode}: {stderr}")
    return r


def out(r: subprocess.CompletedProcess) -> str:
    return r.stdout.decode("utf-8").strip()


def rev(cwd: pathlib.Path, name: str) -> str:
    return out(git(cwd, "rev-parse", "--verify", "--end-of-options", f"{name}^{{commit}}"))


def neutral_config(cwd: pathlib.Path) -> tuple[str, ...]:
    """Configuration under which git reads no attributes, or raise `Refusal`."""
    path = os.fsdecode(git(cwd, "rev-parse", "--path-format=absolute", "--git-path",
                           "info/attributes").stdout.rstrip(b"\n"))
    try:
        lines = pathlib.Path(path).read_bytes().splitlines()
    except FileNotFoundError:
        lines = []
    except OSError as err:
        raise Refusal(f"cannot read {path}: {err}") from err
    if any(line.strip() and not line.lstrip().startswith(b"#") for line in lines):
        raise Refusal(f"{path} sets attributes that this check cannot disable; "
                      "move them aside and retry")
    empty = out(git(cwd, "hash-object", "-t", "tree", "--stdin", "-w", stdin=b""))
    config = (f"attr.tree={empty}", f"core.attributesFile={os.devnull}", *MERGE_CONFIG)
    attrs = git(cwd, "check-attr", "-a", "-z", "--", BIB, "Complexity.lean", config=config)
    if attrs.stdout:
        raise Refusal("this git still reads tracked attributes under `attr.tree`: "
                      + attrs.stdout.decode("utf-8", "replace").replace("\0", " ").strip())
    return config


Stage = tuple[str, str, str, bytes]  # mode, object, stage number, path
Message = tuple[list[bytes], str]  # paths, type (`Auto-merging`, `CONFLICT (contents)`, ...)


def merge_report(stdout: bytes) -> tuple[str, list[Stage], list[Message]]:
    """Parse `git merge-tree --write-tree -z` output for a conflicted merge: the tree, the
    conflicted stages and the informational messages. Malformed output is refused."""
    fields = stdout.split(b"\0")
    try:
        tree, i = fields[0].decode("ascii"), 1
        stages: list[Stage] = []
        while fields[i]:
            info, path = fields[i].split(b"\t", 1)
            mode, oid, stage = info.decode("ascii").split()
            stages.append((mode, oid, stage, path))
            i += 1
        i += 1
        messages: list[Message] = []
        while fields[i]:
            n = int(fields[i])
            if n < 1:
                raise ValueError(f"{n} paths")
            paths, kind, _text = fields[i + 1:i + 1 + n], fields[i + 1 + n], fields[i + 2 + n]
            messages.append((paths, kind.decode("utf-8", "replace")))
            i += n + 3
        if i != len(fields) - 1:
            raise ValueError(f"trailing fields after field {i}")
    except (IndexError, ValueError, UnicodeDecodeError) as err:
        raise Refusal(f"unexpected `git merge-tree` output ({err})") from err
    return tree, stages, messages


def resolve(head: str, base: str, cwd: pathlib.Path | None = None) -> str | None:
    """Commit mode: the SHA of the resolving merge commit, None if clean, or raise `Refusal`.

    Runs in the repository containing `cwd` (default: the current directory)."""
    cwd = cwd or pathlib.Path.cwd()
    head_sha, base_sha = rev(cwd, head), rev(cwd, base)
    config = neutral_config(cwd)
    r = git(cwd, "merge-tree", "--write-tree", "-z", head_sha, base_sha, ok=(0, 1),
            config=config)
    if r.returncode == 0:
        return None
    tree, stages, messages = merge_report(r.stdout)
    bib = BIB.encode()
    conflicts = [(paths, kind) for paths, kind in messages if kind != "Auto-merging"]
    if conflicts != [([bib], "CONFLICT (contents)")]:
        listed = "; ".join(f"{kind}: {', '.join(map(os.fsdecode, paths))}"
                           for paths, kind in conflicts)
        raise Refusal(f"conflicts other than one content conflict in {BIB}: {listed}")
    if (sorted(stage for _, _, stage, _ in stages) != ["1", "2", "3"]
            or any(path != bib or mode != "100644" for mode, _, _, path in stages)):
        raise Refusal(f"the {BIB} conflict is not between three versions of a regular file")
    oids = {stage: oid for _, oid, stage, _ in stages}
    try:
        texts = [git(cwd, "cat-file", "blob", oids[s]).stdout.decode("utf-8") for s in "123"]
    except UnicodeDecodeError as err:
        raise Refusal(f"{BIB} is not UTF-8: {err}") from err
    merged = merge_bib(*texts)
    blob = out(git(cwd, "hash-object", "-w", "--stdin", stdin=merged.encode("utf-8")))
    rows = [row for row in git(cwd, "ls-tree", "-z", tree).stdout.split(b"\0") if row]
    hits = [k for k, row in enumerate(rows) if row.split(b"\t", 1)[1:] == [bib]]
    if len(hits) != 1 or not rows[hits[0]].startswith(b"100644 blob "):
        raise Refusal(f"the merged tree has no regular top-level {BIB}")
    rows[hits[0]] = f"100644 blob {blob}\t{BIB}".encode()
    new_tree = out(git(cwd, "mktree", "-z", stdin=b"\0".join(rows) + b"\0"))
    message = (f"Merge {base} into {head}\n\nResolve the {BIB} conflict entry by entry with "
               "scripts/resolve_bib_conflict.py.\n")
    return out(git(cwd, "commit-tree", new_tree, "-p", head_sha, "-p", base_sha, "-m", message))


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
