#!/usr/bin/env python3
"""Report how the local copies of unmerged upstream work compare with upstream.

Usage:
    scripts/upstream_sync.py [--offline]

Modules copied from work that has not yet merged into cslib carry one of these markers:

    -- upstream: submitted #N @SHA            a copy of an open cslib pull request at head SHA
    -- upstream: vendored <owner>:<branch> @SHA (unsubmitted)
                                              a copy of a branch of <owner>'s fork of cslib with
                                              no pull request yet; without `<owner>:`, the owner is
                                              the first component of the branch name

For every such module the script reports one of:

    MERGED    the pull request has merged: bump the cslib pin past it and delete the copy
    MOVED     the pull request or branch head moved since the copy: re-sync the copy
    CLOSED    the pull request was closed unmerged: decide whether to keep the copy
    CURRENT   the copy matches the current head
    UNTRACKED the marker records no SHA, so drift cannot be checked

Markers can also introduce copied blocks in otherwise candidate modules; each is checked.
It also compares the cslib pin in `lakefile.toml` with upstream `main`. It needs `gh` and
`git` with network access; `--offline` only lists the markers.
The pin comparison reports CURRENT, DIFFERS or UNTRACKED; unequal hashes alone do not
establish whether the pin is behind upstream.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
import tomllib
from collections import defaultdict

from upstream import upstream_markers

ROOT = pathlib.Path(__file__).resolve().parent.parent
REPO = "leanprover/cslib"
SUBMITTED_RE = re.compile(r"submitted\s+#(?P<pr>\d+)(?:\s+@(?P<sha>[0-9a-f]{7,40}))?")
VENDORED_RE = re.compile(
    r"(?:vendored|subset of)\s+(?:(?P<owner>[\w.-]+):)?(?P<branch>[\w.-]+(?:/[\w.-]+)*)"
    r"(?:\s+@(?P<sha>[0-9a-f]{7,40}))?")


def run(*args: str) -> str:
    return subprocess.run(args, check=True, capture_output=True, text=True).stdout


def markers() -> list[tuple[pathlib.Path, str]]:
    found = []
    for path in sorted((ROOT / "Complexity").rglob("*.lean")):
        for status in upstream_markers(path.read_text(encoding="utf-8")):
            found.append((path.relative_to(ROOT), status))
    return found


def same(recorded: str | None, head: str) -> bool:
    return recorded is not None and head.startswith(recorded)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--offline", action="store_true")
    opts = parser.parse_args()

    prs: dict[int, list[tuple[pathlib.Path, str | None]]] = defaultdict(list)
    branches: dict[tuple[str, str], list[tuple[pathlib.Path, str | None]]] = defaultdict(list)
    for path, status in markers():
        if m := SUBMITTED_RE.match(status):
            prs[int(m.group("pr"))].append((path, m.group("sha")))
        elif m := VENDORED_RE.match(status):
            branch = m.group("branch")
            owner = m.group("owner") or branch.split("/")[0]
            branches[(owner, branch)].append((path, m.group("sha")))

    if opts.offline:
        for pr, files in sorted(prs.items()):
            print(f"#{pr}: {len(files)} file(s)")
        for (owner, branch), files in sorted(branches.items()):
            print(f"{owner}:{branch}: {len(files)} file(s)")
        return

    config = tomllib.loads((ROOT / "lakefile.toml").read_text(encoding="utf-8"))
    pinned = next((dep.get("rev") for dep in config.get("require", [])
                   if dep.get("name") == "cslib"), None)
    main_head = run("git", "ls-remote", f"https://github.com/{REPO}", "refs/heads/main").split()[0]
    state = "UNTRACKED" if not pinned else "CURRENT" if same(pinned, main_head) else "DIFFERS"
    print(f"cslib pin {(pinned or '?')[:8]}, upstream main {main_head[:8]}: {state}")

    for pr, files in sorted(prs.items()):
        info = json.loads(run("gh", "pr", "view", str(pr), "--repo", REPO,
                              "--json", "state,headRefOid,mergeCommit,title"))
        head = info["headRefOid"]
        for path, sha in files:
            if info["state"] == "MERGED":
                verdict = f"MERGED as {info['mergeCommit']['oid'][:8]}"
            elif info["state"] == "CLOSED":
                verdict = "CLOSED"
            elif sha is None:
                verdict = "UNTRACKED"
            else:
                verdict = "CURRENT" if same(sha, head) else f"MOVED to {head[:8]}"
            print(f"#{pr} {verdict:<22} {path}")

    for (owner, branch), files in sorted(branches.items()):
        out = run("git", "ls-remote", f"https://github.com/{owner}/cslib", f"refs/heads/{branch}")
        head = out.split()[0] if out else None
        for path, sha in files:
            if head is None:
                verdict = "BRANCH GONE"
            elif sha is None:
                verdict = "UNTRACKED"
            else:
                verdict = "CURRENT" if same(sha, head) else f"MOVED to {head[:8]}"
            print(f"{owner}:{branch} {verdict:<22} {path}")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as e:
        sys.exit(f"error: {' '.join(e.cmd)} failed:\n{e.stderr}")
