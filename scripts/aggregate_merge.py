#!/usr/bin/env python3
"""Report whether an aggregate-only conflict has an exact canonical Git merge.

All four inputs must be full commit IDs available locally. Git writes only to a temporary
repository; the inspected repository is read-only. See aggregate_merge.md for the contract.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import tomllib


AGGREGATE = "CslibFrontier.lean"
# scripts/MkAll.lean, module-style branch; intentionally not a general Lean header parser.
MODULE_HEADER = b"module  -- shake: keep-all --deprecated_module: ignore\n\n"
COMPONENT = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")  # quick_check.source_modules convention
OID = re.compile(r"[0-9a-f]{40}\Z")


class Rejected(Exception):
    """An input or merge is outside this verifier's bounded contract."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Rejected(message)


def environment() -> dict[str, str]:
    # Do not inherit replacement objects, index/object directories or user merge drivers.
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull,
               GIT_ATTR_NOSYSTEM="1", GIT_NO_REPLACE_OBJECTS="1", GIT_OPTIONAL_LOCKS="0")
    return env


class Git:
    def __init__(self, root: Path, env: dict[str, str]):
        self.root, self.env = root, env

    def run(self, *args: str, data: bytes | None = None, allowed=(0,)):
        result = subprocess.run(
            ["git", "-c", "gc.auto=0", "-c", "maintenance.auto=false",
             "-c", "pack.threads=2", "-c", "fetch.parallel=1",
             "-c", f"core.attributesFile={os.devnull}", "-c", f"core.hooksPath={os.devnull}",
             *args], cwd=self.root, env=self.env, input=data, capture_output=True)
        require(result.returncode in allowed,
                f"git {args[0]} failed: {result.stderr.decode(errors='replace').strip()}")
        return result

    def text(self, *args: str) -> str:
        return self.run(*args).stdout.decode().strip()

    def entries(self, tree: str) -> dict[str, dict[str, str]]:
        entries = {}
        for row in self.run("ls-tree", "-rz", tree).stdout.split(b"\0"):
            if row:
                metadata, path = row.split(b"\t", 1)
                mode, kind, oid = metadata.decode().split()
                entries[path.decode()] = {"mode": mode, "type": kind, "oid": oid}
        return entries

    def blob(self, entry: dict[str, str]) -> bytes:
        require(entry["type"] == "blob", "expected a blob")
        return self.run("cat-file", "blob", entry["oid"]).stdout

    def set_aggregate(self, entry: dict[str, str]) -> str:
        self.run("update-index", "--add", "--cacheinfo", entry["mode"], entry["oid"], AGGREGATE)
        return self.text("write-tree")


@contextmanager
def scratch_git(repo: Path, commits: tuple[str, ...]):
    require(all(OID.fullmatch(oid) for oid in commits), "use full immutable commit IDs")
    source = Git(repo, environment())
    require(source.text("rev-parse", "--show-object-format") == "sha1", "only SHA-1 is supported")
    require(source.text("rev-parse", "--is-shallow-repository") == "false",
            "shallow source repositories are unsupported")
    objects = Path(source.text("rev-parse", "--path-format=absolute", "--git-path", "objects"))
    common = Path(source.text("rev-parse", "--path-format=absolute", "--git-common-dir"))
    with tempfile.TemporaryDirectory(prefix="aggregate-merge-") as directory:
        root = Path(directory)
        source.run("init", "--bare", "--quiet", "--template=", "--object-format=sha1", str(root))
        git = Git(root, environment())
        require(Path(git.text("rev-parse", "--absolute-git-dir")).resolve() == root.resolve() and
                Path(git.text("rev-parse", "--path-format=absolute", "--git-common-dir")).resolve()
                == root.resolve() and root.resolve() != common.resolve(),
                "temporary repository does not have an independent common directory")
        own_objects = Path(git.text("rev-parse", "--path-format=absolute", "--git-path", "objects"))
        require(own_objects.resolve() == (root / "objects").resolve() and
                own_objects.resolve() != objects.resolve() and not (root / ".git").exists(),
                "temporary object directory is not independent")
        # Check identity before fetching or writing merge/index objects. A normal file://
        # fetch uses upload-pack, unlike clone's local hard-link shortcut.
        git.run("fetch", "--no-tags", "--no-write-fetch-head", "--no-recurse-submodules",
                "--no-auto-maintenance", repo.as_uri(), *dict.fromkeys(commits))
        require(not (own_objects / "info/alternates").exists() and
                not (own_objects / "info/http-alternates").exists() and not (root / "shallow").exists(),
                "temporary repository contains alternates or a shallow boundary")
        source_inodes = {(p.stat().st_dev, p.stat().st_ino) for p in objects.rglob("*") if p.is_file()}
        copied = [p for p in own_objects.rglob("*") if p.is_file()]
        require(all(not p.is_symlink() and (p.stat().st_dev, p.stat().st_ino) not in source_inodes
                    for p in copied), "temporary objects share source storage")
        git.isolation = {"independent_common_directory": True, "independent_object_directory": True,
                         "no_alternates_or_shallow_boundary": True, "no_shared_object_inodes": True,
                         "fetched_object_files": len(copied)}
        yield git


def canonical(entries: dict[str, dict[str, str]]) -> bytes:
    """Mirror mk_all's CslibFrontier root: all .lean modules, sorted by module name."""
    modules = []
    for path, entry in entries.items():
        if path.startswith("CslibFrontier/") and path.endswith(".lean"):
            parts = path[:-5].split("/")
            require(all(COMPONENT.fullmatch(part) for part in parts),
                    f"unsupported module path: {path}")
            require(entry["type"] == "blob" and entry["mode"] in {"100644", "100755"},
                    f"nonregular Lean module: {path}")
            modules.append(".".join(parts))
    require(bool(modules), "empty CslibFrontier library")
    return MODULE_HEADER + b"".join(f"public import {name}\n".encode() for name in sorted(modules))


def check_aggregate(git: Git, entries: dict, label: str) -> None:
    require("lakefile.lean" not in entries and "lakefile.toml" in entries,
            f"{label}: unsupported Lake configuration")
    config = tomllib.loads(git.blob(entries["lakefile.toml"]).decode())
    libraries = config.get("lean_lib", [])
    require(isinstance(libraries, list), f"{label}: invalid Lake libraries")
    roots = [lib for lib in libraries if isinstance(lib, dict) and lib.get("name") == "CslibFrontier"]
    require(config.get("srcDir", ".") == "." and len(roots) == 1 and
            roots[0].get("srcDir", ".") == "." and
            roots[0].get("roots", ["CslibFrontier"]) == ["CslibFrontier"] and "globs" not in roots[0],
            f"{label}: unsupported CslibFrontier library layout")
    require(AGGREGATE in entries and entries[AGGREGATE]["mode"] == "100644",
            f"{label}: missing or nonregular aggregate")
    content = git.blob(entries[AGGREGATE])
    require(content.startswith(MODULE_HEADER), f"{label}: changed known aggregate preamble")
    # Exact generation rejects options/declarations, comments, malformed, repeated, missing,
    # extra and unsorted imports. General Lean parsing would accept too much here.
    require(content == canonical(entries), f"{label}: aggregate is not canonical for its inventory")


def merge(git: Git, prefix: str, source: str, attributes: str):
    result = git.run("-c", f"attr.tree={attributes}", "merge-tree", "--write-tree",
                     "--name-only", "-z", prefix, source, allowed=(0, 1))
    fields = result.stdout.split(b"\0")
    tree = fields.pop(0).decode()
    require(bool(OID.fullmatch(tree)), "unexpected merge-tree output (Git >= 2.43 required)")
    conflicts = []
    for field in fields:
        if not field:
            break
        conflicts.append(field.decode())
    return result.returncode, tree, conflicts


def verify(git: Git, prefix: str, source: str, reviewed_base: str, reviewed_head: str,
           report: dict) -> None:
    refs = {"prefix": prefix, "source": source,
            "reviewed_base": reviewed_base, "reviewed_head": reviewed_head}
    for label, oid in refs.items():
        require(bool(OID.fullmatch(oid)), f"{label}: use a full immutable commit ID")
        require(git.text("rev-parse", "--verify", f"{oid}^{{commit}}") == oid,
                f"{label}: expected a commit")
    require(git.run("merge-base", "--is-ancestor", reviewed_base, reviewed_head,
                    allowed=(0, 1)).returncode == 0, "reviewed base is not an ancestor of reviewed head")
    require(git.run("merge-base", "--is-ancestor", reviewed_head, source,
                    allowed=(0, 1)).returncode == 0, "source does not retain reviewed history")
    require(len(git.text("merge-base", "--all", prefix, source).splitlines()) == 1,
            "merge needs exactly one base")
    inventories = {label: git.entries(oid) for label, oid in refs.items()}
    for label, entries in inventories.items():
        check_aggregate(git, entries, label)
    report.update(inputs=refs, isolation=git.isolation,
                  input_trees={label: git.text("rev-parse", f"{oid}^{{tree}}")
                                          for label, oid in refs.items()})
    empty = git.run("hash-object", "-t", "tree", "--stdin", "-w", data=b"").stdout.decode().strip()
    # attr.tree must actually disable the tracked union attribute on this Git version.
    attrs = git.run("-c", f"attr.tree={empty}", "check-attr", "-z", "merge", "--", AGGREGATE).stdout
    require(attrs == b"CslibFrontier.lean\0merge\0unspecified\0", "cannot disable tracked attributes")
    status, neutral, conflicts = merge(git, prefix, source, empty)
    report.update(neutral_tree=neutral, conflicts=conflicts)
    require(status == 1 and conflicts == [AGGREGATE],
            f"complete neutral conflict set must be exactly [{AGGREGATE!r}], got {conflicts!r}")
    merged = git.entries(neutral)
    content = canonical(merged)
    entry = {"mode": "100644", "type": "blob",
             "oid": git.run("hash-object", "-w", "--stdin", data=content).stdout.decode().strip()}
    git.run("read-tree", neutral)
    candidate = git.set_aggregate(entry)
    candidate_entries = git.entries(candidate)
    require({p: e for p, e in merged.items() if p != AGGREGATE} ==
            {p: e for p, e in candidate_entries.items() if p != AGGREGATE},
            "canonicalization changed a nonaggregate entry")
    feature = git.run("diff", "--no-ext-diff", "--no-textconv", "--no-renames", "--binary",
                      "--full-index", reviewed_base, reviewed_head, "--", ".",
                      ":(exclude)CslibFrontier.lean").stdout
    require(bool(feature), "reviewed feature has no nonaggregate payload")
    own_paths = sorted(p for p in inventories["reviewed_base"].keys() | inventories["reviewed_head"].keys()
                       if p != AGGREGATE and inventories["reviewed_base"].get(p) !=
                       inventories["reviewed_head"].get(p))
    for path in own_paths:
        require(candidate_entries.get(path) == inventories["reviewed_head"].get(path),
                f"reviewed payload mode/blob changed: {path}")
    # Whole-feature replay is stronger than checking only the named Lean payloads. It also
    # guards docs, removals, modes and every unrelated accepted-prefix entry.
    git.run("read-tree", prefix)
    git.run("apply", "--cached", "--binary", data=feature)
    require(git.set_aggregate(entry) == candidate, "feature forward replay does not recover candidate")
    git.run("read-tree", candidate)
    git.run("apply", "--cached", "--binary", "--reverse", data=feature)
    recovered = git.set_aggregate(inventories["prefix"][AGGREGATE])
    require(recovered == report["input_trees"]["prefix"], "feature inverse does not recover exact prefix")
    report.update(candidate_tree=candidate, candidate_entries=candidate_entries,
                  reviewed_paths=own_paths, reviewed_entries={p: candidate_entries.get(p) for p in own_paths},
                  feature_patch_sha256=hashlib.sha256(feature).hexdigest(), recovered_prefix_tree=recovered,
                  canonical_aggregate_sha256=hashlib.sha256(content).hexdigest(),
                  canonical_import_count=len(content.splitlines()) - 2)
    # A private canonical tree is not an admission mechanism. The ordinary tracked-attribute
    # merge, in the target-prefix direction, must produce exactly that tree itself.
    status, default, conflicts = merge(git, prefix, source, prefix)
    report.update(default_merge_tree=default, default_conflicts=conflicts)
    if status != 0 or conflicts or default != candidate:
        report["status"] = "limitation"
        raise Rejected("ordinary tracked-attribute merge cannot represent the exact canonical candidate; "
                       "refresh the source branch through its owner")
    report["status"] = "verified"


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    for name in ("prefix", "source", "reviewed-base", "reviewed-head"):
        parser.add_argument(f"--{name}", required=True)
    args = parser.parse_args(argv)
    report = {"status": "rejected", "report_only": True,
              "limits": "No source review, CI, hosted candidate or queue authority is certified."}
    try:
        with scratch_git(args.repo.resolve(),
                         (args.prefix, args.source, args.reviewed_base, args.reviewed_head)) as git:
            verify(git, args.prefix, args.source, args.reviewed_base, args.reviewed_head, report)
    except (Rejected, OSError, ValueError) as error:
        report["reason"] = str(error)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["status"] == "verified" else 1


if __name__ == "__main__":
    sys.exit(main())
