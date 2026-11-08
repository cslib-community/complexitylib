#!/usr/bin/env python3
"""Report whether an aggregate-only conflict has an exact canonical Git merge.

The aggregates are `Complexity.lean` and its directory shards under `Complexity/All/`, generated
by `scripts/mk_all.py`. All four inputs must be full commit IDs available locally. Git writes
only to a temporary repository; the inspected repository is read-only. See aggregate_merge.md
for the contract.
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

sys.path.insert(0, str(Path(__file__).resolve().parent))
import mk_all  # noqa: E402

AGGREGATE = "Complexity.lean"
SHARDS = f"Complexity/{mk_all.SHARD_DIR}/"
# scripts/mk_all.py, module-style root; intentionally not a general Lean header parser.
MODULE_HEADER = (mk_all.MODULE_HEADER + "\n").encode()
COMPONENT = mk_all.COMPONENT  # quick_check.source_modules convention
OID = re.compile(r"[0-9a-f]{40}\Z")


class Rejected(Exception):
    """An input or merge is outside this verifier's bounded contract."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Rejected(message)


def is_aggregate(path: str) -> bool:
    return path == AGGREGATE or path.startswith(SHARDS)


def blob_oid(content: bytes) -> str:
    """The SHA-1 object ID that Git gives a blob with this content."""
    return hashlib.sha1(b"blob %d\0" % len(content) + content).hexdigest()


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

    def set_aggregates(self, files: dict[str, dict[str, str]]) -> str:
        """Replace every aggregate in the index by `files` and write the tree."""
        current = [p for p in self.run("ls-files", "-z").stdout.decode().split("\0")
                   if p and is_aggregate(p)]
        # `--index-info` removes a path given mode 0, then adds the new entries.
        lines = [f"0 {'0' * 40}\t{path}" for path in current]
        lines += [f"{entry['mode']} {entry['oid']}\t{path}" for path, entry in sorted(files.items())]
        self.run("update-index", "--index-info", data="".join(f"{line}\n" for line in lines).encode())
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


def canonical(entries: dict[str, dict[str, str]]) -> dict[str, bytes]:
    """Mirror scripts/mk_all.py for the Complexity root: the aggregates of every .lean module
    outside `Complexity/All/`, by path."""
    modules = []
    for path, entry in entries.items():
        if path.startswith("Complexity/") and path.endswith(".lean") and not is_aggregate(path):
            parts = path[len("Complexity/"):-5].split("/")
            require(all(COMPONENT.fullmatch(part) for part in parts) and
                    parts != [mk_all.SHARD_DIR], f"unsupported module path: {path}")
            require(entry["type"] == "blob" and entry["mode"] in {"100644", "100755"},
                    f"nonregular Lean module: {path}")
            modules.append(tuple(parts))
    require(bool(modules), "empty Complexity library")
    files = mk_all.generate(mk_all.Library("Complexity", Path(".")), sorted(modules), True)
    return {path.as_posix(): text.encode() for path, text in files.items()}


def canonical_entries(files: dict[str, bytes]) -> dict[str, dict[str, str]]:
    return {path: {"mode": "100644", "type": "blob", "oid": blob_oid(content)}
            for path, content in files.items()}


def check_aggregate(git: Git, entries: dict, label: str) -> None:
    require("lakefile.lean" not in entries and "lakefile.toml" in entries,
            f"{label}: unsupported Lake configuration")
    config = tomllib.loads(git.blob(entries["lakefile.toml"]).decode())
    libraries = config.get("lean_lib", [])
    require(isinstance(libraries, list), f"{label}: invalid Lake libraries")
    roots = [lib for lib in libraries if isinstance(lib, dict) and lib.get("name") == "Complexity"]
    require(config.get("srcDir", ".") == "." and len(roots) == 1 and
            roots[0].get("srcDir", ".") == "." and
            roots[0].get("roots", ["Complexity"]) == ["Complexity"] and "globs" not in roots[0],
            f"{label}: unsupported Complexity library layout")
    require(AGGREGATE in entries and entries[AGGREGATE]["mode"] == "100644",
            f"{label}: missing or nonregular aggregate")
    content = git.blob(entries[AGGREGATE])
    require(content.startswith(MODULE_HEADER), f"{label}: changed known aggregate preamble")
    # Exact generation rejects options/declarations, comments, malformed, repeated, missing,
    # extra and unsorted imports, in the root and every shard, and missing or obsolete shards.
    # General Lean parsing would accept too much here.
    actual = {p: e for p, e in entries.items() if is_aggregate(p)}
    require(actual == canonical_entries(canonical(entries)),
            f"{label}: aggregate is not canonical for its inventory")


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
    require(attrs == b"Complexity.lean\0merge\0unspecified\0", "cannot disable tracked attributes")
    status, neutral, conflicts = merge(git, prefix, source, empty)
    report.update(neutral_tree=neutral, conflicts=conflicts)
    require(status == 1 and bool(conflicts) and all(map(is_aggregate, conflicts)),
            f"complete neutral conflict set must be generated aggregates only "
            f"({AGGREGATE!r} and {SHARDS}*), got {conflicts!r}")
    merged = git.entries(neutral)
    files = canonical(merged)
    aggregates = canonical_entries(files)
    for path, content in files.items():
        if merged.get(path) != aggregates[path]:
            written = git.run("hash-object", "-w", "--stdin", data=content).stdout.decode().strip()
            require(written == aggregates[path]["oid"], "unexpected blob ID")
    git.run("read-tree", neutral)
    candidate = git.set_aggregates(aggregates)
    candidate_entries = git.entries(candidate)
    require({p: e for p, e in merged.items() if not is_aggregate(p)} ==
            {p: e for p, e in candidate_entries.items() if not is_aggregate(p)},
            "canonicalization changed a nonaggregate entry")
    feature = git.run("diff", "--no-ext-diff", "--no-textconv", "--no-renames", "--binary",
                      "--full-index", reviewed_base, reviewed_head, "--", ".",
                      f":(exclude){AGGREGATE}", f":(exclude){SHARDS}").stdout
    require(bool(feature), "reviewed feature has no nonaggregate payload")
    own_paths = sorted(p for p in inventories["reviewed_base"].keys() | inventories["reviewed_head"].keys()
                       if not is_aggregate(p) and inventories["reviewed_base"].get(p) !=
                       inventories["reviewed_head"].get(p))
    for path in own_paths:
        require(candidate_entries.get(path) == inventories["reviewed_head"].get(path),
                f"reviewed payload mode/blob changed: {path}")
    # Whole-feature replay is stronger than checking only the named Lean payloads. It also
    # guards docs, removals, modes and every unrelated accepted-prefix entry.
    git.run("read-tree", prefix)
    git.run("apply", "--cached", "--binary", data=feature)
    require(git.set_aggregates(aggregates) == candidate,
            "feature forward replay does not recover candidate")
    git.run("read-tree", candidate)
    git.run("apply", "--cached", "--binary", "--reverse", data=feature)
    recovered = git.set_aggregates({p: e for p, e in inventories["prefix"].items() if is_aggregate(p)})
    require(recovered == report["input_trees"]["prefix"], "feature inverse does not recover exact prefix")
    digest = hashlib.sha256()
    for path, content in sorted(files.items()):
        digest.update(path.encode() + b"\0" + content + b"\0")
    report.update(candidate_tree=candidate, candidate_entries=candidate_entries,
                  reviewed_paths=own_paths, reviewed_entries={p: candidate_entries.get(p) for p in own_paths},
                  feature_patch_sha256=hashlib.sha256(feature).hexdigest(), recovered_prefix_tree=recovered,
                  canonical_aggregate_sha256=digest.hexdigest(), canonical_aggregate_files=len(files),
                  canonical_import_count=sum(1 for content in files.values()
                                             for line in content.decode().splitlines()
                                             if line.startswith("public import ") and
                                             not line.startswith(f"public import Complexity.{mk_all.SHARD_DIR}.")))
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
