#!/usr/bin/env python3
# Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Christian Reitwiessner
"""Count daily first-parent Git snapshots with Tokei and build a static Pages site."""
import argparse
import csv
import datetime as dt
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import tarfile
import tempfile

HERE = Path(__file__).resolve().parent
VERSION = "tokei 12.1.2"
METRICS = ("code", "comments", "blanks", "files")


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def daily_snapshots(repo, ref, until):
    """Latest first-parent ancestor at each UTC day end; carry forward quiet days.

    Compare timestamps but choose by ancestry order, even with skewed commit clocks.
    """
    commits = [line.split() for line in git(
        repo, "rev-list", "--first-parent", "--reverse", "--timestamp", ref
    ).decode().splitlines()]
    first = min(dt.datetime.fromtimestamp(int(t), dt.timezone.utc).date() for t, _ in commits)
    rows = []
    day = first
    while day <= until:
        cutoff = int(dt.datetime.combine(day + dt.timedelta(days=1), dt.time(), dt.timezone.utc).timestamp())
        eligible = [sha for timestamp, sha in commits if int(timestamp) < cutoff]
        if eligible:
            rows.append((day.isoformat(), eligible[-1]))
        day += dt.timedelta(days=1)
    return rows


def category(path, categories):
    for cat in categories:
        if path in cat.get("files", []) or any(path.startswith(p) for p in cat.get("prefixes", [])):
            return cat["id"]
    return next(cat["id"] for cat in categories if cat.get("fallback"))


def count_snapshot(repo, sha, tokei, categories):
    totals = {cat["id"]: dict.fromkeys(METRICS, 0) for cat in categories}
    # Stream tracked .lean blobs only: dependencies, ignored files and worktree dirt never enter.
    # Do not extract tar paths or symlinks; write only regular Lean blobs under a temporary root.
    with tempfile.TemporaryDirectory(prefix="frontier-stats-") as scratch:
        root = Path(scratch)
        proc = subprocess.Popen(["git", "-C", str(repo), "archive", sha], stdout=subprocess.PIPE)
        try:
            with tarfile.open(fileobj=proc.stdout, mode="r|") as archive:
                for member in archive:
                    path = PurePosixPath(member.name)
                    if not member.isfile() or path.suffix != ".lean":
                        continue
                    if path.is_absolute() or ".." in path.parts:
                        raise ValueError(f"Unsafe archive path: {path}")
                    target = root / path
                    target.parent.mkdir(parents=True, exist_ok=True)
                    with archive.extractfile(member) as source, target.open("wb") as dest:
                        shutil.copyfileobj(source, dest)
            if proc.wait() != 0:
                raise RuntimeError("git archive failed")
        finally:
            proc.stdout.close()
            if proc.poll() is None:
                proc.kill()
                proc.wait()
        report = json.loads(subprocess.check_output([
            tokei, "--output", "json", "--type", "Lean", "--hidden", "--no-ignore", str(root)
        ]))
        for item in report.get("Lean", {}).get("reports", []):
            path = Path(item["name"]).relative_to(root).as_posix()
            total = totals[category(path, categories)]
            for metric in METRICS[:-1]:
                total[metric] += item["stats"][metric]
            total["files"] += 1
    return totals


def build(repo, ref, until, tokei, config, cache, output):
    version = subprocess.check_output([tokei, "--version"], text=True).strip()
    if " ".join(version.split()[:2]) != VERSION:
        raise ValueError(f"Expected {VERSION}, got {version}")
    if git(repo, "rev-parse", "--is-shallow-repository").strip() == b"true":
        raise ValueError("Full Git history is required (checkout fetch-depth: 0)")
    categories = config["categories"]
    ids = [cat["id"] for cat in categories]
    if len(set(ids)) != len(ids) or sum(bool(c.get("fallback")) for c in categories) != 1:
        raise ValueError("Category ids must be unique, with exactly one fallback")
    fingerprint = hashlib.sha256(
        (VERSION + json.dumps(config, sort_keys=True)).encode() + Path(__file__).read_bytes()
    ).hexdigest()
    cache = cache / fingerprint
    cache.mkdir(parents=True, exist_ok=True)
    snapshots = []
    for date, sha in daily_snapshots(repo, ref, until):
        saved = cache / f"{sha}.json"
        if saved.exists():
            counts = json.loads(saved.read_text())
        else:
            print(f"Counting {date} {sha[:10]}", flush=True)
            counts = count_snapshot(repo, sha, tokei, categories)
            saved.write_text(json.dumps(counts, sort_keys=True) + "\n")
        snapshots.append({"date": date, "commit": sha, "categories": counts})
    output.mkdir(parents=True, exist_ok=True)
    data = {"schema": 1, "generated_at": dt.datetime.now(dt.timezone.utc).isoformat(),
            "head": git(repo, "rev-parse", ref).decode().strip(), "tokei": VERSION,
            "categories": categories, "snapshots": snapshots}
    (output / "data.json").write_text(json.dumps(data, indent=2) + "\n")
    with (output / "data.csv").open("w", newline="") as file:
        writer = csv.writer(file)
        writer.writerow(["date", "commit", "category", *METRICS])
        for row in snapshots:
            for cat, counts in row["categories"].items():
                writer.writerow([row["date"], row["commit"], cat, *(counts[m] for m in METRICS)])
    for name in ("index.html", "style.css", "dashboard.js"):
        shutil.copyfile(HERE / name, output / name)
    print(f"Built {len(snapshots)} daily snapshots in {output}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=HERE.parents[1])
    parser.add_argument("--ref", default="HEAD")
    parser.add_argument("--until", type=dt.date.fromisoformat, default=dt.datetime.now(dt.timezone.utc).date())
    parser.add_argument("--tokei", default="tokei")
    parser.add_argument("--config", type=Path, default=HERE / "config.json")
    parser.add_argument("--cache", type=Path, default=HERE / ".cache")
    parser.add_argument("--output", type=Path, default=HERE / "_site")
    args = parser.parse_args()
    build(args.repo, args.ref, args.until, args.tokei, json.loads(args.config.read_text()), args.cache, args.output)


if __name__ == "__main__":
    main()
