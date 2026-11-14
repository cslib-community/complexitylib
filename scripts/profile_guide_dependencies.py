#!/usr/bin/env python3
"""One-off hosted Guide dependency experiment; never a production build helper."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time


ROOT = Path.cwd().resolve()
TEMP = Path(os.environ["RUNNER_TEMP"]).resolve() / "guide-dependency-profile"
REPORT = TEMP / "report"
DEPS = ("verso", "subverso", "MD4Lean", "illuminate")


def save(name: str, value: object) -> None:
    (REPORT / name).write_text(json.dumps(value, indent=2) + "\n")


def run(name: str, args: list[str], cache: Path) -> dict:
    env = os.environ | {"LAKE_CACHE_DIR": str(cache)}
    print(f"::group::{name}", flush=True)
    start = time.time()
    with (REPORT / f"{name}.log").open("w") as log:
        proc = subprocess.Popen(
            ["/usr/bin/time", "-v", "-o", str(REPORT / f"{name}.time"), *args],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env,
        )
        assert proc.stdout is not None
        for line in proc.stdout:
            stamp = f"{time.time():.6f} "
            log.write(stamp + line)
            print(line, end="", flush=True)
        status = proc.wait()
    result = {"args": args, "started": start, "ended": time.time(), "status": status}
    result["elapsed"] = result["ended"] - start
    save(f"{name}.json", result)
    print(json.dumps(result), flush=True)
    print("::endgroup::", flush=True)
    if status:
        raise subprocess.CalledProcessError(status, args)
    return result


def fingerprint(directory: Path, exclude_deps: bool = False) -> dict:
    """Hash bytes, paths and permissions; ignore Git controls, times, and inode identities."""
    digest = hashlib.sha256()
    count = size = 0
    for current, dirs, files in os.walk(directory):
        here = Path(current)
        dirs[:] = sorted(d for d in dirs if d != ".git" and not (
            exclude_deps and here == directory / "packages" and d in DEPS
        ))
        for name in sorted(files):
            path = here / name
            rel = path.relative_to(directory).as_posix()
            if path.is_symlink():
                data_hash = hashlib.sha256(os.readlink(path).encode()).hexdigest()
                nbytes = len(os.readlink(path))
            else:
                item = hashlib.sha256()
                with path.open("rb") as file:
                    for chunk in iter(lambda: file.read(4 * 1024 * 1024), b""):
                        item.update(chunk)
                data_hash = item.hexdigest()
                nbytes = path.stat().st_size
            digest.update(f"{rel}\0{path.lstat().st_mode:o}\0{nbytes}\0{data_hash}\n".encode())
            count += 1
            size += nbytes
    return {"sha256": digest.hexdigest(), "files": count, "bytes": size}


def inventory(directory: Path) -> dict:
    counts: dict[str, dict[str, int]] = {}
    for path in sorted(directory.rglob("*")):
        if path.is_file():
            ext = path.suffix or "<none>"
            entry = counts.setdefault(ext, {"files": 0, "bytes": 0})
            entry["files"] += 1
            entry["bytes"] += path.stat().st_size
    return {"files": sum(v["files"] for v in counts.values()),
            "bytes": sum(v["bytes"] for v in counts.values()), "extensions": counts}


def source_identity() -> dict:
    files = subprocess.check_output(["git", "ls-files", "-z"]).split(b"\0")
    digest = hashlib.sha256()
    for item in sorted(item for item in files if item):
        path = ROOT / os.fsdecode(item)
        digest.update(item + b"\0" + hashlib.sha256(path.read_bytes()).digest())
    return {"head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
            "tracked_sha256": digest.hexdigest(),
            "pins": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
                     for p in ("lean-toolchain", "lake-manifest.json", "guide/lake-manifest.json",
                               "lakefile.toml", "guide/lakefile.toml")}}


def arm(name: str) -> dict:
    cache = TEMP / f"artifact-cache-{name}"
    assert not cache.exists(), f"artifact store must start empty: {cache}"
    guide_build = ROOT / "guide/.lake/build"
    assert not guide_build.exists(), "chapter/native/site outputs must start absent"
    before = fingerprint(ROOT / ".lake", exclude_deps=True)
    save(f"{name}-root-before.json", before)
    if before != json.loads((REPORT / "baseline-root.json").read_text()):
        raise RuntimeError("root/shared baseline differs before measured arm")
    save(f"{name}-source-before.json", source_identity())
    phases = []
    # These are the normal workflow's commands and scripts/guide.sh expanded into timed phases.
    # Only -q/--log-level=error are replaced, so successful build tasks become observable.
    phases.append(run(f"{name}-examples",
                      ["lake", "-d", "guide", "build", "--log-level=info", "CslibFrontierGuide"], cache))
    phases.append(run(f"{name}-pins", ["python3", "scripts/check_docs.py", "--config-only"], cache))
    phases.append(run(f"{name}-native", ["lake", "-d", "guide", "build", "--log-level=info"], cache))
    site = guide_build / "site"
    if site.exists():
        shutil.rmtree(site)
    phases.append(run(f"{name}-render",
                      ["lake", "--log-level=info", "-d", "guide", "exe", "guide", "--output", str(site)], cache))
    if not (site / "html-multi/index.html").is_file():
        raise RuntimeError("normal Guide output is missing")
    inventories = {dep: inventory(ROOT / ".lake/packages" / dep / ".lake/build") for dep in DEPS}
    inventories["guide"] = inventory(guide_build)
    save(f"{name}-inventories.json", inventories)
    save(f"{name}-root-after.json", fingerprint(ROOT / ".lake", exclude_deps=True))
    save(f"{name}-site.json", fingerprint(site))
    return {"phases": phases, "inventories": inventories}


def main() -> None:
    if os.environ.get("GITHUB_ACTIONS") != "true":
        raise SystemExit("This diagnostic only runs on its disposable hosted job.")
    if TEMP.exists():
        raise SystemExit("Diagnostic directory already exists; refusing to reuse it.")
    REPORT.mkdir(parents=True)
    save("source.json", source_identity())
    run("initialize-packages", ["lake", "-d", "guide", "env", "true"], TEMP / "artifact-cache-initialize")
    packages = ROOT / ".lake/packages"
    for dep in DEPS:
        build = packages / dep / ".lake/build"
        if build.exists():
            shutil.rmtree(build)
    guide_build = ROOT / "guide/.lake/build"
    if guide_build.exists():
        shutil.rmtree(guide_build)
    save("dependency-pins.json", {
        dep: subprocess.check_output(["git", "-C", str(packages / dep), "rev-parse", "HEAD"], text=True).strip()
        for dep in DEPS
    })
    baseline = TEMP / "baseline-lake"
    run("snapshot-baseline", ["cp", "-a", "--reflink=auto", str(ROOT / ".lake"), str(baseline)], TEMP / "artifact-cache-initialize")
    save("baseline-root.json", fingerprint(ROOT / ".lake", exclude_deps=True))
    results = {"cold": arm("cold")}
    # Retain only the four Guide-only dependency builds. Every root/shared output is reset,
    # including diagnostic traces, so pass two cannot reuse work done there by pass one.
    reset = ["rsync", "-a", "--delete", "--checksum"]
    reset.extend(f"--exclude=/packages/{dep}/" for dep in DEPS)
    reset.extend([str(baseline) + "/", str(ROOT / ".lake") + "/"])
    run("reset-root-baseline", reset, TEMP / "artifact-cache-initialize")
    shutil.rmtree(guide_build)
    results["dependency-warm"] = arm("dependency-warm")
    after = source_identity()
    if after != json.loads((REPORT / "source.json").read_text()):
        raise RuntimeError("tracked source/pins changed during experiment")
    save("results.json", results)
    # Size a concrete dependency-only payload after the measured phases; never upload it to
    # Actions cache. This reports compression overhead and bytes, not network restore speed.
    archive = TEMP / "guide-dependencies.tar.zst"
    run("compress-dependencies", ["tar", "--zstd", "-cf", str(archive),
        *[f".lake/packages/{dep}/.lake/build" for dep in DEPS]], TEMP / "artifact-cache-initialize")
    save("archive.json", {"compressed_bytes": archive.stat().st_size,
                         "paths": [f".lake/packages/{dep}/.lake/build" for dep in DEPS]})
    print(json.dumps({"results": results, "archive_bytes": archive.stat().st_size}), flush=True)


if __name__ == "__main__":
    main()
