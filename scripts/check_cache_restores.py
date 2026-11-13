#!/usr/bin/env python3
"""Re-elaborate local Lean files whose build outputs came from Lake's artifact cache (#4523).

Usage: python3 scripts/check_cache_restores.py [--files-from JSON] [--built-under PATH ...]
                                            [--progress | --quiet]

`lakefile.toml` enables Lake's local artifact cache, which checkouts on the same machine share.
Lake stores a module's outputs there whenever it builds them, also when the build logged warnings.
Only `--wfail` and `--iofail` turn those warnings into failures. A cache entry keeps the outputs
but not the messages. When another checkout later builds the same source, Lake restores the
outputs and writes a trace marked `"synthetic": true` with an empty log, so
`lake build --wfail --iofail` and `lake test --wfail --iofail` pass without showing the warnings.
CI does not hit this, because its remote cache is published only from `main`.

After the Lean gates, `scripts/full_check.py` runs this check for all built sources of the root
package, including unchanged clients, tests and executables. This also covers deletions and
configuration changes, which cannot use quick mode's bounded import graph. `scripts/quick_check.py`
passes its affected source files as a JSON list, plus built import aggregates and executable
source directories whose helpers may import the edited library indirectly. Missing or unreadable
traces are checked too.

It runs `lake -q lean` on each selected file whose trace is synthetic and fails when the command
fails or prints anything at all: `lake lean` exits 0 after warnings, and `--iofail` rejects
informational output too. `lake lean` first builds the file's imports and replays their logs, so
a reported message can also come from an import. Files are elaborated one at a time. This local
audit does not change Lake: a bare `lake build` still cannot replay a cached module's messages.
Outside CI, progress lists the selected count and each source before elaboration, with elapsed
audit time. `--progress` enables those lines in CI; `--quiet` suppresses them locally. Failures
and the final summary are always printed.
"""

from __future__ import annotations

import argparse
from collections.abc import Sequence
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]


def layout(root: Path) -> tuple[Path, list[Path]]:
    """The root package's Lean build directory, and the source directories of its libraries and
    executables relative to `root`, most specific first (`lakefile.toml`)."""
    config = tomllib.loads((root / "lakefile.toml").read_text())
    lib_dir = root / config.get("buildDir", ".lake/build") / config.get("leanLibDir", "lib/lean")
    package = Path(config.get("srcDir", "."))
    targets = config.get("lean_lib", []) + config.get("lean_exe", [])
    dirs = {(root / package / target.get("srcDir", ".")).resolve().relative_to(root.resolve())
            for target in targets} | {(root / package).resolve().relative_to(root.resolve())}
    return lib_dir, sorted(dirs, key=lambda path: len(path.parts), reverse=True)


def trace_path(rel: str, lib_dir: Path, dirs: list[Path]) -> Path | None:
    """The existing build trace of source file `rel`, if any."""
    for directory in dirs:
        if Path(rel).is_relative_to(directory):
            trace = lib_dir / Path(rel).relative_to(directory).with_suffix(".trace")
            if trace.is_file():
                return trace
    return None


def restored(trace: Path) -> bool:
    """Whether Lake wrote `trace` when it restored the outputs from a cache rather than building
    them. An unreadable trace counts as restored, so the file is checked."""
    try:
        data = json.loads(trace.read_text())
    except (OSError, ValueError):
        return True
    return not isinstance(data, dict) or data.get("synthetic") is True


def built_files(root: Path, lib_dir: Path, dirs: list[Path]) -> set[str]:
    """Sources corresponding to root-package outputs, without scanning dependency checkouts.

    Include `.olean` files as well as traces: losing a trace must not silently omit an output.
    Stale outputs whose source was deleted are ignored; the build gates check their clients.
    """
    modules = {path.relative_to(lib_dir).with_suffix(".lean")
               for suffix in ("*.trace", "*.olean") for path in lib_dir.rglob(suffix)}
    return {(directory / module).as_posix() for directory in dirs for module in modules
            if (root / directory / module).is_file()}


def restored_files(root: Path, files: list[str] | None = None,
                   built_under: Sequence[str] = ()) -> list[str]:
    """Selected sources with restored, missing or unreadable build traces.

    Without an explicit list, cover all root-package build outputs. Extra paths select built
    aggregates or executable helper directories without forcing unbuilt sources into the audit.
    """
    lib_dir, dirs = layout(root)
    built = built_files(root, lib_dir, dirs) if files is None or built_under else set()
    selected = built if files is None else set(files)
    selected |= {rel for rel in built if any(Path(rel).is_relative_to(path) for path in built_under)}
    for rel in selected:
        path = Path(rel)
        if (path.is_absolute() or ".." in path.parts or path.suffix != ".lean"
                or not (root / path).is_file()):
            raise ValueError(f"not an existing checkout-relative Lean source: {rel!r}")
    return [rel for rel in sorted(selected)
            if (trace := trace_path(rel, lib_dir, dirs)) is None or restored(trace)]


def elaborate(root: Path, rel: str) -> subprocess.CompletedProcess:
    """Elaborate `rel` with its library's options, without writing build outputs."""
    return subprocess.run(["lake", "-q", "lean", f"./{rel}"], cwd=root, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def main(argv: list[str] | None = None, root: Path = ROOT) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--files-from", type=Path,
                        help="JSON list of affected source paths; default: all built root sources")
    parser.add_argument("--built-under", action="append", default=[],
                        help="also check built sources at this file or under this directory")
    progress = parser.add_mutually_exclusive_group()
    progress.add_argument("--progress", action="store_true", dest="progress",
                          help="show source-by-source progress, including in CI")
    progress.add_argument("--quiet", action="store_false", dest="progress",
                          help="suppress progress lines, retaining failures and the summary")
    parser.set_defaults(progress=not os.environ.get("CI"))
    args = parser.parse_args(argv)
    started = time.monotonic()
    try:
        selected = json.loads(args.files_from.read_text()) if args.files_from else None
        if args.files_from and (not isinstance(selected, list)
                                or any(not isinstance(rel, str) for rel in selected)):
            raise ValueError("--files-from must contain a JSON list of source paths")
        files = restored_files(root, selected, args.built_under)
    except (OSError, ValueError) as error:
        print(f"Cannot audit restored sources: {error}", file=sys.stderr)
        return 1
    if args.progress:
        print(f"Cache-restore audit: checking {len(files)} source(s) serially.", flush=True)
    failed = []
    for index, rel in enumerate(files, 1):
        if args.progress:
            print(f"Cache-restore audit [{index}/{len(files)}]: {rel} "
                  f"(elapsed {time.monotonic() - started:.1f}s)", flush=True)
        result = elaborate(root, rel)
        if result.returncode or result.stdout.strip():
            failed.append(rel)
            # `lake lean` first builds the file's imports and replays their logs, so a message can
            # also come from an import that this checkout built with warnings.
            print(f"FAIL  {rel} (restored or missing trace; messages from it or its "
                  f"imports)\n{result.stdout.rstrip()}", flush=True)
    elapsed = time.monotonic() - started
    if failed:
        print(f"Re-elaborating {len(failed)} file(s) with restored or missing traces "
              "printed messages that `lake build --wfail --iofail` did not replay; "
              f"see #4523. Audit elapsed {elapsed:.1f}s.",
              file=sys.stderr)
        return 1
    print(f"Files with restored or missing traces re-elaborated cleanly ({len(files)}) "
          f"in {elapsed:.1f}s.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
