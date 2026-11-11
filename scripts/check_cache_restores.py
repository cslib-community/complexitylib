#!/usr/bin/env python3
"""Re-elaborate changed Lean files whose build outputs came from Lake's artifact cache (#4523).

Usage: python3 scripts/check_cache_restores.py [--base REF]

`lakefile.toml` enables Lake's local artifact cache, which checkouts on the same machine share.
Lake stores a module's outputs there whenever it builds them, also when the build logged warnings.
Only `--wfail` and `--iofail` turn those warnings into failures. A cache entry keeps the outputs
but not the messages. When another checkout later builds the same source, Lake restores the
outputs and writes a trace marked `"synthetic": true` with an empty log, so
`lake build --wfail --iofail` and `lake test --wfail --iofail` pass without showing the warnings.
CI does not hit this, because its remote cache is published only from `main`.

After the Lean gates, `scripts/full_check.py` and `scripts/quick_check.py` run this check. It runs
`lake -q lean` on each library or test file that the change adds or modifies (against the merge
base of REF, default `origin/main`, and the working tree, untracked files included, as
`scripts/check_changed_files.py` computes them) and whose trace is synthetic. It fails when that
command fails or prints anything at all: `lake lean` exits 0 after warnings, and `--iofail` rejects
informational output too. `lake lean` first builds the file's imports and replays their logs, so
a reported message can also come from an import. A changed file with no trace was not built,
which the gates report. Files are elaborated one at a time.

The check does not cover unchanged modules restored from a local entry that another checkout built
with warnings. Lake would have to keep each entry's messages and replay them on restore to close
that gap.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from check_changed_files import changed_files  # noqa: E402


def layout(root: Path) -> tuple[Path, list[Path]]:
    """The root package's Lean build directory, and the source directories of its libraries and
    executables relative to `root`, most specific first (`lakefile.toml`)."""
    config = tomllib.loads((root / "lakefile.toml").read_text())
    lib_dir = root / config.get("buildDir", ".lake/build") / config.get("leanLibDir", "lib/lean")
    package = Path(config.get("srcDir", "."))
    targets = config.get("lean_lib", []) + config.get("lean_exe", [])
    dirs = {package / target.get("srcDir", ".") for target in targets} | {package}
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


def restored_files(root: Path, base: str) -> list[str]:
    """The changed Lean files whose build trace says they were restored from a cache."""
    added, modified = changed_files(root, base)
    lib_dir, dirs = layout(root)
    return [rel for rel in sorted(added + modified) if rel.endswith(".lean")
            and (trace := trace_path(rel, lib_dir, dirs)) is not None and restored(trace)]


def elaborate(root: Path, rel: str) -> subprocess.CompletedProcess:
    """Elaborate `rel` with its library's options, without writing build outputs."""
    return subprocess.run(["lake", "-q", "lean", rel], cwd=root, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def main(argv: list[str] | None = None, root: Path = ROOT) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base", default="origin/main",
                        help="comparison ref; changes are taken from its merge base with HEAD")
    args = parser.parse_args(argv)
    files = restored_files(root, args.base)
    failed = []
    for rel in files:
        result = elaborate(root, rel)
        if result.returncode or result.stdout.strip():
            failed.append(rel)
            # `lake lean` first builds the file's imports and replays their logs, so a message can
            # also come from an import that this checkout built with warnings.
            print(f"FAIL  {rel} (restored from the artifact cache; messages from it or its "
                  f"imports)\n{result.stdout.rstrip()}", flush=True)
    if failed:
        print(f"Re-elaborating {len(failed)} changed file(s) restored from the artifact cache "
              "printed messages that `lake build --wfail --iofail` did not replay; see #4523.",
              file=sys.stderr)
        return 1
    print(f"Changed files restored from the artifact cache re-elaborated cleanly ({len(files)}).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
