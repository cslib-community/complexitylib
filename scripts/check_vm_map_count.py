#!/usr/bin/env python3
"""Check Linux `vm.max_map_count` for whole-library Lean imports, or measure an importer's VMAs.

Usage:
  python3 scripts/check_vm_map_count.py [--root DIR] [--max-map-count N] [--min-map-count N]
  python3 scripts/check_vm_map_count.py --measure MODULE [--measure MODULE ...] [--json]

Under Lean's `module` system, importing a compiled module maps up to five files into the `lean`
process (`.olean`, `.olean.server`, `.olean.private`, `.ir`, and `.ir.sig`). Whole-library gates
(`CslibFrontierTests/Smoke.lean`, `CslibFrontierTests/Axioms.lean`, `lake lint`, and
`lake exe checkInitImports`) therefore create over 70,000 virtual memory areas (VMAs) in a single
process. On Linux hosts with the stock `vm.max_map_count = 65530` limit, `mmap` fails with `ENOMEM`
and Lean's heap-copy fallback reports a misleading `failed to read file ... .olean` error (#5012).

Default mode runs a fast, build-free preflight on Linux. `--measure MODULE` launches a child `lean`
process via `lake env lean --run` and inspects `/proc/self/maps` inside that child process (not the
`lake` launcher) to report exact VMA counts by artifact kind.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import signal
import subprocess
import sys
import tempfile
from typing import TextIO

ROOT = Path(__file__).resolve().parent.parent
PROC_MAX_MAP_COUNT = Path("/proc/sys/vm/max_map_count")

# Measured baseline: at ~7,035 root modules (`CslibFrontier.lean`), `CslibFrontierResults` alone
# maps ~46,400 VMAs (~9,267 transitive modules * 5 files) and `CslibFrontier` maps >75,000 VMAs.
# Require headroom above both the current whole-library footprint and growth of `CslibFrontier`.
BASELINE_NON_ROOT_VMAS = 40_000
SAFETY_HEADROOM_VMAS = 20_000
DEFAULT_MIN_MAP_COUNT = 131_072
RECOMMENDED_SYSCTL = 262_144

IMPORT_LINE = re.compile(r"^\s*(?:public\s+)?import\s+[A-Za-z_][A-Za-z_0-9.]*\s*$")
MODULE_NAME = re.compile(r"^[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*$")
ARTIFACT_SUFFIXES = (".olean.server", ".olean.private", ".olean", ".ir.sig", ".ir")


def read_max_map_count(proc_path: Path = PROC_MAX_MAP_COUNT) -> int | None:
    """Return the host's `vm.max_map_count` on Linux, or `None` when `/proc` is absent."""
    if not proc_path.exists():
        return None
    return int(proc_path.read_text(encoding="utf-8").strip())


def count_root_aggregate_imports(root: Path) -> int:
    """Count `import` lines in `CslibFrontier.lean` without invoking Lean or requiring a build."""
    aggregate = root / "CslibFrontier.lean"
    if not aggregate.is_file():
        return 0
    return sum(1 for line in aggregate.read_text(encoding="utf-8").splitlines()
               if IMPORT_LINE.match(line))


def required_map_count(root: Path, explicit_min: int | None = None) -> tuple[int, int]:
    """Return `(required_limit, root_module_count)` for whole-library Lean gates."""
    root_modules = count_root_aggregate_imports(root)
    if explicit_min is not None:
        return explicit_min, root_modules
    # Each `module`-system root file contributes up to 5 mapped artifacts (`.olean`,
    # `.olean.server`, `.olean.private`, `.ir`, `.ir.sig`).
    estimated = 5 * root_modules + BASELINE_NON_ROOT_VMAS + SAFETY_HEADROOM_VMAS
    return max(DEFAULT_MIN_MAP_COUNT, estimated if root_modules else 0), root_modules


def classify_maps(maps_text: str) -> dict[str, int]:
    """Classify `/proc/self/maps` lines by Lean artifact suffix and shared-library/other regions."""
    counts: Counter[str] = Counter()
    lines = [line for line in maps_text.splitlines() if line.strip()]
    for line in lines:
        parts = line.split(None, 5)
        path = parts[5].strip() if len(parts) > 5 else ""
        matched = False
        for suffix in ARTIFACT_SUFFIXES:
            if path.endswith(suffix):
                counts[suffix] += 1
                matched = True
                break
        if not matched:
            if ".so" in path:
                counts[".so"] += 1
            else:
                counts["other"] += 1
    return {
        "total_vmas": len(lines),
        ".olean": counts[".olean"],
        ".olean.server": counts[".olean.server"],
        ".olean.private": counts[".olean.private"],
        ".ir": counts[".ir"],
        ".ir.sig": counts[".ir.sig"],
        ".so": counts[".so"],
        "other": counts["other"],
    }


def remediation_message(limit: int, needed: int, root_modules: int,
                        measured: int | None = None) -> str:
    detail = (
        f"measured {measured:,} VMAs in the child `lean` process"
        if measured is not None
        else f"requires vm.max_map_count >= {needed:,} ({root_modules:,} root modules in "
             "CslibFrontier.lean; each `module`-system import maps up to 5 `.olean*`/`.ir*` files)"
    )
    return (
        f"Linux vm.max_map_count is {limit:,}, but whole-library Lean validation {detail}.\n"
        "At this limit, whole-library importers (`Smoke`/`Axioms` in `lake test`, `lake lint`, "
        "`lake exe checkInitImports`) exhaust per-process memory mappings and fail with misleading "
        "`uncaught exception: failed to read file ... .olean` errors (#5012).\n"
        "Remediation:\n"
        f"  * Host operator (when authorized to change kernel settings): raise vm.max_map_count, "
        f"e.g. `sudo sysctl -w vm.max_map_count={RECOMMENDED_SYSCTL}` (or `/etc/sysctl.d/`).\n"
        "  * Shared host / unprivileged session: do NOT modify host kernel settings or claim a "
        "local full run passed; run `scripts/check.sh --quick --no-full-fallback` (plus targeted "
        "`lake build` checks) and use hosted CI for whole-library validation.\n"
        "See `manual/workflows/troubleshooting.md` for details.\n"
    )


def preflight(root: Path = ROOT, out: TextIO = sys.stdout,
              max_map_count: int | None = None, min_map_count: int | None = None,
              proc_path: Path = PROC_MAX_MAP_COUNT) -> int:
    """Fast local preflight for `scripts/check.sh` and `scripts/full_check.py`."""
    try:
        limit = max_map_count if max_map_count is not None else read_max_map_count(proc_path)
    except (OSError, ValueError) as error:
        out.write(f"FAIL  Linux vm.max_map_count preflight: cannot read {proc_path}: {error}\n")
        return 1
    if limit is None:
        return 0
    needed, root_modules = required_map_count(root, min_map_count)
    if limit < needed:
        out.write(remediation_message(limit, needed, root_modules))
        return 1
    return 0


def measure_importer(modules: list[str], root: Path = ROOT) -> subprocess.CompletedProcess[str]:
    """Run `lake env lean --run` on a temporary file importing `modules` and printing `/proc/self/maps`."""
    for module in modules:
        if not MODULE_NAME.match(module):
            raise ValueError(f"invalid Lean module name: {module!r}")
    imports = "\n".join(f"import {module}" for module in modules)
    probe = (
        f"{imports}\n"
        "def main : IO Unit := do\n"
        '  let maps ← IO.FS.readFile "/proc/self/maps"\n'
        "  IO.print maps\n"
    )
    with tempfile.TemporaryDirectory(prefix="cslib-frontier-vma-") as temp:
        probe_path = Path(temp) / "MeasureMaps.lean"
        probe_path.write_text(probe, encoding="utf-8")
        return subprocess.run(
            ["lake", "env", "lean", "--run", str(probe_path)],
            cwd=root,
            capture_output=True,
            text=True,
        )


def run_measure(modules: list[str], root: Path = ROOT, out: TextIO = sys.stdout,
                max_map_count: int | None = None, as_json: bool = False,
                proc_path: Path = PROC_MAX_MAP_COUNT) -> int:
    """Measure live `/proc/self/maps` inside a `lean` importer process and compare with the limit."""
    limit = max_map_count if max_map_count is not None else read_max_map_count(proc_path)
    if limit is None and not Path("/proc/self/maps").exists():
        out.write("Measurement requires Linux `/proc/self/maps`.\n")
        return 2
    result = measure_importer(modules, root=root)
    if result.returncode != 0:
        sig_note = ""
        if result.returncode < 0:
            sig = -result.returncode
            sig_name = signal.Signals(sig).name if sig in signal.Signals._value2member_map_ else str(sig)
            sig_note = f" (terminated by {sig_name}; cf. #4122 if SIGSEGV in setImportedIREntries)"
        out.write(
            f"FAIL  importer measurement for {', '.join(modules)} exited {result.returncode}"
            f"{sig_note}\n{result.stderr}"
        )
        if limit is not None and "failed to read file" in result.stderr and ".olean" in result.stderr:
            needed, root_modules = required_map_count(root)
            out.write(remediation_message(limit, needed, root_modules))
        return 1
    summary = classify_maps(result.stdout)
    summary["modules"] = modules
    summary["vm_max_map_count"] = limit
    if limit is not None:
        summary["headroom_vmas"] = limit - summary["total_vmas"]
    if as_json:
        out.write(json.dumps(summary, indent=2) + "\n")
    else:
        limit_text = f"{limit:,}" if limit is not None else "unavailable"
        out.write(
            f"Modules: {', '.join(modules)}\n"
            f"Child `lean` VMAs (`/proc/self/maps`): {summary['total_vmas']:,} "
            f"(host vm.max_map_count: {limit_text})\n"
            f"  .olean: {summary['.olean']:,}, .olean.server: {summary['.olean.server']:,}, "
            f".olean.private: {summary['.olean.private']:,}, "
            f".ir: {summary['.ir']:,}, .ir.sig: {summary['.ir.sig']:,}, "
            f".so: {summary['.so']:,}, other: {summary['other']:,}\n"
        )
    if limit is not None and summary["total_vmas"] + SAFETY_HEADROOM_VMAS > limit:
        needed, root_modules = required_map_count(root)
        out.write(remediation_message(limit, max(needed, summary["total_vmas"] + SAFETY_HEADROOM_VMAS),
                                      root_modules, measured=summary["total_vmas"]))
        return 1
    return 0


def main(argv: list[str] | None = None, out: TextIO = sys.stdout) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root")
    parser.add_argument("--max-map-count", type=int, default=None,
                        help="override host vm.max_map_count (for testing or threshold simulation)")
    parser.add_argument("--min-map-count", type=int, default=None,
                        help="override required minimum vm.max_map_count in preflight mode")
    parser.add_argument("--measure", action="append", default=[], metavar="MODULE",
                        help="measure `/proc/self/maps` inside a child `lean` process importing MODULE")
    parser.add_argument("--json", action="store_true",
                        help="emit JSON output in `--measure` mode")
    args = parser.parse_args(argv)
    if args.measure:
        return run_measure(args.measure, root=args.root, out=out,
                           max_map_count=args.max_map_count, as_json=args.json)
    status = preflight(root=args.root, out=out,
                       max_map_count=args.max_map_count, min_map_count=args.min_map_count)
    if status == 0:
        limit = args.max_map_count if args.max_map_count is not None else read_max_map_count()
        if limit is not None:
            needed, root_modules = required_map_count(args.root, args.min_map_count)
            out.write(
                f"ok    vm.max_map_count = {limit:,} "
                f"(required >= {needed:,} for {root_modules:,} root modules)\n"
            )
    return status


if __name__ == "__main__":
    sys.exit(main())
