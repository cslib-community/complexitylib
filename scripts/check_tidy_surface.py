#!/usr/bin/env python3
"""Stop tidy computability from spreading into public statements (S3 of #456).

Usage: python3 scripts/check_tidy_surface.py [--update [--allow-increase]] [--no-build-check]

Tidy computability (`ComputableTidily…`, `ComputesTidily…`, `IsTidy…`) is a proof device: it may
appear anywhere inside proofs, never in a public statement. A public declaration of the
`Complexity` library has a *tidy statement* when a tidy constant occurs in its type (a theorem's
statement, a definition's type, a structure field) or in the exposed body of a definition.
Proofs, bodies that are not exposed and private declarations do not count, and neither do the raw
machine constructions listed in `scripts/tidy_allowlist.txt` (#608).

The check counts tidy statements per module and compares the counts with
`scripts/tidy_surface_baseline.json`, which records those that #456's sweep has yet to restate.
Every count must equal its baseline entry (a module without an entry, such as a new one, has
none). A count above its entry is a new tidy statement. A count below it fails too, until the
baseline is lowered in the same change: otherwise the unused allowance would let a removed
statement come back later. `--update` rewrites the baseline with the current counts; it refuses
to raise an entry unless `--allow-increase` is given, for instance when a module that has tidy
statements is moved.

Declarations written in source come from the `.ilean` files and statements from the `.olean`
files, read by `scripts/lean_outputs.py` and `scripts/LeanOutputs.lean`. The check needs the
build outputs of `lake build Complexity ComplexityTests ComplexityAbstracts` (`lake build` and
`lake test`), and refuses stale ones unless `--no-build-check` is given.
This is a post-build audit; the default freshness probe invokes Lake and may materialize
dependencies.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import lean_outputs as lo  # noqa: E402

ALLOWLIST = ROOT / "scripts/tidy_allowlist.txt"
BASELINE = ROOT / "scripts/tidy_surface_baseline.json"
UPDATE = "python3 scripts/check_tidy_surface.py --update"

# A tidy statement: the declaration, its line, and the tidy constants it mentions.
Statement = tuple[str, int, list[str]]


def load_allowlist(path: Path) -> set[str]:
    """Source paths relative to the repository root, one per line; `#` starts a comment."""
    return {line.split("#", 1)[0].strip() for line in path.read_text().splitlines()} - {""}


def tidy_statements(lib: lo.Library, allowlist: set[str]) -> dict[str, list[Statement]]:
    """The tidy statements of each module outside the allowlist, by source path. Declarations
    written in source count, structure fields included; constants generated from them (`simps`
    lemmas, equation lemmas, recursors) do not."""
    decls, _ = lo.collect_declarations(lib)
    found: dict[str, list[Statement]] = defaultdict(list)
    for name, decl in decls.items():
        if decl["role"] == "generated":
            continue
        const = lib.constants[name]
        mentions = sorted(set(const["tidy"]) | set(const.get("tb", ())))
        path = "Complexity/" + decl["path"]
        if mentions and path not in allowlist:
            found[path].append((name, decl["range"][0] if decl["range"] else 0, mentions))
    return {path: sorted(rows, key=lambda row: (row[1], row[0])) for path, rows in found.items()}


def load_baseline(path: Path) -> dict[str, int]:
    data = json.loads(path.read_text())
    if not isinstance(data, dict) or not all(
            isinstance(k, str) and type(v) is int and v > 0 for k, v in data.items()):
        sys.exit(f"{path}: expected a JSON object from source paths to positive counts")
    return data


def baseline_text(counts: dict[str, int]) -> str:
    return json.dumps({k: v for k, v in sorted(counts.items()) if v}, indent=1) + "\n"


def compare(counts: dict[str, int], baseline: dict[str, int]
            ) -> tuple[dict[str, tuple[int, int]], dict[str, tuple[int, int]]]:
    """`(over, under)`: the modules whose count exceeds or falls short of their baseline entry,
    as `path -> (count, entry)`. A module without an entry has entry 0."""
    over, under = {}, {}
    for path in sorted(set(counts) | set(baseline)):
        count, entry = counts.get(path, 0), baseline.get(path, 0)
        if count > entry:
            over[path] = (count, entry)
        elif count < entry:
            under[path] = (count, entry)
    return over, under


def over_report(over: dict[str, tuple[int, int]], found: dict[str, list[Statement]]) -> str:
    out = ["Public statements may not mention tidy computability, only proofs may (#456). Restate "
           "these with plain computability (`ComputableInPolyTime`, `ComputableInTimeAndSpace`, "
           "…) and switch inside the proofs (`.tidy`, `.of_tidy`).", ""]
    for path, (count, entry) in over.items():
        out.append(f"{path}: {count} tidy statement(s), baseline {entry}:")
        out += [f"  {path}:{line}: {name} mentions {', '.join(mentions)}"
                for name, line, mentions in found.get(path, [])]
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--update", action="store_true",
                        help="rewrite the baseline with the current counts")
    parser.add_argument("--allow-increase", action="store_true",
                        help="with --update, allow raising entries and adding modules")
    parser.add_argument("--no-build-check", action="store_true",
                        help="do not check that the build outputs are current")
    parser.add_argument("--allowlist", type=Path, default=ALLOWLIST)
    parser.add_argument("--baseline", type=Path, default=BASELINE)
    args = parser.parse_args(argv)
    if args.allow_increase and not args.update:
        parser.error("--allow-increase needs --update")
    lo.check_outputs(lo.DEFAULT_BUILD_DIR, args.no_build_check)
    found = tidy_statements(lo.Library(lo.DEFAULT_BUILD_DIR), load_allowlist(args.allowlist))
    counts = {path: len(rows) for path, rows in found.items()}
    baseline = load_baseline(args.baseline) if args.baseline.exists() else {}
    over, under = compare(counts, baseline)
    summary = f"{sum(counts.values())} public tidy statement(s) in {len(counts)} module(s)"
    if args.update:
        if over and not args.allow_increase:
            print(over_report(over, found), file=sys.stderr)
            print("\nThe baseline only goes down; pass --allow-increase to raise it on purpose, "
                  "for instance for a moved module.", file=sys.stderr)
            return 1
        args.baseline.write_text(baseline_text(counts))
        print(f"Wrote {args.baseline}: {summary}.")
        return 0
    if over:
        print(over_report(over, found), file=sys.stderr)
    if under:
        print(("\n" if over else "") + "Tidy statements were removed, so the baseline is stale. "
              f"Lower it with `{UPDATE}` and commit the result, so that they cannot come back:",
              file=sys.stderr)
        print("\n".join(f"  {path}: {count} (baseline {entry})"
                        for path, (count, entry) in under.items()), file=sys.stderr)
    if over or under:
        return 1
    print(f"{summary}, matching the baseline.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
