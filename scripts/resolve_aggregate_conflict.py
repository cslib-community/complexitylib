#!/usr/bin/env python3
"""Git merge driver for the `mk_all` import aggregates: merge their import lines as sets.

`lake exe mk_all` writes each aggregate (`Complexity.lean`, `ComplexityResults.lean`) as a fixed
header followed by one import line per module, sorted by module name. Two branches
that add modules between the same neighbours conflict as text, and `merge=union` keeps imports
that one side deleted and can misorder the added ones. This driver merges the import lines three
ways as sets: it keeps every line that either side added and drops every line of the base that
either side deleted, then writes the header and the sorted lines. The header (the lines before
the first import) must be the same in all three versions and every later line an import (`import
M` or `public import M`). Otherwise the driver leaves `git merge-file`'s text merge, with conflict
markers where it finds them, and exits nonzero, so git reports a conflict.

`.gitattributes` names the driver `leanagg` for the aggregates; enable it once per clone with

    git config merge.leanagg.driver "python3 scripts/resolve_aggregate_conflict.py %O %A %B"

Where it is not configured (on GitHub, or in another clone), git uses its ordinary text merge.
The driver sees only the aggregate, not the merged tree: when a merge also moves modules,
regenerate the aggregates with `lake exe mk_all`. CI's `lake exe mk_all --check` rejects anything
else.
"""

from __future__ import annotations

import argparse
import os
import pathlib
import re
import subprocess
import sys
import tempfile

IMPORT = re.compile(r"(?:public )?import (\S+)")


class Refusal(Exception):
    """The set merge does not apply; a person resolves the conflict."""


def split(text: str, side: str) -> tuple[list[str], list[str]]:
    """The header lines before the first import, and the import lines, of one version."""
    if text and not text.endswith("\n"):
        raise Refusal(f"the {side} version does not end with a newline")
    lines = text.split("\n")[:-1]
    start = next((i for i, line in enumerate(lines) if IMPORT.fullmatch(line)), len(lines))
    for line in lines[start:]:
        if not IMPORT.fullmatch(line):
            raise Refusal(f"the {side} version has a line after its imports that is not an "
                          f"import: {line!r}")
    return lines[:start], lines[start:]


def merge_aggregate(base: str, ours: str, theirs: str) -> str:
    """Merge three versions of an aggregate, or raise `Refusal`."""
    (header, base_lines), (ours_header, ours_lines), (theirs_header, theirs_lines) = (
        split(text, side) for text, side in ((base, "base"), (ours, "ours"), (theirs, "theirs")))
    if not header == ours_header == theirs_header:
        raise Refusal("the headers before the imports differ")
    kept, ours_set, theirs_set = set(base_lines), set(ours_lines), set(theirs_lines)
    merged = (ours_set | theirs_set) - (kept - ours_set) - (kept - theirs_set)
    lines = sorted(merged, key=lambda line: (IMPORT.fullmatch(line).group(1), line))
    return "".join(f"{line}\n" for line in header + lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("base", help="the merge base's version (%%O)")
    parser.add_argument("ours", help="our version, which receives the result (%%A)")
    parser.add_argument("theirs", help="their version (%%B)")
    args = parser.parse_args(argv)
    try:
        texts = [pathlib.Path(p).read_bytes().decode("utf-8")
                 for p in (args.base, args.ours, args.theirs)]
        merged = merge_aggregate(*texts).encode("utf-8")
        ours = pathlib.Path(args.ours).resolve()
        fd, tmp = tempfile.mkstemp(dir=ours.parent, prefix=f".{ours.name}.")
        try:
            with os.fdopen(fd, "wb") as out:
                out.write(merged)
            os.replace(tmp, ours)
        except BaseException:
            pathlib.Path(tmp).unlink(missing_ok=True)
            raise
        return 0
    except Exception as err:  # noqa: BLE001 - every failure leaves a conflict
        print(f"resolve_aggregate_conflict: {err}; leaving a text merge as a conflict",
              file=sys.stderr)
    subprocess.run(["git", "merge-file", "-L", "ours", "-L", "base", "-L", "theirs",
                    args.ours, args.base, args.theirs])
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
