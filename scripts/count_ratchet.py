#!/usr/bin/env python3
"""The per-module count ratchet shared by `check_projection_chains.py`,
`check_experiment_readability.py` and `check_probability_idioms.py`.

A check supplies a `Ratchet`: how to find the counted rows of a module, and the words of its
messages. This module supplies the baseline file, the comparison and the command line.

The baseline maps each module path to its count, `{path: n}`, or, for a check with several
categories, to its counts per category, `{path: {category: n}}`. Zero counts are left out. In a
module that the change adds, modifies or deletes (against the merge base of `--base`, default
`origin/main`, and the working tree, as `scripts/check_changed_files.py` computes it), a count
above its entry fails; a new module's entry is 0. A count below its entry does not fail: it is
reported with the command that lowers the entry, so that in-flight migrations need not each edit
the baseline. Pull requests run this mode.

`--all` enforces every module. `--report` prints every difference from the baseline and always
succeeds; merge groups and pushes to `main` run it, so that queued changes written before an entry
was lowered are not ejected. `--update-baseline` lowers the entries of the changed modules (with
`--all`, of every module) to their counts; it refuses to add or raise an entry unless
`--allow-increase` is given, for instance when a module moves. `--update-baseline --all
--allow-increase` regenerates the whole baseline. `--list [PREFIX]` ignores the baseline and
prints every counted row in the modules under the path PREFIX, or in every module, with the most
affected modules first; it always succeeds.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from collections.abc import Callable, Sequence
from dataclasses import dataclass
import json
from pathlib import Path
import sys
from typing import Protocol

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_encoding_readability as cer  # noqa: E402


class Row(Protocol):
    """A counted occurrence: the declaration it is in and its line."""
    declaration: str
    line: int


Key = tuple[str, str]  # (module path, category); the category is "" for a single count


@dataclass(frozen=True)
class Ratchet:
    """What a count ratchet counts, and how it words its messages."""
    description: str  # the checking script's docstring, for `--help`
    baseline: Path  # the checked-in baseline, under `ROOT`
    update: str  # the command that lowers the baseline
    unit: str  # what is counted, in totals, such as "projection chain(s)"
    short: str  # what is counted, per module, such as "chain(s)"
    intro: str  # the opening of the failure report: the rule, its reference, then the list
    removed: str  # the opening of the note when counts fall: "Projection chains were removed"
    scan: Callable[[Path, list[str]], dict[str, list[Row]]]  # (root, paths) -> rows per module
    render: Callable[[Row], str]  # a row's text after its declaration, such as "`.1.2`"
    tree: str = "CslibFrontier"  # the checked modules are the Lean files under this directory
    categories: tuple[str, ...] = ()  # empty: one count per module
    category: Callable[[Row], str] = lambda row: ""
    # Further problems in the enforced modules that the baseline cannot record, such as stale
    # allowlist entries: (root, paths) -> messages, each failing the enforcing modes.
    extra: Callable[[Path, list[str]], list[str]] | None = None
    # Further modules that a change to a data file affects, such as those named by changed
    # allowlist entries: (root, comparison base) -> module paths.
    affected: Callable[[Path, str], set[str]] | None = None


def module_paths(ratchet: Ratchet, root: Path, prefix: str = "") -> list[str]:
    """The checked modules under the path `prefix`, as paths relative to `root`."""
    parts = Path(prefix).parts
    return [path.relative_to(root).as_posix()
            for path in sorted((root / ratchet.tree).rglob("*.lean"))
            if path.relative_to(root).parts[:len(parts)] == parts]


def touched(ratchet: Ratchet, root: Path, ref: str) -> list[str]:
    """The checked modules that the change adds, modifies or deletes, or otherwise affects."""
    paths = cer.touched_modules(root, ref)
    if ratchet.affected:
        paths |= ratchet.affected(root, cer.ccf.comparison_base(root, ref))
    tree = Path(ratchet.tree).parts
    return sorted(path for path in paths if Path(path).parts[:len(tree)] == tree)


def load_baseline(ratchet: Ratchet, path: Path) -> dict[Key, int]:
    data = json.loads(path.read_text(encoding="utf-8"))

    def positive(value: object) -> bool:
        return type(value) is int and value > 0

    if ratchet.categories:
        ok = isinstance(data, dict) and all(
            isinstance(k, str) and isinstance(v, dict) and v and all(
                c in ratchet.categories and positive(n) for c, n in v.items())
            for k, v in data.items())
        if not ok:
            sys.exit(f"{path}: expected a JSON object from source paths to objects from the "
                     f"categories {', '.join(ratchet.categories)} to positive counts")
        return {(k, c): n for k, v in data.items() for c, n in v.items()}
    if not isinstance(data, dict) or not all(
            isinstance(k, str) and positive(v) for k, v in data.items()):
        sys.exit(f"{path}: expected a JSON object from source paths to positive counts")
    return {(k, ""): v for k, v in data.items()}


def baseline_text(ratchet: Ratchet, counts: dict[Key, int]) -> str:
    """The baseline file for `counts`: sorted, zero counts left out, one module per line when
    there are categories (so that changes to different modules merge cleanly)."""
    if not ratchet.categories:
        return json.dumps({p: n for (p, _), n in sorted(counts.items()) if n}, indent=1) + "\n"
    nested: dict[str, dict[str, int]] = defaultdict(dict)
    for (path, category), n in counts.items():
        if n:
            nested[path][category] = n
    order = {c: i for i, c in enumerate(ratchet.categories)}
    lines = [json.dumps(path) + ": " + json.dumps(
        dict(sorted(nested[path].items(), key=lambda item: order[item[0]])))
        for path in sorted(nested)]
    return "{\n" + ",\n".join(" " + line for line in lines) + ("\n" if lines else "") + "}\n"


def count(ratchet: Ratchet, found: dict[str, list[Row]]) -> dict[Key, int]:
    counts: dict[Key, int] = defaultdict(int)
    for path, rows in found.items():
        for row in rows:
            counts[path, ratchet.category(row)] += 1
    return dict(counts)


def keys(ratchet: Ratchet, paths: Sequence[str]) -> list[Key]:
    return [(path, category) for path in sorted(paths)
            for category in (ratchet.categories or ("",))]


Change = tuple[Key, int, int]  # (key, count, baseline entry)


def compare(counts: dict[Key, int], baseline: dict[Key, int], checked: list[Key]
            ) -> tuple[list[Change], list[Change]]:
    """`(over, under)`: the keys of `checked` whose count exceeds or falls short of their entry.
    A missing count or entry is 0."""
    over, under = [], []
    for key in checked:
        n, entry = counts.get(key, 0), baseline.get(key, 0)
        if n > entry:
            over.append((key, n, entry))
        elif n < entry:
            under.append((key, n, entry))
    return over, under


def label(key: Key) -> str:
    path, category = key
    return f"{path} [{category}]" if category else path


def over_report(ratchet: Ratchet, over: list[Change], found: dict[str, list[Row]]) -> str:
    out = [ratchet.intro, ""]
    for key, n, entry in over:
        path, category = key
        out.append(f"{label(key)}: {n} {ratchet.short}, baseline {entry}:")
        out += [f"  {path}:{row.line}: {row.declaration}: {ratchet.render(row)}"
                for row in found.get(path, []) if ratchet.category(row) == category]
    return "\n".join(out)


def under_report(under: list[Change]) -> str:
    return "\n".join(f"  {label(key)}: {n} (baseline {entry})" for key, n, entry in under)


def listing(ratchet: Ratchet, found: dict[str, list[Row]]) -> str:
    total = sum(len(rows) for rows in found.values())
    head = f"{total} counted {ratchet.unit} in {len(found)} module(s)"
    if ratchet.categories:
        per = count(ratchet, found)
        head += " (" + ", ".join(
            f"{c}: {sum(n for (_, k), n in per.items() if k == c)}"
            for c in ratchet.categories) + ")"
    out = [head + "."]
    for path, rows in sorted(found.items(), key=lambda item: (-len(item[1]), item[0])):
        out += ["", f"{path}: {len(rows)}"]
        by_declaration: dict[str, list[Row]] = defaultdict(list)
        for row in rows:
            by_declaration[row.declaration].append(row)
        for name, declaration_rows in by_declaration.items():
            out.append(f"  {path}:{declaration_rows[0].line}: {name}: "
                       + " ".join(ratchet.render(row) for row in declaration_rows))
    return "\n".join(out)


def main(ratchet: Ratchet, argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=ratchet.description,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument("--base", default="origin/main",
                       help="enforce in the modules changed since the merge base with this "
                            "revision (default origin/main)")
    scope.add_argument("--all", action="store_true", help="enforce in every module")
    scope.add_argument("--report", action="store_true",
                       help="report every difference from the baseline and succeed")
    scope.add_argument("--list", nargs="?", const="", metavar="PREFIX",
                       help=f"ignore the baseline and list every counted {ratchet.unit} in the "
                            "modules under the path PREFIX, or in every module; always succeeds")
    parser.add_argument("--update-baseline", action="store_true",
                        help="lower the baseline entries of the enforced modules")
    parser.add_argument("--allow-increase", action="store_true",
                        help="with --update-baseline, allow adding and raising entries")
    parser.add_argument("--root", type=Path, default=ROOT, help="the repository to check")
    parser.add_argument("--baseline", type=Path, help="default: the root's baseline file")
    args = parser.parse_args(argv)
    if args.allow_increase and not args.update_baseline:
        parser.error("--allow-increase needs --update-baseline")
    if (args.report or args.list is not None) and args.update_baseline:
        parser.error("--report and --list do not combine with --update-baseline")
    if args.list is not None:
        paths = module_paths(ratchet, args.root, args.list)
        print(listing(ratchet, ratchet.scan(args.root, paths)))
        return 0
    baseline_path = args.baseline or args.root / ratchet.baseline.relative_to(ROOT)
    baseline = load_baseline(ratchet, baseline_path) if baseline_path.exists() else {}
    whole = args.all or args.report
    paths = (sorted(set(module_paths(ratchet, args.root)) | {path for path, _ in baseline})
             if whole else touched(ratchet, args.root, args.base))
    found = ratchet.scan(args.root, paths)
    counts = count(ratchet, found)
    over, under = compare(counts, baseline, keys(ratchet, paths))
    extra = ratchet.extra(args.root, paths) if ratchet.extra else []
    scope_text = "every module" if whole else f"{len(paths)} changed module(s)"
    status = (f"{sum(counts.values())} counted {ratchet.unit} in {len(found)} module(s), "
              f"checking {scope_text}")
    if args.report:
        sections = []
        if over:
            sections.append(over_report(ratchet, over, found))
        if under:
            sections.append("Entries above the current count:\n" + under_report(under))
        sections += extra
        print("\n\n".join([*sections, f"{status}; report only, nothing is enforced."]))
        return 0
    if args.update_baseline:
        if over and not args.allow_increase:
            print(over_report(ratchet, over, found), file=sys.stderr)
            print("\nThe baseline only goes down; pass --allow-increase to raise it on purpose, "
                  "for instance for a moved module.", file=sys.stderr)
            return 1
        updated = dict(baseline)
        for key in keys(ratchet, paths):
            updated[key] = counts.get(key, 0)
        baseline_path.write_text(baseline_text(ratchet, updated), encoding="utf-8")
        print(f"Wrote {baseline_path} for {scope_text}: {status}.")
        if extra:
            print("\n\n".join(extra), file=sys.stderr)
            return 1
        return 0
    if under:
        print(f"{ratchet.removed}, so these entries can come down. Lower them with "
              f"`{ratchet.update}` and commit the result, so that they cannot come back:\n"
              + under_report(under))
    if over or extra:
        sections = ([over_report(ratchet, over, found)] if over else []) + extra
        print(("\n" if under else "") + "\n\n".join(sections), file=sys.stderr)
        return 1
    print(f"{status}; none exceeds its baseline entry.")
    return 0
