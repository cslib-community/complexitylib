#!/usr/bin/env python3
"""Stop positional projection chains from spreading in public statements (#1764).

Usage: python3 scripts/check_projection_chains.py [--base REF | --all | --report | --list [PREFIX]]
           [--update-baseline [--allow-increase]] [--root DIR] [--baseline FILE]

This checks the rule "Named components instead of positional projections" in CONTRIBUTING.md. A
*chain* is a run of two or more tuple projections written after a term: `c.1.2`, `s.2.1.1`,
`p.2.fst`, `(f x).1.2`, `(·.1.2)`. A single projection `p.1` is not a chain, and neither is a
numeric literal such as `1.5.2`. A module's *count* is the number of chains in

* the signature of each public declaration (theorem, lemma, def, abbrev, instance, opaque, axiom;
  for a structure, class or inductive, the whole declaration with its fields and constructors), and
* the body of each public `def`, `abbrev`, `instance` and `opaque`,

leaving out tactic blocks (`by …` to the end of its bracket group, and `termination_by` and
`decreasing_by` clauses), comments and strings: projections inside proofs are fine, and theorem
bodies are proofs. Public means what it means for `scripts/check_encoding_readability.py`, whose
declaration reader this check shares; unlike that check, `Internal` namespaces and modules count.
The standing exceptions of CONTRIBUTING do not count:

* declarations marked `@[program_certificate]` or `@[fun_prop]`, and chains inside an application
  of an efficiency predicate (`Computable…In…`, `IsPPT…`, `IsOraclePPT…`, `PolyTimeComputable…`,
  `Refines`, bare or namespace-qualified, as in `Turing.MultiTapeTM.ComputableInPolyTime`):
  conclusions that automation looks up by head keep the projection form;
* section `variable`s, which are not declarations;
* named accessors, a `def` or `abbrev` whose body is one chain on a binder, such as
  `abbrev Ctx.desc (c : Ctx) := c.1.2`: these are the recommended remedy.

The reader is syntactic, so the count is a measure, not a proof that a statement reads well.

`scripts/projection_chains_baseline.json` records the count of each module that has chains, as
`{module path: count}`. In a module that the change adds, modifies or deletes (against the merge
base of `--base`, default `origin/main`, and the working tree, as
`scripts/check_changed_files.py` computes it), a count above the module's *limit* fails. The limit
is the module's entry (0 for a new module), capped at the module's count at the merge base unless
the change raises the entry itself. A change therefore cannot add chains back under an entry that
is higher than the count it started from (to add them back on purpose, raise the entry by hand
above its value at the merge base), and removing chains needs no baseline edit: a count below its
entry is only reported. Edits to the baseline are kept to raises, moves and missing entries,
because concurrent edits to neighbouring lines of the file conflict in the merge queue; entries
above their counts are pruned from time to time with `--update-baseline --all`. Only the changed
modules are read, so the check takes seconds. Pull requests run this mode.

`--all` enforces every module. `--report` prints every difference from the baseline and always
succeeds; merge groups and pushes to `main` run it. `--update-baseline` sets the entries of the
changed modules (with `--all`, of every module) to their counts; it refuses a count above its
limit unless `--allow-increase` is given, for instance when a module moves, and always refuses
one that the recorded entry would still leave above its limit.
`--update-baseline --all --allow-increase` regenerates the whole baseline. `--list [PREFIX]`
ignores the baseline and prints every counted chain in the modules under the path PREFIX (such as
`CslibFrontier/DataStructure`), or in every module, with the most affected modules first; it
always succeeds.

The scanner is adapted from the survey script of the #1764 projections lane. The check reads only
the sources: it needs no build outputs.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_changed_files as ccf  # noqa: E402
import check_encoding_readability as cer  # noqa: E402

BASELINE = ROOT / "scripts/projection_chains_baseline.json"
UPDATE = "python3 scripts/check_projection_chains.py --update-baseline"
RULE = "CONTRIBUTING.md, Named components instead of positional projections"

COMPONENT = r"(?:\d+|fst|snd)"
# Two or more `.1`/`.2`/`.fst`/`.snd` after an identifier character, a closing bracket or `·`.
CHAIN = re.compile(r"(?:(?<=[\w'!?)\]}⟩⦄])|(?<=·))((?:\." + COMPONENT + r"(?![\w'!?])){2,})")
# A chain whose head is only digits is a numeric literal such as `1.5.2`, not a projection.
NUMERIC_HEAD = re.compile(r"(?<![\w'!?.])\d+$")
ATTRIBUTES = re.compile(r"@\[([^\]]*)\]")
CERTIFICATE_ATTRIBUTES = {"program_certificate", "fun_prop"}
BODY_KEYWORDS = {"def", "abbrev", "instance", "opaque"}
TACTIC = re.compile(r"(?<![\w'.!?])(by|decreasing_by|termination_by)(?![\w'!?])")
# An efficiency predicate head, bare or qualified (`Turing.MultiTapeTM.ComputableInPolyTime`,
# `_root_.IsPPT`): automation looks it up by its last component, however it is spelled.
EFFICIENCY = re.compile(
    r"(?<![\w'.])(?:[\w']+\.)*"
    r"(?:Computable\w*In\w*|IsPPT\w*|IsOraclePPT\w*|PolyTimeComputable\w*|Refines)(?![\w'!?])")
# The body of a named accessor: `:= c.1.2` or `:= fun c => c.1.2`, optionally parenthesized.
ACCESSOR = re.compile(r"\s*:=\s*(?:fun\s+\w+\s*=>\s*)?\(?\s*[\w'.]+?(?:\." + COMPONENT
                      + r"){2,}\s*\)?\s*")
OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"


@dataclass(frozen=True)
class Chain:
    declaration: str
    line: int
    chain: str  # such as `.1.2`


def _group_end(text: str, pos: int) -> int:
    """The offset where the bracket group enclosing `pos` closes, or the length of `text`."""
    depth = 0
    for i in range(pos, len(text)):
        if text[i] in OPEN:
            depth += 1
        elif text[i] in CLOSE:
            if depth == 0:
                return i
            depth -= 1
    return len(text)


def mask_tactics(text: str) -> str:
    """Blank each `by` block to the end of its enclosing bracket group (or of `text`), and each
    `decreasing_by` or `termination_by` clause to the end of `text`, keeping offsets."""
    out, pos = list(text), 0
    while match := TACTIC.search(text, pos):
        end = _group_end(text, match.end()) if match[1] == "by" else len(text)
        for i in range(match.start(), end):
            if out[i] != "\n":
                out[i] = " "
        pos = max(end, match.end())
    return "".join(out)


def chains(text: str) -> list[tuple[int, str]]:
    """The chains of masked source, as `(offset, chain)`, outside efficiency predicates."""
    exempt = [(m.start(), _group_end(text, m.end())) for m in EFFICIENCY.finditer(text)]
    return [(m.start(), m[1]) for m in CHAIN.finditer(text)
            if not NUMERIC_HEAD.search(text[max(0, m.start() - 40):m.start()])
            and not any(start <= m.start() < end for start, end in exempt)]


def module_chains(text: str) -> list[Chain]:
    """The counted chains of a Lean source file, in order."""
    found = []
    for command in cer.commands(text):
        keyword = command.keyword
        if keyword not in cer.DECLARATIONS or not command.public:
            continue
        attributes = {item.split()[0] for group in ATTRIBUTES.finditer(
            command.text[:command.keyword_start]) for item in group[1].split(",") if item.split()}
        if attributes & CERTIFICATE_ATTRIBUTES:
            continue
        name, pos, split = command.parts()
        source = command.text
        if keyword in cer.TYPE_DECLARATIONS:
            parts = [(pos, len(source))]  # fields and constructors are the statement
        elif keyword in BODY_KEYWORDS:
            if keyword in ("def", "abbrev") and ACCESSOR.fullmatch(mask_tactics(source[split:])):
                continue
            parts = [(pos, split), (split, len(source))]
        else:
            parts = [(pos, split)]
        name = name or f"{keyword}@{command.line}"
        for start, end in parts:
            for offset, chain in chains(mask_tactics(source[start:end])):
                line = command.syntax.count("\n", 0, command.start + start + offset) + 1
                found.append(Chain(name, line, chain))
    return found


def module_paths(root: Path, prefix: str = "") -> list[str]:
    """The checked modules under `prefix`, as paths relative to `root`."""
    parts = Path(prefix).parts
    return [path.relative_to(root).as_posix()
            for path in sorted((root / "CslibFrontier").rglob("*.lean"))
            if path.relative_to(root).parts[:len(parts)] == parts]


def scan(root: Path, paths: list[str]) -> dict[str, list[Chain]]:
    """The counted chains of each of `paths` that exists and has any."""
    found = {}
    for rel in paths:
        path = root / rel
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        if not CHAIN.search(text):  # masking only removes matches
            continue
        try:
            rows = module_chains(text)
        except ValueError as error:
            raise ValueError(f"{rel}: {error}") from error
        if rows:
            found[rel] = rows
    return found


def load_baseline(path: Path) -> dict[str, int]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or not all(
            isinstance(k, str) and type(v) is int and v > 0 for k, v in data.items()):
        sys.exit(f"{path}: expected a JSON object from source paths to positive counts")
    return data


def baseline_text(counts: dict[str, int]) -> str:
    return json.dumps({k: v for k, v in sorted(counts.items()) if v}, indent=1) + "\n"


Change = tuple[str, int, int]  # (path, count, baseline entry or limit)


def compare(counts: dict[str, int], baseline: dict[str, int], paths: list[str],
            limits: dict[str, int] | None = None) -> tuple[list[Change], list[Change]]:
    """`(over, under)`: those of `paths` whose count exceeds their limit (by default their entry),
    with the limit, or falls short of their entry, with the entry. A missing count or entry is
    0."""
    limits = baseline if limits is None else limits
    over, under = [], []
    for path in sorted(paths):
        count, entry, cap = counts.get(path, 0), baseline.get(path, 0), limits.get(path, 0)
        if count > cap:
            over.append((path, count, cap))
        elif count < entry:
            under.append((path, count, entry))
    return over, under


def read_at(root: Path, revision: str, rel: str) -> str | None:
    """The text of `rel` at `revision`, or None when it is not there."""
    shown = subprocess.run(["git", "show", f"{revision}:{rel}"], cwd=root, capture_output=True)
    return shown.stdout.decode("utf-8") if shown.returncode == 0 else None


MergeBase = tuple[int, int | None]  # (entry at the merge base, count there or None if absent)


def merge_base_state(root: Path, base: str, baseline_rel: str | None, paths: list[str],
                     baseline: dict[str, int]) -> dict[str, MergeBase]:
    """The entry and the count of each of `paths` at `base`. Without a baseline at `base`, the
    current entries stand in, which keeps every entry capped."""
    old_text = read_at(root, base, baseline_rel) if baseline_rel else None
    old = json.loads(old_text) if old_text else baseline
    state = {}
    for path in paths:
        text = read_at(root, base, path)
        try:
            count = None if text is None else len(module_chains(text)) if CHAIN.search(text) else 0
        except ValueError as error:
            raise ValueError(f"{path} at {base}: {error}") from error
        state[path] = (old.get(path, 0), count)
    return state


def limit(entry: int, old_entry: int, base_count: int | None) -> int:
    """A module's limit given its entry: the entry, capped at the count at the merge base unless
    the module is new there or the entry is above its value there."""
    return entry if base_count is None or entry > old_entry else min(entry, base_count)


def unrecordable(over: list[Change], state: dict[str, MergeBase] | None) -> list[Change]:
    """Those of `over` that recording their count as the entry would leave over the limit."""
    return [change for change in over
            if state is not None and limit(change[1], *state[change[0]]) < change[1]]


def over_report(over: list[Change], found: dict[str, list[Chain]],
                baseline: dict[str, int] | None = None,
                state: dict[str, MergeBase] | None = None) -> str:
    out = ["Public statements and the bodies of public definitions bind tuple components by name "
           f"instead of chaining positional projections such as `c.1.2` (#1764; {RULE}). These "
           "modules have more chains than their limit; the counted chains are:", ""]
    for path, count, cap in over:
        entry = cap if baseline is None else baseline.get(path, 0)
        bound = (f"baseline {entry}" if cap == entry
                 else f"limit {cap} (the count at the merge base; baseline {entry})")
        out.append(f"{path}: {count} chain(s), {bound}:")
        out += [f"  {path}:{row.line}: {row.declaration}: `{row.chain}`"
                for row in found.get(path, [])]
    stuck = unrecordable(over, state)
    if stuck:
        out += ["", "Recording these counts with `--update-baseline` would not raise the entry above "
                "its value at the merge base, so the limit would stay the count there. Remove the "
                "chains or, to add them back on purpose, raise the entry by hand above its value at "
                "the merge base, so that the raise is visible in review:"]
        out += [f"  {path}: above {state[path][0]}" for path, _, _ in stuck]
    return "\n".join(out)


def under_report(under: list[Change]) -> str:
    return "\n".join(f"  {path}: {count} (baseline {entry})" for path, count, entry in under)


def listing(found: dict[str, list[Chain]]) -> str:
    total = sum(len(rows) for rows in found.values())
    out = [f"{total} counted projection chain(s) in {len(found)} module(s)."]
    for path, rows in sorted(found.items(), key=lambda item: (-len(item[1]), item[0])):
        out += ["", f"{path}: {len(rows)}"]
        by_declaration: dict[str, list[Chain]] = defaultdict(list)
        for row in rows:
            by_declaration[row.declaration].append(row)
        for name, chain_rows in by_declaration.items():
            out.append(f"  {path}:{chain_rows[0].line}: {name}: "
                       + " ".join(f"`{row.chain}`" for row in chain_rows))
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument("--base", default="origin/main",
                       help="enforce in the modules changed since the merge base with this "
                            "revision (default origin/main)")
    scope.add_argument("--all", action="store_true", help="enforce in every module")
    scope.add_argument("--report", action="store_true",
                       help="report every difference from the baseline and succeed")
    scope.add_argument("--list", nargs="?", const="", metavar="PREFIX",
                       help="ignore the baseline and list every counted chain in the modules "
                            "under the path PREFIX, or in every module; always succeeds")
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
        print(listing(scan(args.root, module_paths(args.root, args.list))))
        return 0
    baseline_path = args.baseline or args.root / BASELINE.relative_to(ROOT)
    baseline = load_baseline(baseline_path) if baseline_path.exists() else {}
    whole = args.all or args.report
    paths = (sorted(set(module_paths(args.root)) | set(baseline)) if whole
             else sorted(cer.touched_modules(args.root, args.base)))
    found = scan(args.root, paths)
    counts = {path: len(rows) for path, rows in found.items()}
    state = limits = None
    if not whole:
        try:
            baseline_rel = baseline_path.resolve().relative_to(args.root.resolve()).as_posix()
        except ValueError:
            baseline_rel = None
        state = merge_base_state(args.root, ccf.comparison_base(args.root, args.base),
                                 baseline_rel, paths, baseline)
        limits = {path: limit(baseline.get(path, 0), *state[path]) for path in paths}
    over, under = compare(counts, baseline, paths, limits)
    scope_text = "every module" if whole else f"{len(paths)} changed module(s)"
    status = (f"{sum(counts.values())} counted projection chain(s) in {len(counts)} module(s), "
              f"checking {scope_text}")
    if args.report:
        if over:
            print(over_report(over, found))
        if under:
            print(("\n" if over else "") + "Entries above the current count:\n"
                  + under_report(under))
        print(("\n" if over or under else "") + f"{status}; report only, nothing is enforced.")
        return 0
    if args.update_baseline:
        stuck = unrecordable(over, state)
        if stuck:
            print(over_report(stuck, found, baseline, state), file=sys.stderr)
            return 1
        if over and not args.allow_increase:
            print(over_report(over, found, baseline), file=sys.stderr)
            print("\nThe baseline only goes down; pass --allow-increase to raise it on purpose, "
                  "for instance for a moved module.", file=sys.stderr)
            return 1
        updated = dict(baseline)
        for path in paths:
            updated[path] = counts.get(path, 0)
        baseline_path.write_text(baseline_text(updated), encoding="utf-8")
        print(f"Wrote {baseline_path} for {scope_text}: {status}.")
        return 0
    if under:
        print("Projection chains were removed. No baseline edit is needed: the check caps each "
              "changed module at its count at the merge base, and stale entries are pruned "
              f"periodically with `{UPDATE} --all`:\n" + under_report(under))
    if over:
        print(("\n" if under else "") + over_report(over, found, baseline, state),
              file=sys.stderr)
        return 1
    print(f"{status}; none exceeds its limit.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
