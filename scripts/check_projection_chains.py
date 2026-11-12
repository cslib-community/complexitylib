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
  of an efficiency predicate (`Computable…In…`, `IsPPT…`, `PolyTimeComputable…`, `Refines`,
  bare or namespace-qualified, as in `Turing.MultiTapeTM.ComputableInPolyTime`): conclusions that
  automation looks up by head keep the projection form;
* section `variable`s, which are not declarations;
* named accessors, a `def` or `abbrev` whose body is one chain on a binder, such as
  `abbrev Ctx.desc (c : Ctx) := c.1.2`: these are the recommended remedy.

The reader is syntactic, so the count is a measure, not a proof that a statement reads well.

`scripts/projection_chains_baseline.json` records the count of each module that has chains, as
`{module path: count}`. In a module that the change adds, modifies or deletes (against the merge
base of `--base`, default `origin/main`, and the working tree, as
`scripts/check_changed_files.py` computes it), a count above its entry fails; a new module's
entry is 0. Only the changed modules are read, so the check takes seconds. A count below its entry
does not fail: it is reported with the command that lowers the entry, so that the in-flight
migrations do not each have to edit the baseline. Pull requests run this mode.

`--all` enforces every module. `--report` prints every difference from the baseline and always
succeeds; merge groups and pushes to `main` run it. `--update-baseline` lowers the entries of the
changed modules (with `--all`, of every module) to their counts; it refuses to add or raise an
entry unless `--allow-increase` is given, for instance when a module moves.
`--update-baseline --all --allow-increase` regenerates the whole baseline. `--list [PREFIX]`
ignores the baseline and prints every counted chain in the modules under the path PREFIX (such as
`CslibFrontier/DataStructure`), or in every module, with the most affected modules first; it
always succeeds. `scripts/count_ratchet.py` implements this baseline handling, which
`scripts/check_experiment_readability.py` shares.

The scanner is adapted from the survey script of the #1764 projections lane. The check reads only
the sources: it needs no build outputs.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_encoding_readability as cer  # noqa: E402
import count_ratchet as ratchet  # noqa: E402

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
    r"(?:Computable\w*In\w*|IsPPT\w*|PolyTimeComputable\w*|Refines)(?![\w'!?])")
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


RATCHET = ratchet.Ratchet(
    description=__doc__, baseline=BASELINE, update=UPDATE, unit="projection chain(s)",
    short="chain(s)",
    intro=("Public statements and the bodies of public definitions bind tuple components by name "
           f"instead of chaining positional projections such as `c.1.2` (#1764; {RULE}). These "
           "modules have more chains than their baseline entry; the counted chains are:"),
    removed="Projection chains were removed", scan=scan, render=lambda row: f"`{row.chain}`")


def main(argv: list[str] | None = None) -> int:
    return ratchet.main(RATCHET, argv)


if __name__ == "__main__":
    sys.exit(main())
