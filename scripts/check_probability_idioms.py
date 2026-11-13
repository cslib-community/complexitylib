#!/usr/bin/env python3
"""Keep raw probability plumbing from spreading outside `PMF` algebra (#4817).

Usage: python3 scripts/check_probability_idioms.py [--base REF | --all | --report | --list [PREFIX]]
           [--update-baseline [--allow-increase]] [--root DIR] [--baseline FILE]

This checks two conventions of "State a probability and sample uniformly" in
`manual/workflows/probabilistic-workflows.md`: a public statement writes the probability that a
program returns `true` as `Pr[e]`, or through a named `Experiment.succProbability` or
`Experiment.advantage`, and a program samples uniformly with `$ᵗ α`. In the modules under
`CslibFrontier/`, leaving out the `PMF` algebra modules under `CslibFrontier/Probability/`,
`CslibFrontier/Foundations/Probability/` and `CslibFrontier/Languages/Probabilistic/`, it counts

* `eval_statement`: in the signature of each public `theorem` and `lemma`, each
  `ProbComp.eval e true` (its argument `e` an identifier or a bracket group, so `.toReal`
  applications and `≤` bounds in `ℝ≥0∞` both count) and each `succProbability (ProbComp.eval …`.
  The `ℝ≥0∞` mass facts that the convention keeps for other `PMF` proofs do not count: theorems
  whose name's last component starts with `eval_` or `bind_apply_`;
* `uniform_call`: in the body of each `def`, `abbrev`, `instance` and `opaque`, public or not,
  each `ProbComp.uniform` (not `ProbComp.uniform_…` lemma names), which `$ᵗ` writes.

Tactic blocks, comments and strings are left out, as `scripts/check_projection_chains.py` does,
whose declaration reader this check shares, and so are declarations marked
`@[program_certificate]` or `@[fun_prop]`. The reader is syntactic: it sees the `ProbComp.`
qualified spellings, which are the ones the library uses outside the excluded modules, so the
counts measure the debt; review covers the rest of the convention.

`scripts/probability_idioms_baseline.json` records the counts of each module that has any, as
`{module path: {category: count}}`, and is ratcheted as `scripts/count_ratchet.py` describes. A
lane that retypes a module's experiments lowers its entries with `--update-baseline`.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_encoding_readability as cer  # noqa: E402
import check_projection_chains as cpc  # noqa: E402
import count_ratchet as ratchet  # noqa: E402

BASELINE = ROOT / "scripts/probability_idioms_baseline.json"
UPDATE = "python3 scripts/check_probability_idioms.py --update-baseline"
RULE = "manual/workflows/probabilistic-workflows.md, State a probability and sample uniformly"
CATEGORIES = ("eval_statement", "uniform_call")
EXCLUDED = ("CslibFrontier/Probability/", "CslibFrontier/Foundations/Probability/",
            "CslibFrontier/Languages/Probabilistic/")
STATEMENT_KEYWORDS = {"theorem", "lemma"}
MASS_FACT = re.compile(r"(?:eval|bind_apply)_")

_PROB_COMP = r"(?<![\w'!?.])(?:Cslib\.)?ProbComp\."
EVAL = re.compile(_PROB_COMP + r"eval(?![\w'!?])")
SUCC_EVAL = re.compile(r"(?<![\w'!?])(?:[\w']+\.)*succProbability\s*\(\s*(?:Cslib\.)?ProbComp\."
                       r"eval(?![\w'!?])")
UNIFORM = re.compile(_PROB_COMP + r"uniform(?![\w'!?])")
IDENTIFIER = re.compile(r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*")
TRUE = re.compile(r"\s*true(?![\w'!?])")
# Cheap prefilter: masking only removes matches.
ANY = re.compile(r"ProbComp\.(?:eval|uniform)(?![\w'!?])")


@dataclass(frozen=True)
class Finding:
    declaration: str
    line: int
    category: str
    text: str


def _argument_end(text: str, pos: int) -> int:
    """The offset after the application argument at `pos`: a bracket group or an identifier."""
    pos = cer._skip_space(text, pos)
    if pos < len(text) and text[pos] in "([{⟨":
        return cer._skip_brackets(text, pos)
    match = IDENTIFIER.match(text, pos)
    return match.end() if match else pos


def statement_evals(signature: str) -> list[tuple[int, str]]:
    """The counted `eval_statement` occurrences of a masked signature, as `(offset, text)`."""
    found = []
    for match in EVAL.finditer(signature):
        end = _argument_end(signature, match.end())
        if end > match.end() and TRUE.match(signature, end):
            found.append((match.start(), "ProbComp.eval … true"))
    found += [(match.start(), "succProbability (ProbComp.eval …")
              for match in SUCC_EVAL.finditer(signature)]
    return sorted(found)


def module_findings(text: str) -> list[Finding]:
    """The findings of a Lean source file, in order."""
    found = []
    for command in cer.commands(text):
        keyword = command.keyword
        statement = keyword in STATEMENT_KEYWORDS and command.public
        if not statement and keyword not in cpc.BODY_KEYWORDS:
            continue
        attributes = {item.split()[0] for group in cpc.ATTRIBUTES.finditer(
            command.text[:command.keyword_start]) for item in group[1].split(",") if item.split()}
        if attributes & cpc.CERTIFICATE_ATTRIBUTES:
            continue
        name, pos, split = command.parts()
        name = name or f"{keyword}@{command.line}"
        source = command.text

        def line(offset: int) -> int:
            return command.syntax.count("\n", 0, command.start + offset) + 1

        if statement:
            if MASS_FACT.match(name.split(".")[-1]):
                continue
            for offset, token in statement_evals(cpc.mask_tactics(source[pos:split])):
                found.append(Finding(name, line(pos + offset), "eval_statement", token))
        else:
            for match in UNIFORM.finditer(cpc.mask_tactics(source[split:])):
                found.append(Finding(name, line(split + match.start()), "uniform_call", match[0]))
    return sorted(found, key=lambda row: row.line)


def scan(root: Path, paths: list[str]) -> dict[str, list[Finding]]:
    """The findings of each of `paths` that exists, is checked and has any."""
    found = {}
    for rel in paths:
        path = root / rel
        if rel.startswith(EXCLUDED) or not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        if not ANY.search(text):
            continue
        try:
            rows = module_findings(text)
        except ValueError as error:
            raise ValueError(f"{rel}: {error}") from error
        if rows:
            found[rel] = rows
    return found


RATCHET = ratchet.Ratchet(
    description=__doc__, baseline=BASELINE, update=UPDATE, unit="probability idiom finding(s)",
    short="finding(s)",
    intro=("Public statements write a probability as `Pr[e]` or a named `Experiment` "
           "probability, and programs sample uniformly with `$ᵗ α` (#4817; "
           f"{RULE}). These modules have more findings than their baseline entry; the counted "
           "findings are:"),
    removed="Probability idiom findings were removed", scan=scan,
    render=lambda row: f"{row.category} `{row.text}`", categories=CATEGORIES,
    category=lambda row: row.category)


def main(argv: list[str] | None = None) -> int:
    return ratchet.main(RATCHET, argv)


if __name__ == "__main__":
    sys.exit(main())
