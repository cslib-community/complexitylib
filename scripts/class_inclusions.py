#!/usr/bin/env python3
"""Generate the complexity-class inclusion tables in the operator manual (stdlib only).

    python3 scripts/class_inclusions.py           # rewrite the manual page
    python3 scripts/class_inclusions.py --check   # exit 1 if the page is out of date

Two layers are combined for every ordered pair of classes `A`, `B` in a grid:

* **The library.** Theorems named `A_subset_B`, `A_ssubset_B`, `A_eq_B` or `A_not_subset_B`
  between classes of a grid are found in the Lean sources automatically. `EXTRA` adds
  instances of theorems that take a parameter, such as `NC_subset_AC 1`. Inclusions that
  follow by chaining proved ones are marked separately from those stated directly, and
  non-inclusions follow from a proved non-inclusion `Z ⊄ Y` whenever `Z ⊆ A` and `B ⊆ Y`.
* **The literature.** `LITERATURE` records the inclusions and non-inclusions that are known
  unconditionally, closed under the same two rules. A pair that the literature neither proves nor
  refutes is an open question.

The script refuses to write a table in which the library proves something the literature layer
calls open or false, so a mistake in either layer is reported rather than published.
"""
from __future__ import annotations

import argparse
import itertools
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ROOT / "CslibFrontier"
PAGE = ROOT / "manual/machines-and-classes/class-inclusions.md"

# Grid label -> the token naming the class in theorem names.
UNIFORM = {
    "L": "L", "NL": "NL", "P": "P", "ZPP": "ZPP", "RP": "RP", "coRP": "coRP", "BPP": "BPP",
    "NP": "NP", "coNP": "coNP", "MA": "MA", "AM": "AM", "PH": "PH", "BQP": "BQP", "QMA": "QMA",
    "PP": "PP", "P^#P": "PWithSharpPOracle", "PSPACE": "PSPACE", "IP": "IP", "EXP": "EXP",
    "NEXP": "NEXP",
}
CIRCUIT = {
    "AC⁰": "AC0", "ACC⁰": "ACC0", "TC⁰": "TC0", "NC¹": "NC_one", "AC¹": "AC_one",
    "NC²": "NC_two", "P/poly": "PPoly",
}
# Classes that equal their complement, with the reason, and the complement pairs among the rest.
CO_CLOSED = {
    "L": "deterministic; swap accepting and rejecting states",
    "NL": "Immerman 1988 (`Immerman1988`); Szelepcsényi 1987 (`Szelepcsenyi1987`)",
    "P": "deterministic; swap accepting and rejecting states",
    "ZPP": "swap the two definite answers",
    "BPP": "the error bound is symmetric",
    "PH": "each level Σₖᵖ has complement Πₖᵖ ⊆ Σₖ₊₁ᵖ",
    "BQP": "the error bound is symmetric",
    "PP": "Gill 1977, after making the acceptance probability never exactly one half",
    "P^#P": "deterministic machine with an oracle; swap its answers",
    "PSPACE": "deterministic; swap accepting and rejecting states",
    "IP": "IP = PSPACE (Shamir 1992), which is closed under complement",
    "EXP": "deterministic; swap accepting and rejecting states",
}
COMPLEMENT = {"NP": "coNP", "coNP": "NP", "RP": "coRP", "coRP": "RP"}

# Instances of parametric theorems: (A, relation, B, declaration as applied).
EXTRA = [
    ("NC¹", "subset", "AC¹", "NC_subset_AC 1"),
    ("NC¹", "subset", "NC²", "NC_mono (i := 1) (j := 2)"),
    ("AC¹", "subset", "NC²", "AC_subset_NC_succ 1"),
    ("NC¹", "subset", "P/poly", "NC_subset_PPoly 1"),
    ("NC²", "subset", "P/poly", "NC_subset_PPoly 2"),
    ("AC¹", "subset", "P/poly", "AC_subset_PPoly 1"),
]

# Unconditional results of the literature: (A, relation, B, source). `subset` means A ⊆ B and
# `not_subset` means A ⊄ B. Closure under chaining and complements supplies the rest.
LITERATURE = [
    ("L", "subset", "NL", "by definition"),
    ("NL", "subset", "P", "reachability in polynomial time, Arora–Barak Chapter 4"),
    ("P", "subset", "ZPP", "by definition"),
    ("ZPP", "subset", "RP", "Gill 1977 (`Gill1977`)"),
    ("RP", "subset", "NP", "Gill 1977"),
    ("RP", "subset", "BPP", "Gill 1977"),
    ("NP", "subset", "MA", "by definition"),
    ("BPP", "subset", "MA", "by definition"),
    ("MA", "subset", "AM", "Babai 1985 (`Babai1985`)"),
    ("AM", "subset", "PH", "AM ⊆ Π₂ᵖ, Babai 1985"),
    ("NP", "subset", "PH", "by definition"),
    ("BPP", "subset", "BQP", "Bernstein–Vazirani 1997 (`BernsteinVazirani1997`)"),
    ("MA", "subset", "QMA", "by definition"),
    ("BQP", "subset", "QMA", "by definition"),
    ("QMA", "subset", "PP", "Kitaev–Watrous 2000 (`KitaevWatrous2000`)"),
    ("NP", "subset", "PP", "Gill 1977"),
    ("PP", "subset", "P^#P", "by definition"),
    ("PH", "subset", "P^#P", "Toda 1991 (`Toda1991`)"),
    ("P^#P", "subset", "PSPACE", "counting by enumeration, Arora–Barak Chapter 17"),
    ("PSPACE", "subset", "IP", "Shamir 1992 (`Shamir1992`)"),
    ("IP", "subset", "PSPACE", "evaluating the game tree in polynomial space, Arora–Barak Chapter 8"),
    ("PSPACE", "subset", "EXP", "counting configurations, Arora–Barak Chapter 4"),
    ("EXP", "subset", "NEXP", "by definition"),
    ("PSPACE", "not_subset", "NL",
     "NL ⊆ SPACE(log² n) (Savitch 1970, `Savitch1970`) ⊊ PSPACE by the space hierarchy theorem "
     "(Stearns–Hartmanis–Lewis 1965, `StearnsHartmanisLewis1965`)"),
    ("EXP", "not_subset", "P", "time hierarchy theorem, Arora–Barak Chapter 3"),
    ("NEXP", "not_subset", "NP",
     "nondeterministic time hierarchy theorem (Žák 1983, `Zak1983`)"),
    ("NEXP", "not_subset", "coNP",
     "NEXP ⊆ coNP would give NP ⊆ coNP, so NP = coNP ⊇ NEXP, contradicting NP ⊊ NEXP"),
    ("AC⁰", "subset", "ACC⁰", "by definition"),
    ("ACC⁰", "subset", "TC⁰", "a MOD gate is a sum of threshold gates"),
    ("TC⁰", "subset", "NC¹", "iterated addition in logarithmic depth"),
    ("NC¹", "subset", "AC¹", "by definition"),
    ("AC¹", "subset", "NC²", "balanced fan-in-two trees"),
    ("NC²", "subset", "P/poly", "by definition"),
    ("ACC⁰", "not_subset", "AC⁰",
     "parity is not in AC⁰ (Furst–Saxe–Sipser 1984, `FurstSaxeSipser1984`; Ajtai 1983, "
     "`Ajtai1983`)"),
]

GRIDS = [
    ("Uniform classes", UNIFORM),
    ("Nonuniform circuit classes", CIRCUIT),
]

THEOREM = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:public\s+|private\s+|protected\s+)*(?:theorem|lemma)\s+"
                     r"(?:Cslib\.)?(?:Complexity\.)?([^\s(:{\[]+)", re.M)
RELATIONS = ("not_subset", "ssubset", "subset", "eq")


def locate() -> dict[str, Path]:
    """The first source file declaring each theorem name."""
    found: dict[str, Path] = {}
    for path in sorted(SOURCES.rglob("*.lean")):
        for match in THEOREM.finditer(path.read_text(encoding="utf-8")):
            found.setdefault(match[1], path)
    return found


def library_facts(grid: dict[str, str], theorems: dict[str, Path]):
    """(A, relation, B, declaration) for every library theorem between classes of `grid`."""
    label = {token: name for name, token in grid.items()}
    pattern = re.compile(r"(.+?)_(%s)_(.+)$" % "|".join(RELATIONS))
    facts = []
    for name in sorted(theorems):
        match = pattern.fullmatch(name)
        if match and match[1] in label and match[3] in label:
            facts.append((label[match[1]], match[2], label[match[3]], name))
    for a, relation, b, applied in EXTRA:
        if a in grid and b in grid:
            name = applied.split()[0]
            if name not in theorems:
                sys.exit(f"class_inclusions: `{name}` (in EXTRA) is not a theorem in {SOURCES}")
            facts.append((a, relation, b, applied))
    return facts


def close(nodes, facts, complements: bool):
    """Inclusions and non-inclusions implied by `facts`."""
    sub = {(a, a) for a in nodes}
    non = set()
    for a, relation, b, *_ in facts:
        if relation in ("subset", "ssubset", "eq"):
            sub.add((a, b))
        if relation == "eq":
            sub.add((b, a))
        if relation == "ssubset":
            non.add((b, a))
        if relation == "not_subset":
            non.add((a, b))
    if complements:
        def co(x):
            return x if x in CO_CLOSED else COMPLEMENT.get(x)
        sub |= {(co(a), co(b)) for a, b in sub if co(a) and co(b)}
        non |= {(co(a), co(b)) for a, b in non if co(a) and co(b)}
    changed = True
    while changed:
        changed = False
        for (a, b), (c, d) in itertools.product(list(sub), list(sub)):
            if b == c and (a, d) not in sub:
                sub.add((a, d))
                changed = True
    non = {(a, b) for a, b in itertools.product(nodes, nodes)
           if any((z, a) in sub and (b, y) in sub for z, y in non)}
    return sub, non


def link(declaration, theorems):
    return f"../../{theorems[declaration.split()[0]].relative_to(ROOT).as_posix()}"


def grid_table(title, grid, theorems, problems):
    nodes = list(grid)
    facts = library_facts(grid, theorems)
    direct = {}
    for a, relation, b, declaration in facts:
        direct.setdefault((a, b), declaration)
        if relation == "eq":
            direct.setdefault((b, a), declaration)
    proved, refuted = close(nodes, facts, complements=False)
    literature = [f for f in LITERATURE if f[0] in grid and f[2] in grid]
    known, false = close(nodes, literature, complements=grid is UNIFORM)
    lines = [f"## {title}", "",
             "| ⊆ | " + " | ".join(nodes) + " |",
             "|---|" + "---|" * len(nodes)]
    for a in nodes:
        cells = []
        for b in nodes:
            pair = (a, b)
            if pair in proved and pair not in known or pair in refuted and pair not in false:
                problems.append(f"{a} vs {b}: the library proves what the literature layer does not")
            if a == b:
                cell = "·"
            elif pair in proved:
                mark = "=" if (b, a) in proved else "✓" if pair in direct else "✓*"
                cell = f"[{mark}]({link(direct[pair], theorems)})" if pair in direct else mark
            elif pair in refuted:
                cell = "✗"
            elif pair in known:
                cell = "(✓)"
            elif pair in false:
                cell = "(✗)"
            else:
                cell = "?"
            cells.append(cell)
        lines.append(f"| **{a}** | " + " | ".join(cells) + " |")
    used = sorted({(a, b, d) for a, _, b, d in facts},
                  key=lambda f: (nodes.index(f[0]), nodes.index(f[1]), f[2]))
    lines += ["", "<details><summary>Theorems used</summary>", "",
              "| Statement | Declaration |", "|---|---|"]
    for a, b, declaration in used:
        relation = next(r for x, r, y, d in facts if (x, y, d) == (a, b, declaration))
        symbol = {"subset": "⊆", "ssubset": "⊊", "eq": "=", "not_subset": "⊄"}[relation]
        lines.append(f"| {a} {symbol} {b} | [`{declaration}`]({link(declaration, theorems)}) |")
    lines += ["", "</details>", ""]
    return lines


def render() -> str:
    theorems = locate()
    problems: list[str] = []
    body = []
    for title, grid in GRIDS:
        body += grid_table(title, grid, theorems, problems)
    if problems:
        sys.exit("class_inclusions: inconsistent layers:\n  " + "\n  ".join(problems))
    sources = ["| Fact | Source |", "|---|---|"]
    for a, relation, b, source in LITERATURE:
        sources.append(f"| {a} {'⊆' if relation == 'subset' else '⊄'} {b} | {source} |")
    sources += ["", "Complements are used only for these classes, which are closed under "
                "complement, and for the pairs NP/coNP and RP/coRP.", "",
                "| Class | Why it is closed under complement |", "|---|---|"]
    for name, source in CO_CLOSED.items():
        sources.append(f"| {name} | {source} |")
    return "\n".join([
        "# Inclusions between complexity classes",
        "",
        "[Chapter index](index.md) · [Major endpoints](endpoints-and-hierarchies.md) · "
        "[Verifier models](verifiers-counting-interaction.md)",
        "",
        "<!-- Generated by scripts/class_inclusions.py; edit the script, not this page. -->",
        "",
        "Each cell says whether the row class is contained in the column class: what the library "
        "proves, and otherwise what is known.",
        "",
        "| Mark | Meaning |",
        "|---|---|",
        "| ✓ | A library theorem states the inclusion; the mark links to it |",
        "| = | The library proves both inclusions |",
        "| ✓* | The inclusion follows by chaining library theorems |",
        "| ✗ | The library proves that the inclusion fails |",
        "| (✓) | Known to hold, not yet formalized here |",
        "| (✗) | Known to fail, not yet formalized here |",
        "| ? | An open question in the literature |",
        "",
        "Known non-inclusions all come from hierarchy theorems or lower bounds: `Z ⊄ Y` gives "
        "`A ⊄ B` whenever `Z ⊆ A` and `B ⊆ Y`. For the uniform classes, complements are used "
        "too: `NP ⊆ coNP` holds exactly when `coNP ⊆ NP`.",
        "",
        "The uniform grid compares classes of bit-string languages, that is, the classes at the "
        "encoding `encBits`. Most of the linked inclusion theorems are more general and hold for "
        "every injective encoding `enc`. The strict inclusions behind the ✗ marks "
        "(`L ⊊ PSPACE`, `P ⊊ EXP`, `NP ⊊ NEXP`) are stated only for `encBits`, and they can fail "
        "for other encodings: with a single instance, every class is the same. The circuit "
        "classes are nonuniform, so they are "
        "not compared with the uniform classes: nonuniform AC⁰ already contains undecidable "
        "unary languages.",
        "",
        *body,
        "## Literature layer",
        "",
        "These unconditional results, closed under chaining and complements, decide every cell "
        "that is not marked ?. A cell marked ? is open: neither the inclusion nor its failure "
        "follows from them.",
        "",
        *sources,
        "",
        "## Regenerating",
        "",
        "Run `python3 scripts/class_inclusions.py` after adding an inclusion theorem, and "
        "`python3 scripts/class_inclusions.py --check` to test whether this page is current. New "
        "theorems named `A_subset_B`, `A_ssubset_B`, `A_eq_B` or `A_not_subset_B` between "
        "classes of a grid appear automatically. The script refuses to write a page on which the "
        "library proves something the literature layer calls open or false.",
        "",
    ])


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--check", action="store_true", help="exit 1 if the page is stale")
    args = parser.parse_args()
    text = render()
    if args.check:
        if not PAGE.is_file() or PAGE.read_text(encoding="utf-8") != text:
            print(f"{PAGE.relative_to(ROOT)} is out of date; run scripts/class_inclusions.py")
            return 1
        return 0
    PAGE.write_text(text, encoding="utf-8")
    print(f"wrote {PAGE.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
