#!/usr/bin/env python3
"""Build the complexity-class inclusion tables for the API documentation site (stdlib only).

    python3 tools/class_inclusions/build.py --index DIR/declarations/declaration-data.bmp

The page is written to `tools/class_inclusions/_site/index.html` (or `--output`). The API
documentation workflow builds it from the doc-gen4 index of the same run and publishes it at
https://www.cslib.io/cslib-frontier/class-inclusions/, so it always describes the published
library. Two layers are combined for every ordered pair of classes `A`, `B` in a grid:

* **The library.** Theorems named `A_subset_B`, `A_ssubset_B`, `A_eq_B` or `A_not_subset_B`
  between classes of a grid are read from the doc-gen4 declaration index, and each mark links to
  the theorem's API page. `EXTRA` adds instances of theorems that take a parameter, such as
  `NC_subset_AC 1`. Inclusions that follow by chaining proved ones are marked separately from
  those stated directly, and non-inclusions follow from a proved non-inclusion `Z ⊄ Y` whenever
  `Z ⊆ A` and `B ⊆ Y`.
* **The literature.** `LITERATURE` records the inclusions and non-inclusions that are known
  unconditionally, closed under the same two rules. A pair that the literature neither proves nor
  refutes is an open question.

The build fails, rather than publishing, if the library proves something the literature layer
calls open or false, so a mistake in either layer is reported.
"""
from __future__ import annotations

import argparse
import html
import itertools
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
# doc-gen4 links local declarations under these module roots.
LOCAL_PREFIXES = ("./CslibFrontier/", "./Cslib/")

# Grid label -> the token naming the class in theorem names.
UNIFORM = {
    "L": "L", "NL": "NL", "P": "P", "ZPP": "ZPP", "RP": "RP", "coRP": "coRP", "BPP": "BPP",
    "NP": "NP", "coNP": "coNP", "MA": "MA", "AM": "AM", "PH": "PH", "BQP": "BQP", "QMA": "QMA",
    "PP": "PP", "P^#P": "PWithSharpPOracle", "PSPACE": "PSPACE", "IP": "IP", "EXP": "EXP",
    "NEXP": "NEXP", "EXPSPACE": "EXPSPACE",
}
CIRCUIT = {
    "AC⁰": "AC0", "ACC⁰": "ACC0", "TC⁰": "TC0", "NC¹": "NC_one", "AC¹": "AC_one",
    "NC²": "NC_two", "P/poly": "PPoly",
}
# Classes that equal their complement, with the reason, and the complement pairs among the rest.
CO_CLOSED = {
    "L": "deterministic; swap accepting and rejecting states",
    "NL": "Immerman 1988; Szelepcsényi 1987",
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
    "EXPSPACE": "deterministic; swap accepting and rejecting states",
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
    ("ZPP", "subset", "RP", "Gill 1977"),
    ("RP", "subset", "NP", "Gill 1977"),
    ("RP", "subset", "BPP", "Gill 1977"),
    ("NP", "subset", "MA", "by definition"),
    ("BPP", "subset", "MA", "by definition"),
    ("MA", "subset", "AM", "Babai 1985"),
    ("AM", "subset", "PH", "AM ⊆ Π₂ᵖ, Babai 1985"),
    ("NP", "subset", "PH", "by definition"),
    ("BPP", "subset", "BQP", "Bernstein–Vazirani 1997"),
    ("MA", "subset", "QMA", "by definition"),
    ("BQP", "subset", "QMA", "by definition"),
    ("QMA", "subset", "PP", "Kitaev–Watrous 2000"),
    ("NP", "subset", "PP", "Gill 1977"),
    ("PP", "subset", "P^#P", "by definition"),
    ("PH", "subset", "P^#P", "Toda 1991"),
    ("P^#P", "subset", "PSPACE", "counting by enumeration, Arora–Barak Chapter 17"),
    ("PSPACE", "subset", "IP", "Shamir 1992"),
    ("IP", "subset", "PSPACE", "evaluating the game tree in polynomial space, Arora–Barak Chapter 8"),
    ("PSPACE", "subset", "EXP", "counting configurations, Arora–Barak Chapter 4"),
    ("EXP", "subset", "NEXP", "by definition"),
    ("NEXP", "subset", "EXPSPACE",
     "trying every certificate in turn, reusing the space, Arora–Barak Chapter 4"),
    ("PSPACE", "not_subset", "NL",
     "NL ⊆ SPACE(log² n) (Savitch 1970) ⊊ PSPACE by the space hierarchy theorem "
     "(Stearns–Hartmanis–Lewis 1965)"),
    ("EXPSPACE", "not_subset", "PSPACE",
     "space hierarchy theorem (Stearns–Hartmanis–Lewis 1965)"),
    ("EXP", "not_subset", "P", "time hierarchy theorem, Arora–Barak Chapter 3"),
    ("NEXP", "not_subset", "NP",
     "nondeterministic time hierarchy theorem (Žák 1983)"),
    ("NEXP", "not_subset", "coNP",
     "NEXP ⊆ coNP would give NP ⊆ coNP, so NP = coNP ⊇ NEXP, contradicting NP ⊊ NEXP"),
    ("AC⁰", "subset", "ACC⁰", "by definition"),
    ("ACC⁰", "subset", "TC⁰", "a MOD gate is a sum of threshold gates"),
    ("TC⁰", "subset", "NC¹", "iterated addition in logarithmic depth"),
    ("NC¹", "subset", "AC¹", "by definition"),
    ("AC¹", "subset", "NC²", "balanced fan-in-two trees"),
    ("NC²", "subset", "P/poly", "by definition"),
    ("ACC⁰", "not_subset", "AC⁰",
     "parity is not in AC⁰ (Furst–Saxe–Sipser 1984; Ajtai 1983)"),
]

GRIDS = [
    ("Uniform classes", UNIFORM),
    ("Nonuniform circuit classes", CIRCUIT),
]

RELATIONS = ("not_subset", "ssubset", "subset", "eq")
SYMBOL = {"subset": "⊆", "ssubset": "⊊", "eq": "=", "not_subset": "⊄"}


def load_theorems(index: dict) -> dict[str, tuple[str, str]]:
    """Short theorem name -> (full name, link relative to this page), from a doc-gen4 index.

    The short name is the last component of the full name. When several theorems share it, the
    alphabetically first full name is used.
    """
    found: dict[str, tuple[str, str]] = {}
    declarations = index.get("declarations", {})
    for name in sorted(declarations):
        info = declarations[name]
        link = info.get("docLink", "")
        if info.get("kind") != "theorem" or not link.startswith(LOCAL_PREFIXES):
            continue
        found.setdefault(name.rsplit(".", 1)[-1], (name, "../" + link.removeprefix("./")))
    return found


def library_facts(grid: dict[str, str], theorems: dict[str, tuple[str, str]]):
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
                raise ValueError(f"`{name}` (in EXTRA) is not a theorem in the declaration index")
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


def inline(text: str) -> str:
    """Escape `text`, rendering `code` spans."""
    return re.sub(r"`([^`]+)`", r"<code>\1</code>", html.escape(text, quote=False))


def mark(css: str, text: str, title: str, href: str | None = None) -> str:
    title = html.escape(title)
    if href:
        return (f'<td class="{css}"><a href="{html.escape(href)}" title="{title}">'
                f"{text}</a></td>")
    return f'<td class="{css}" title="{title}">{text}</td>'


def grid_table(title, grid, theorems, problems):
    nodes = list(grid)
    facts = library_facts(grid, theorems)

    def href(declaration):
        return theorems[declaration.split()[0]][1]

    direct, direct_non = {}, {}
    for a, relation, b, declaration in facts:
        if relation == "not_subset":
            direct_non.setdefault((a, b), declaration)
            continue
        direct.setdefault((a, b), declaration)
        if relation == "eq":
            direct.setdefault((b, a), declaration)
        if relation == "ssubset":
            direct_non.setdefault((b, a), declaration)
    proved, refuted = close(nodes, facts, complements=False)
    literature = [f for f in LITERATURE if f[0] in grid and f[2] in grid]
    known, false = close(nodes, literature, complements=grid is UNIFORM)
    rows = []
    for a in nodes:
        cells = [f'<th scope="row">{html.escape(a)}</th>']
        for b in nodes:
            pair = (a, b)
            if pair in proved and pair not in known or pair in refuted and pair not in false:
                problems.append(f"{a} vs {b}: the library proves what the literature layer does not")
            if a == b:
                cells.append('<td class="same">·</td>')
            elif pair in proved:
                text = "=" if (b, a) in proved else "✓" if pair in direct else "✓*"
                if pair in direct:
                    cells.append(mark("proved", text, f"{a} ⊆ {b}: {direct[pair]}",
                                      href(direct[pair])))
                else:
                    cells.append(mark("chained", text, f"{a} ⊆ {b}, by chaining library theorems"))
            elif pair in refuted:
                if pair in direct_non:
                    cells.append(mark("refuted", "✗", f"{a} ⊄ {b}: {direct_non[pair]}",
                                      href(direct_non[pair])))
                else:
                    cells.append(mark("refuted chained", "✗*",
                                      f"{a} ⊄ {b}, from library theorems"))
            elif pair in known:
                cells.append(mark("known", "(✓)", f"{a} ⊆ {b}: known, not yet formalized"))
            elif pair in false:
                cells.append(mark("false", "(✗)", f"{a} ⊄ {b}: known, not yet formalized"))
            else:
                cells.append(mark("open", "?", f"{a} ⊆ {b}: open"))
        rows.append("<tr>" + "".join(cells) + "</tr>")
    head = ('<tr><th scope="col">⊆</th>'
            + "".join(f'<th scope="col">{html.escape(b)}</th>' for b in nodes) + "</tr>")
    used = sorted({(a, b, d) for a, _, b, d in facts},
                  key=lambda f: (nodes.index(f[0]), nodes.index(f[1]), f[2]))
    theorem_rows = []
    for a, b, declaration in used:
        relation = next(r for x, r, y, d in facts if (x, y, d) == (a, b, declaration))
        full = theorems[declaration.split()[0]][0]
        shown = full + declaration[len(declaration.split()[0]):]
        theorem_rows.append(
            f"<tr><td>{html.escape(f'{a} {SYMBOL[relation]} {b}')}</td>"
            f'<td><a href="{html.escape(href(declaration))}"><code>{html.escape(shown)}</code>'
            "</a></td></tr>")
    return f"""<h2>{html.escape(title)}</h2>
<p class="grid-caption">Row class ⊆ column class</p>
<div class="table-scroll grid-scroll"><table class="grid">
<thead>{head}</thead>
<tbody>
{chr(10).join(rows)}
</tbody></table></div>
<details><summary>Library theorems used ({len(used)})</summary>
<div class="table-scroll"><table class="list"><thead><tr><th scope="col">Statement</th><th scope="col">Declaration</th></tr></thead>
<tbody>
{chr(10).join(theorem_rows)}
</tbody></table></div></details>"""


# Additions to doc-gen4's style.css, in its colour variables so they follow its light/dark theme.
# A grid scrolls inside its own box, which fits below the fixed header, so that the column and
# row labels stay pinned. Sticky cells lose collapsed borders, hence the separate borders there.
STYLE = """.table-scroll{overflow-x:auto;margin:1em 0}
.grid-scroll{overflow:auto;max-height:calc(100vh - var(--header-height,3em) - 2em)}
.class-inclusions table{border-collapse:collapse}
.class-inclusions th,.class-inclusions td{padding:.25em .5em;border:1px solid var(--code-bg)}
.class-inclusions p,.class-inclusions summary{overflow-wrap:break-word}
.grid-caption{font-style:italic;margin-bottom:0}
.class-inclusions .grid{border-collapse:separate;border-spacing:0}
.class-inclusions .grid th,.class-inclusions .grid td{border-width:0 1px 1px 0}
.class-inclusions .grid thead th{border-top-width:1px}
.class-inclusions .grid th:first-child{border-left-width:1px}
.grid td{text-align:center;min-width:2.4em;white-space:nowrap}
.grid th{white-space:nowrap;background:var(--body-bg)}
.grid thead th{position:sticky;top:0;z-index:1}
.grid tbody th{position:sticky;left:0;text-align:left}
.grid thead th:first-child{left:0;z-index:2}
.grid a{display:block;color:inherit;text-decoration:none}
.proved,.chained{background:var(--theorem-color)}
.refuted{background:var(--axiom-and-constant-color)}
.known{background:color-mix(in srgb,var(--theorem-color) 35%,var(--body-bg))}
.false{background:color-mix(in srgb,var(--axiom-and-constant-color) 35%,var(--body-bg))}
.open{background:color-mix(in srgb,var(--structure-and-inductive-color) 25%,var(--body-bg))}
.list td,.list th{text-align:left;vertical-align:top}
.list td:first-child{white-space:nowrap}
.list code{overflow-wrap:anywhere}
"""

LEGEND = [
    ("proved", "✓", "A library theorem states the inclusion; the mark links to it"),
    ("proved", "=", "The library proves both inclusions"),
    ("chained", "✓*", "The inclusion follows by chaining library theorems"),
    ("refuted", "✗", "A library theorem states that the inclusion fails; the mark links to it"),
    ("refuted", "✗*", "The failure follows from a library theorem and inclusions, as below"),
    ("known", "(✓)", "Known to hold, not yet formalized here"),
    ("false", "(✗)", "Known to fail, not yet formalized here"),
    ("open", "?", "An open question in the literature"),
]


def render(index: dict) -> str:
    theorems = load_theorems(index)
    problems: list[str] = []
    body = [grid_table(title, grid, theorems, problems) for title, grid in GRIDS]
    if problems:
        raise ValueError("inconsistent layers:\n  " + "\n  ".join(problems))
    strict = ", ".join(
        f"<code>{html.escape(f'{a} ⊄ {b}' if relation == 'not_subset' else f'{a} ⊊ {b}')}</code>"
        for a, relation, b, _ in sorted(library_facts(UNIFORM, theorems),
                                        key=lambda f: [list(UNIFORM).index(x) for x in (f[0], f[2])])
        if relation in ("ssubset", "not_subset")) or "none so far"
    legend = "".join(f'<tr><td class="{css}">{text}</td><td>{html.escape(meaning)}</td></tr>'
                     for css, text, meaning in LEGEND)
    sources = "".join(
        f"<tr><td>{html.escape(f'{a} {SYMBOL[relation]} {b}')}</td><td>{inline(source)}</td></tr>"
        for a, relation, b, source in LITERATURE)
    co_closed = "".join(f"<tr><td>{html.escape(name)}</td><td>{inline(source)}</td></tr>"
                        for name, source in CO_CLOSED.items())
    root = "../"
    return f"""<!doctype html>
<html lang="en"><head><meta charset="UTF-8"/><meta name="viewport" content="width=device-width, initial-scale=1"/>
<link rel="stylesheet" href="{root}style.css"/><link rel="icon" href="{root}favicon.svg"/>
<link rel="mask-icon" href="{root}favicon.svg" color="#000000"/>
<title>Inclusions between complexity classes</title>
<script>const SITE_ROOT="{root}";</script>
<script type="module" src="{root}search.js"></script><script type="module" src="{root}expand-nav.js"></script>
<style>
{STYLE}</style></head>
<body><input id="nav_toggle" type="checkbox"/><header><h1><label for="nav_toggle"></label><span>Documentation</span></h1>
<h2 class="header_filename break_within"><span class="name">Inclusions between complexity classes</span></h2>
<form id="search_form"><input type="text" name="q" autocomplete="off"/>&#32;<button id="search_button" onclick="javascript: form.action='{root}search.html';">Search</button></form></header>
<main class="class-inclusions"><a id="top"></a>
<h1>Inclusions between complexity classes</h1>
<p>Whether each standard class is contained in another: what the library proves, and otherwise
what is known. Rebuilt from the library's declarations with every documentation deployment.</p>
<table class="list"><tbody>{legend}</tbody></table>
<p>Known non-inclusions all come from hierarchy theorems or lower bounds: <code>Z ⊄ Y</code> gives
<code>A ⊄ B</code> whenever <code>Z ⊆ A</code> and <code>B ⊆ Y</code>. For the uniform classes,
complements are used too: <code>NP ⊆ coNP</code> holds exactly when <code>coNP ⊆ NP</code>.</p>
<p>The uniform grid compares classes of bit-string languages, that is, the classes at the encoding
<code>encBits</code>. Most of the linked inclusion theorems are more general and hold for every
injective encoding <code>enc</code>. The separations behind the ✗ and ✗* marks
({strict}) are stated only for
<code>encBits</code>, and they can fail for other encodings: with a single instance, every class
is the same. The circuit classes are nonuniform, so they are not compared with the uniform
classes: nonuniform AC⁰ already contains undecidable unary languages.</p>
{chr(10).join(body)}
<h2>Literature layer</h2>
<p>These unconditional results, closed under chaining and complements, decide every cell that is
not marked ?. A cell marked ? is open: neither the inclusion nor its failure follows from them.</p>
<table class="list"><thead><tr><th scope="col">Fact</th><th scope="col">Source</th></tr></thead>
<tbody>{sources}</tbody></table>
<p>Complements are used only for these classes, which are closed under complement, and for the
pairs NP/coNP and RP/coRP.</p>
<table class="list"><thead><tr><th scope="col">Class</th><th scope="col">Why it is closed under complement</th></tr></thead>
<tbody>{co_closed}</tbody></table>
<p>Theorems named <code>A_subset_B</code>, <code>A_ssubset_B</code>, <code>A_eq_B</code> or
<code>A_not_subset_B</code> between classes of a grid appear automatically.
<a href="https://github.com/cslib-community/cslib-frontier/tree/main/tools/class_inclusions">Source and literature layer</a>.</p>
</main><nav class="nav"><iframe src="{root}navbar.html" class="navframe" frameBorder="0"></iframe></nav></body></html>
"""


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--index", type=Path, required=True,
                        help="doc-gen4 declarations/declaration-data.bmp")
    parser.add_argument("--output", type=Path, default=HERE / "_site",
                        help="directory to write index.html into")
    args = parser.parse_args(argv)
    try:
        page = render(json.loads(args.index.read_text(encoding="utf-8")))
    except ValueError as error:
        print(f"class_inclusions: {error}", file=sys.stderr)
        return 1
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "index.html").write_text(page, encoding="utf-8")
    print(f"wrote {args.output / 'index.html'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
