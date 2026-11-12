#!/usr/bin/env python3
"""Advisory notice: proof blocks that repeat a block of another proof nearly verbatim.

Usage: python3 scripts/proof_copies.py [--base REF | --all] [--min-lines N] [--min-weight N]
           [--max-renamed N] [--max-copies N] [--limit N] [--github] [--root DIR]

A second proof that needs an argument another proof already makes should use a shared lemma
rather than a copy of the argument (#3725). This tool points authors and reviewers at candidates:
the same multi-line tactic block in two theorem or lemma proofs of the library, in one file or in
two files of the same directory. It reads only the sources and needs no build.

By default it examines the `CslibFrontier/` files changed since the merge base of REF (default
`origin/main`), as `scripts/parallel_defs.py` does, and compares their proofs with every proof in
the same directory. It reports a pair when at least one of its two blocks contains an added or
modified line, so a new copy of an old block is reported and untouched old repetition is not.
A renamed or moved file counts as added, so its old repetition is reported again. With `--all`
it examines the whole library, as an audit (well under a minute).

Each proof body becomes a list of logical lines: comments are dropped, whitespace is collapsed, a
line continues while a bracket is open, and leading `·` bullets and `by` are dropped. Local names
are replaced by a placeholder, so a copy whose hypotheses or bound variables are renamed still
matches. A local name is one that the theorem's binders or the quantifiers of its statement bind,
or that the proof binds with `intro`, `rintro`, `obtain`, `rcases … with`, `have`, `let`, `set`,
`fun`, `case`, `next`, a `| pattern =>` alternative and similar forms. Two lines are alike when
they have the same *shape*, which keeps punctuation, tactic names and keywords (`KEYWORDS`) and
abstracts every other name and numeral.

A block is a run of at least `--min-lines` (default 4) consecutive logical lines alike in two
proofs, extended across one line that differs. It is reported when

1. its alike lines differ in at most `--max-renamed` (default 2) pairs of names or numerals, such
   as `size` and `wireCount`, `Sum.inl` and `Sum.inr`, or `2` and `1`; two local names, or
   projections of them (`hp.pos` and `hq.pos`), are not such a pair;
2. at least 3 of them are substantive: they contain at least 3 names other than local ones and
   do not start with `simp`, `simpa`, `dsimp`, `norm_num` or a similar normalization tactic
   (`SIMP_LIKE`). The substantive lines carry at least `--min-weight` (default 15) such names in
   all. Closers (`omega`, `rfl`, `exact h`), introductions and `simp only` lists alone are thus
   never enough;
3. at least 3 of them have distinct shapes, so that a list of facts proved alike (`have hk : Fits
   w k := …`) is not a block.

A window of `--min-lines` lines that occurs in more than `--max-copies` (default 12) places of the
directory is common plumbing rather than a copy, and is ignored. A block that meets a larger
block of the same two proofs shows the same lines at another alignment and is dropped. Each pair
of proofs is reported once, with its largest block; the text counts the others. The defaults
were calibrated against the repeated-machinery findings of the #3725 audit; the PR that added
this tool records the calibration. The detector compares text, not meaning: it does not see the
same argument written differently, a copy in another directory, repetition inside definitions
and instances, or copied definitions (see `scripts/parallel_defs.py`).

A candidate is not a finding. If both blocks make the same argument and a lemma would make both
proofs clearer, prove it once (private if it is plumbing) and use it in both; otherwise leave
them. The tool is advisory: it always exits 0, and it is not a count to drive down. With
`--github` it writes the candidates to the job summary (`$GITHUB_STEP_SUMMARY`) and as notice
annotations on the changed block. `--root DIR` examines another checkout, for calibration.
"""

from __future__ import annotations

import argparse
import bisect
import os
import re
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from parallel_defs import changed_ranges, escape  # noqa: E402
from proof_lengths import DECL, command_starts, masks, signature_end  # noqa: E402

TOKEN = re.compile(
    r"(?P<ident>«[^»\n]*»(?:\.[^\W\d][\w'!?]*)*|[^\W\d][\w'!?]*(?:\.(?:[^\W\d][\w'!?]*|\d+))*)"
    r"|(?P<num>\d+(?:\.\d+)?)|(?P<meta>\?[^\W\d][\w'!?]*|\?_)"
    r"|(?P<sym>:=|=>|<;>|<\|>|<\||\|>\.|\|>|::|\.\.|\S)")
OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"
# Tactic names and keywords: kept in a line's shape, never taken for local names.
KEYWORDS = frozenset("""
    by at with using only from fun λ do then else if match have haveI let letI show calc suffices
    this in generalizing to says obtain rcases rintro intro intros cases cases' induction
    induction' case next exact exacts apply refine refine' constructor use exists existsi left
    right rw rwa rewrite erw simp simp_all simpa dsimp simp_rw norm_num norm_cast push_cast
    exact_mod_cast field_simp ring ring_nf linarith nlinarith positivity omega decide rfl trivial
    aesop grind tauto assumption contradiction exfalso by_contra by_contra! by_cases split
    split_ifs ext funext congr gcongr convert unfold delta change set generalize specialize
    replace clear subst subst_vars rename_i filter_upwards choose peel lift wlog push_neg
    contrapose contrapose! fun_prop infer_instance first try repeat all_goals any_goals iterate
    focus classical symm trans abel bound fin_cases interval_cases nofun nomatch absurd conv lhs
    rhs arg enter ac_rfl apply_fun rel mono continuity measurability norm_num1 simp_arith
    termination_by decreasing_by
    """.split())
# Names that a pattern can mention without binding them.
NOT_BINDERS = KEYWORDS | {"_", "rfl", "none", "some", "nil", "cons", "zero", "succ", "inl",
                          "inr", "true", "false", "unit", "mk", "intro", "refl"}
# Lines starting with these normalize the goal; they never make a block substantive.
SIMP_LIKE = frozenset({"simp", "simp_all", "simpa", "dsimp", "simp_rw", "norm_num", "field_simp",
                       "push_cast", "norm_cast", "simp_arith", "unfold", "delta"})
QUANTIFIERS = frozenset({"∀", "∃", "∃!", "fun", "λ", "∑", "∏", "⋃", "⋂", "⨆", "⨅"})
# What ends a quantifier's binders: `∀ x y,`, `fun x =>`, `∀ x ∈ s,`, `∑ i < n,`.
BINDERS_END = frozenset({",", "=>", "↦", "∈", "∉", "<", "≤", ">", "≥", "⊆", "≠", "|"})
# Forms whose names come before a `:=` or a type ascription.
DEFINING = frozenset({"have", "haveI", "let", "letI", "set", "obtain", "replace"})
# Forms whose name, if any, comes before a `:`.
NAMED_PROPOSITION = frozenset({"by_cases", "suffices", "generalize"})
# Tactics followed by the names they bind.
INTRODUCING = frozenset({"intro", "intros", "rintro", "rename_i", "next", "ext", "funext",
                         "by_contra", "by_contra!", "choose", "choose!"})
MIN_SUBSTANTIVE = 3
MAX_GAP = 1
MIN_DISTINCT = 3

ADVICE = ("These are candidates, not findings. If both blocks make the same argument and a "
          "lemma would make both proofs clearer, prove it once (private if it is plumbing) and "
          "use it in both; otherwise leave them. A block that only looks alike needs no "
          "change or explanation.")
TITLE = "Repeated-proof-block notice"


# --- Reading proofs -----------------------------------------------------------------------------

def tokens(text: str) -> list[tuple[str, str]]:
    """`(kind, text)` pairs: kind `ident`, `num`, `meta` (`?_`, `?x`) or `sym`."""
    return [(m.lastgroup, m.group()) for m in TOKEN.finditer(text)]


def region_end(toks: list[tuple[str, str]], start: int, stops: frozenset[str] | set[str]) -> int:
    """The index of the first token from `start` that is in `stops` outside brackets, or that
    closes a bracket opened before `start`."""
    depth = 0
    for k in range(start, len(toks)):
        text = toks[k][1]
        if text in OPEN:
            depth += 1
        elif text in CLOSE:
            depth -= 1
            if depth < 0:
                return k
        elif not depth and text in stops:
            return k
    return len(toks)


def has_colon(toks: list[tuple[str, str]]) -> bool:
    return region_end(toks, 0, {":"}) < len(toks)


def pattern_names(toks: list[tuple[str, str]], alternative: bool = False) -> set[str]:
    """The names a binder region binds: its plain identifiers, except type ascriptions (after a
    `:`, to the end of the bracket or region) and, in an alternative's pattern, a constructor
    applied to arguments (`succ` in `succ n ih`)."""
    names: set[str] = set()
    depth, skip = 0, None
    for k, (kind, text) in enumerate(toks):
        if text in OPEN:
            depth += 1
        elif text in CLOSE:
            if skip == depth:
                skip = None
            depth = max(0, depth - 1)
        elif skip is not None:
            continue
        elif text == ":":
            skip = depth or -1
        elif kind == "ident" and "." not in text and text not in NOT_BINDERS \
                and not (k and toks[k - 1][1] == "."):
            starts = not k or toks[k - 1][1] in OPEN or toks[k - 1][1] in (",", "|")
            following = toks[k + 1] if k + 1 < len(toks) else ("", "")
            if alternative and starts and (following[0] in ("ident", "num")
                                           or following[1] in ("⟨", "(")):
                continue
            names.add(text)
    return names


def quantified_names(toks: list[tuple[str, str]]) -> set[str]:
    """Names bound by the quantifiers, `fun`s and set-builders `{x | …}` in a term."""
    names: set[str] = set()
    for k, (_, text) in enumerate(toks):
        if text in QUANTIFIERS:
            names |= pattern_names(toks[k + 1:region_end(toks, k + 1, BINDERS_END)])
        elif text == "{":
            bar = region_end(toks, k + 1, {"|"})
            if bar < len(toks) and toks[bar][1] == "|" and bar - k <= 4:
                names |= pattern_names(toks[k + 1:bar])
    return names


def signature_names(signature: str) -> set[str]:
    """Names bound by a theorem's binders, before the colon of its statement, and by the
    quantifiers of the statement."""
    toks = tokens(signature)
    colon = region_end(toks, 0, {":"})
    names: set[str] = set()
    k = 0
    while k < colon:
        text = toks[k][1]
        if text in "({⦃[":
            end = region_end(toks, k + 1, set())
            group = toks[k + 1:end]
            if text in "{⦃" or has_colon(group):
                names |= pattern_names(group)
            k = end
        k += 1
    return names | quantified_names(toks[colon:])


def bound_names(line: list[tuple[str, str]]) -> set[str]:
    """Names that a logical line of a proof binds."""
    names = quantified_names(line)
    if line and line[0][1] == "|":
        names |= pattern_names(line[1:region_end(line, 1, {"=>"})], alternative=True)
    for k, (kind, text) in enumerate(line):
        if kind != "ident":
            continue
        if text == "with":
            stop = region_end(line, k + 1, {";", "<;>", ":=", "=>"})
            names |= pattern_names(line[k + 1:stop])
        elif text in DEFINING:
            names |= pattern_names(line[k + 1:region_end(line, k + 1,
                                                         {":=", ";", "<;>", "with", "from"})])
        elif text in NAMED_PROPOSITION:
            region = line[k + 1:region_end(line, k + 1, {":=", ";", "<;>", "with", "from", "by"})]
            if has_colon(region):
                names |= pattern_names(region)
        elif text == "case":
            names |= pattern_names(line[k + 2:region_end(line, k + 1, {"=>"})])
        elif text in INTRODUCING:
            names |= pattern_names(line[k + 1:region_end(line, k + 1,
                                                         {";", "<;>", "=>", "using", ":="})])
    return names


@dataclass
class Line:
    """A logical line of a proof: physical lines `start`..`end` (1-based)."""
    start: int
    end: int
    toks: list[tuple[str, str]]
    words: tuple[str, ...] = ()
    norm: tuple[str, ...] = ()
    shape: int = 0
    weight: int = 0
    substantive: bool = False


@dataclass
class Proof:
    path: str
    name: str
    line: int
    lines: list[Line] = field(default_factory=list)


def logical_lines(body: str, first_line: int) -> list[Line]:
    """The non-blank lines of a masked proof body; a line continues while a bracket is open or
    when the next line starts with `<;>`."""
    out: list[Line] = []
    depth = 0
    for offset, raw in enumerate(body.split("\n")):
        toks = tokens(raw)
        if not toks:
            continue
        number = first_line + offset
        if out and (depth > 0 or toks[0][1] == "<;>"):
            out[-1].toks += toks
            out[-1].end = number
        else:
            out.append(Line(number, number, toks))
        for _, text in toks:
            if text in OPEN:
                depth += 1
            elif text in CLOSE:
                depth = max(0, depth - 1)
    return out


def normalize(line: Line, local: set[str]) -> None:
    """Drop leading bullets and `by`, replace local names by `?` (keeping a projection: `?.le`),
    and compute the line's shape and weight."""
    toks = line.toks
    while toks and toks[0][1] in ("·", "by"):
        toks = toks[1:]
    norm, shape, weight = [], [], 0
    for kind, text in toks:
        if kind == "ident":
            head, dot, rest = text.partition(".")
            if head in local:
                norm.append("?" + dot + rest)
                shape.append("?")
                weight += bool(dot)
            else:
                norm.append(text)
                shape.append(text if text in KEYWORDS else "?")
                weight += text not in ("_", "by")
        elif kind == "num":
            norm.append(text)
            shape.append("#")
            weight += 1
        else:
            norm.append(text)
            shape.append(text)
    line.words = tuple(text for _, text in toks)
    line.norm = tuple(norm)
    line.shape = hash(tuple(shape))
    line.weight = weight
    line.substantive = weight >= 3 and bool(norm) and norm[0] not in SIMP_LIKE


def scan_file(text: str, path: str) -> list[Proof]:
    """The theorem and lemma proofs of a Lean source file. Proofs whose statement cannot be
    delimited are skipped."""
    try:
        _, syntax = masks(text)
    except ValueError:
        return []
    starts = [0] + [m.end() for m in re.finditer("\n", syntax)]
    boundaries = command_starts(syntax) + [len(syntax)]
    proofs = []
    for match in DECL.finditer(syntax):
        start = match.start()
        end = boundaries[bisect.bisect_right(boundaries, match.end())]
        try:
            statement_end, body = signature_end(syntax[start:end])
        except ValueError:
            continue
        lines = logical_lines(syntax[start + body:end], bisect.bisect_right(starts, start + body))
        local = signature_names(syntax[match.end():start + statement_end])
        for line in lines:
            local |= bound_names(line.toks)
        for line in lines:
            normalize(line, local)
        proofs.append(Proof(path, match[2], bisect.bisect_right(starts, start),
                            [line for line in lines if line.norm]))
    return proofs


# --- Matching -----------------------------------------------------------------------------------

@dataclass
class Copy:
    """Lines `i`..`i + n - 1` of proof `a` and `j`..`j + n - 1` of proof `b` are alike, except
    `gaps` lines; `renamed` lists the pairs of differing names or numerals of the alike lines,
    other than local names. `others` are further blocks of the same two proofs."""
    a: Proof
    b: Proof
    i: int
    j: int
    n: int
    gaps: int = 0
    renamed: tuple[tuple[str, str], ...] = ()
    weight: int = 0
    substantive: int = 0
    distinct: int = 0
    others: list[Copy] = field(default_factory=list)

    def span(self, side: str = "a") -> tuple[int, int]:
        proof, k = (self.a, self.i) if side == "a" else (self.b, self.j)
        return proof.lines[k].start, proof.lines[k + self.n - 1].end

    def swapped(self) -> Copy:
        return Copy(self.b, self.a, self.j, self.i, self.n, self.gaps,
                    tuple((t, s) for s, t in self.renamed), self.weight, self.substantive,
                    self.distinct, [other.swapped() for other in self.others])

    def text(self) -> str:
        (s, e), (t, f) = self.span("a"), self.span("b")
        where = "" if self.a.path == self.b.path else f"{self.b.path}, "
        renamed = [f"`{x}` in place of `{y}`" for x, y in self.renamed]
        notes = (f", with {', '.join(renamed)}" if renamed else "") + \
            (f"; {self.gaps} line(s) differ" if self.gaps else "") + \
            (f"; {len(self.others)} more block(s) of these proofs are alike"
             if self.others else "")
        return (f"`{self.a.name}` (lines {s}–{e}) and `{self.b.name}` ({where}lines {t}–{f}) "
                f"share {self.n} tactic lines, alike up to local names{notes}.")


def diagonals(proofs: list[Proof], window: int, max_copies: int
              ) -> dict[tuple[int, int, int], list[int]]:
    """Windows of `window` alike lines in two places, grouped by `(proof a, proof b, j - i)`, as
    the lists of their starts `i` in proof `a`. Windows in more than `max_copies` places are
    skipped, as are overlapping windows of one proof."""
    index: dict[tuple[int, ...], list[tuple[int, int]]] = defaultdict(list)
    for p, proof in enumerate(proofs):
        shapes = [line.shape for line in proof.lines]
        for i in range(len(shapes) - window + 1):
            index[tuple(shapes[i:i + window])].append((p, i))
    found: dict[tuple[int, int, int], list[int]] = defaultdict(list)
    for spots in index.values():
        if not 2 <= len(spots) <= max_copies:
            continue
        for x, (p, i) in enumerate(spots):
            for q, j in spots[x + 1:]:
                if p != q or j - i >= window:
                    found[(p, q, j - i)].append(i)
    return found


def is_local(token: str) -> bool:
    """A local name or a projection of one, after `normalize`, or a hole `_`."""
    return token == "_" or token.startswith("?") and token != "?_"


def score(copy: Copy) -> Copy:
    """Compute the renamed pairs, the substantive lines, the weight and the distinct shapes of a
    copy's alike lines. Two local names, or projections of them (`hp.pos`, `hq.pos`), are not a
    renaming, nor is the same name, local in one proof and not in the other (a section `variable`
    is not seen as local)."""
    renamed: set[tuple[str, str]] = set()
    shapes = set()
    for k in range(copy.n):
        x, y = copy.a.lines[copy.i + k], copy.b.lines[copy.j + k]
        if x.shape != y.shape:
            continue
        renamed |= {(u, v) for s, t, u, v in zip(x.norm, y.norm, x.words, y.words)
                    if s != t and u != v and not (is_local(s) and is_local(t))}
        shapes.add(x.shape)
        if x.substantive:
            copy.substantive += 1
            copy.weight += x.weight
    copy.renamed = tuple(sorted(renamed))
    copy.distinct = len(shapes)
    return copy


def copies(proofs: list[Proof], window: int, max_copies: int) -> list[Copy]:
    """The maximal runs of alike windows, joined across `MAX_GAP` differing lines."""
    found = []
    for (p, q, d), starts in diagonals(proofs, window, max_copies).items():
        runs: list[list[int]] = []  # [first, end, gaps]
        for i in sorted(starts):
            if runs and i <= runs[-1][1] + MAX_GAP:
                runs[-1][2] += max(0, i - runs[-1][1])
                runs[-1][1] = i + window
            else:
                runs.append([i, i + window, 0])
        for i, end, gaps in runs:
            n = min(end - i, d) if p == q else end - i
            found.append(score(Copy(proofs[p], proofs[q], i, i + d, n, gaps)))
    return found


def reportable(copy: Copy, min_lines: int, min_weight: int, max_renamed: int) -> bool:
    return (copy.n >= min_lines and copy.substantive >= MIN_SUBSTANTIVE
            and copy.weight >= min_weight and len(copy.renamed) <= max_renamed
            and copy.distinct >= MIN_DISTINCT)


def meets(x: tuple[int, int], y: tuple[int, int]) -> bool:
    return x[0] <= y[1] and y[0] <= x[1]


def overlaps(span: tuple[int, int], ranges: list[tuple[int, int]] | None) -> bool:
    """Whether `span` meets one of `ranges`; `None` stands for a whole added file."""
    return ranges is None or any(a <= span[1] and span[0] <= b for a, b in ranges)


def directory_proofs(root: Path, directory: str) -> list[Proof]:
    """The proofs of the Lean files directly in `directory` (relative to `root`)."""
    proofs = []
    for path in sorted((root / directory).glob("*.lean")):
        proofs += scan_file(path.read_text(encoding="utf-8"), str(path.relative_to(root)))
    return proofs


def select(proofs: list[Proof], examined: set[str],
           changed: dict[str, list[tuple[int, int]] | None] | None, min_lines: int = 4,
           min_weight: int = 15, max_renamed: int = 2, max_copies: int = 12) -> list[Copy]:
    """The reportable copies among the proofs of one directory with a block in an `examined`
    file; with `changed`, that block must contain a changed line. That block comes first. Each
    pair of proofs appears once, with its largest copy; the others are in its `others`."""
    pairs: dict[tuple[int, int], list[Copy]] = defaultdict(list)
    for copy in copies(proofs, min_lines, max_copies):
        if reportable(copy, min_lines, min_weight, max_renamed):
            pairs[(id(copy.a), id(copy.b))].append(copy)
    found = []
    for blocks in pairs.values():
        kept: list[Copy] = []
        for copy in sorted(blocks, key=lambda c: (-c.weight, -c.n)):
            # A block meeting a larger one shows the same lines at another alignment.
            if not any(meets(copy.span("a"), k.span("a")) or meets(copy.span("b"), k.span("b"))
                       or copy.a is copy.b and (meets(copy.span("a"), k.span("b"))
                                                or meets(copy.span("b"), k.span("a")))
                       for k in kept):
                kept.append(copy)
        if changed is None:
            first = kept[0] if kept[0].a.path in examined else kept[0].swapped()
            shown = [first] + [k if k.a is first.a else k.swapped() for k in kept[1:]]
            if first.a.path not in examined:
                continue
        else:
            shown = [k if overlaps(k.span("a"), changed.get(k.a.path, [])) else k.swapped()
                     for k in kept]
            shown = [k for k in shown if overlaps(k.span("a"), changed.get(k.a.path, []))]
            if not shown:
                continue
            first = shown[0]
            shown = [first] + [k if k.a is first.a else k.swapped() for k in shown[1:]]
        first.others = shown[1:]
        found.append(first)
    return found


def find(root: Path, paths: list[str], changed: dict[str, list[tuple[int, int]] | None] | None,
         **thresholds: int) -> tuple[list[Copy], int]:
    """The copies with a block in one of `paths` (on a changed line, with `changed`), each file
    compared with the files of its directory, largest first, and the number of proofs in
    `paths`."""
    directories: dict[str, set[str]] = defaultdict(set)
    for rel in paths:
        directories[rel.rsplit("/", 1)[0]].add(rel)
    found: list[Copy] = []
    examined = 0
    for directory, files in sorted(directories.items()):
        proofs = directory_proofs(root, directory)
        examined += sum(p.path in files for p in proofs)
        found += select(proofs, files, changed, **thresholds)
    found.sort(key=lambda c: (-c.weight, c.a.path, c.span()))
    return found, examined


# --- Reports ------------------------------------------------------------------------------------

def markdown(found: list[Copy], examined: int, limit: int) -> str:
    head = f"### {TITLE} (advisory)\n\n"
    if not found:
        return head + f"No repeated proof block in the {examined} proofs examined.\n"
    more = f" The first {limit} are listed." if len(found) > limit else ""
    lines = [head + f"{len(found)} candidate pair(s) of repeated proof blocks in the "
             f"{examined} proofs examined.{more} {ADVICE}\n"]
    lines += [f"- {c.a.path}:{c.span()[0]}: {c.text()}" for c in found[:limit]]
    return "\n".join(lines) + "\n"


def annotations(found: list[Copy], limit: int) -> list[str]:
    return [f"::notice file={escape(c.a.path, True)},line={c.span()[0]},endLine={c.span()[1]},"
            f"title={escape('Possible repeated proof block', True)}::"
            f"{escape(c.text() + ' Advisory only; see the job summary.')}"
            for c in found[:limit]]


def note(message: str, github: bool) -> int:
    print(message)
    if github and os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as summary:
            summary.write(f"### {TITLE} (advisory)\n\n{message}\n")
    return 0


def run(args: argparse.Namespace) -> int:
    root = args.root.resolve()
    if args.all:
        changed = None
        paths = sorted(str(p.relative_to(root)) for p in (root / "CslibFrontier").rglob("*.lean"))
    else:
        changed = changed_ranges(root, args.base)
        paths = sorted(changed)
    if not paths:
        print(f"{TITLE}: no `CslibFrontier/` file added or modified.")
        return 0
    found, examined = find(root, paths, changed, min_lines=args.min_lines,
                           min_weight=args.min_weight, max_renamed=args.max_renamed,
                           max_copies=args.max_copies)
    report = markdown(found, examined, args.limit)
    print(report, end="")
    if args.github:
        for line in annotations(found, args.limit):
            print(line)
        if os.environ.get("GITHUB_STEP_SUMMARY"):
            with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as summary:
                summary.write(report)
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base", default="origin/main",
                        help="comparison ref; changes are taken from its merge base with HEAD")
    parser.add_argument("--all", action="store_true",
                        help="examine every proof of the library (an audit)")
    parser.add_argument("--min-lines", type=int, default=4,
                        help="the fewest alike logical lines in a block (default 4)")
    parser.add_argument("--min-weight", type=int, default=15,
                        help="the fewest names, other than local ones, in the substantive lines "
                        "of a block (default 15)")
    parser.add_argument("--max-renamed", type=int, default=2,
                        help="the most pairs of differing names or numerals (default 2)")
    parser.add_argument("--max-copies", type=int, default=12,
                        help="ignore line windows found in more places of a directory "
                        "(default 12)")
    parser.add_argument("--limit", type=int, default=10, help="report at most this many")
    parser.add_argument("--github", action="store_true",
                        help="write the job summary and notice annotations")
    parser.add_argument("--root", type=Path, default=ROOT,
                        help="the checkout to examine (default: this one)")
    args = parser.parse_args(argv)
    try:
        return run(args)
    except (Exception, SystemExit) as error:  # advisory: never fail the caller
        return note(f"{TITLE} skipped: the tool failed ({error}).", args.github)


if __name__ == "__main__":
    sys.exit(main())
