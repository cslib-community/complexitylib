#!/usr/bin/env python3
"""Name compound encodings that public statements repeat (#1656).

Usage: python3 scripts/check_encoding_readability.py
           [--base REF | --all | --report | --list [PREFIX]]
           [--update-baseline [--allow-increase]] [--summary [N]] [--root DIR] [--baseline FILE]

This checks rule 1 of "Encodings in statements" in AGENTS.md. A *compound encoding* is an
application of one of the generic combinators `encPair`, `encList`, `encOption`, `encSum`,
`encFramed`, `encPi` or `encDPi` (`COMBINATORS`) with an application of one of them as an
argument, such as `encPair encS (encOption encBool)`. `encPair encNat encNat` is not compound, and
neither is `encPair encNat (encCSP (encOption e) encNat)`, whose inner combinator is an argument of
another function. A compound encoding
that the signatures of three or more public declarations of a module spell out is a violation:
give it a documented, reducible `abbrev` (or use one that already exists with the same meaning)
and write the name in those statements.

A signature runs from the declaration's name to the first top-level `:=`, `where` or equation
clause `| … =>` (for `structure`, `class` and `inductive`, the first top-level `|`), so proofs and
bodies do not count, nor does the body of the `abbrev` that names an encoding. Each field of a
structure or class is a declaration too, whose signature is its type. Terms are compared up to
whitespace, comments and the names of local variables, which become `?1`, `?2`, … in order of
first appearance. Local variables are the binders of the declaration, the `variable`s in scope,
for a field the structure's parameters and earlier fields, and the names bound inside the
signature by `∀`, `∃`, `fun`, `λ`, the big operators, `let`, `have`, `(x : T) → …` and
`{x | …}`. Each of these is visible from the end of its binder (after the type in `(x : T)`, after
the value in `let x := v`) to the end of its enclosing brackets, and an inner binder shadows an
outer one of the same name. So `encPair encS (encOption encBool)` and
`encPair encT (encOption encBool)` are the same term `encPair ?1 (encOption encBool)` when `encS`
and `encT` are local, and `enc.index` is `?1.index` when `enc` is. Everything else is compared
verbatim: `Turing.encPair` differs from `encPair`. Occurrences inside larger terms count, such as
the restated input encoding in `fun p => (encPair encS (encOption encBool) p).length`.

Only public declarations count: in a `module`, those inside a `public section` or marked `public`,
and not `private` or `local`. Declarations in a namespace with an `Internal` component, and modules
with an `Internal` path component, are not counted. Every module under `CslibFrontier/` is checked; the
tests are not.

A declaration counts towards a term when it spells the term out other than inside an occurrence
of a longer violation, which is reported instead: naming the longer term fixes both. The result is
the same pass or fail as counting every occurrence; only the numbers differ.

`scripts/encoding_readability_baseline.json` records the violations that the #1656 sweep has yet
to name, as `{module path: {term: number of declarations}}`. In a module that the change touches
(adds, modifies or deletes, against the merge base of `--base`, default `origin/main`, and the
working tree, as `scripts/check_changed_files.py` computes it), every violation must match its
entry exactly. A violation without an entry, or with more declarations than its entry, fails. An
entry that records more declarations than remain, or that no longer occurs, fails too until the
baseline is lowered in the same change, so that a named encoding cannot be spelled out again later.
Differences in modules that the change does not touch are reported but do not fail: existing code
is brought in line when it is next modified, and by the sweep. Pull requests run this mode.

`--all` enforces the baseline in every module, for maintenance. `--report` prints every difference
and always succeeds; merge groups and pushes to `main` run it, so that queued changes written before
a baseline entry was lowered are not ejected. Merges can therefore leave `main` above the baseline
in some module; the next change that touches that module names the encoding or, with
`--update-baseline --allow-increase`, records it.

`--update-baseline` rewrites the entries of the touched modules (with `--all`, of every module)
with the current violations; it refuses to add or raise an entry unless `--allow-increase` is
given, for instance when a module moves or a rename changes the spelling of recorded terms.
`--summary` prints the totals, the counts per top-level directory of `CslibFrontier/`, the modules
with the most violations and the terms repeated in several modules.

`--list [PREFIX]` is for the sweep. It ignores the baseline and prints every violation, with its
declarations, in the modules whose path is PREFIX or lies under it (such as `CslibFrontier/Logics`),
or in every module. It also prints the `local notation`s whose right-hand side contains a compound
encoding: the check reads a notation as an atom, so these hide compound encodings, and rule 3
asks for a documented `abbrev` instead. It always succeeds, and combines with neither the other
modes nor `--update-baseline` or `--summary`.

The check reads only the sources: it needs no build outputs.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_changed_files as ccf  # noqa: E402
from proof_lengths import command_starts, masks, signature_end  # noqa: E402

BASELINE = ROOT / "scripts/encoding_readability_baseline.json"
UPDATE = "python3 scripts/check_encoding_readability.py --update-baseline"
# The generic encoding combinators (`CslibFrontier/Computability/Machines/Turing/MultiTape/
# Encodings/`) and their explicit arities.
COMBINATORS = {"encPair": 2, "encList": 1, "encOption": 1, "encSum": 2, "encFramed": 1,
               "encPi": 1, "encDPi": 1}
# A compound term is repeated when at least this many public declarations of a module spell it out.
MIN_DECLARATIONS = 3

MODIFIER = r"(?:public|private|protected|noncomputable|unsafe|partial|nonrec|scoped|local|meta)"
# `open … in`, `set_option … in` and the other prefixes of the command that follows.
PREFIX = re.compile(r"(?:open|set_option|include|omit|variable|attribute|unseal|seal|#\w+)\b"
                    r"[^\n]*?(?<![\w'.!?])in(?![\w'!?])")
HEADER = re.compile(rf"((?:{MODIFIER}\s+)*)(class\s+inductive|[a-z_]+)(?![\w'!?])")
# `public meta section`, which `proof_lengths.COMMAND` does not recognize as a command.
EXTRA_SCOPE = re.compile(rf"^(?:@\[[^\]\n]*\]\s*)*(?:{MODIFIER}\s+)+section\b", re.M)
DECLARATIONS = {"theorem", "lemma", "def", "abbrev", "instance", "structure", "class",
                "class inductive", "inductive", "opaque", "axiom"}
TYPE_DECLARATIONS = {"structure", "class", "class inductive", "inductive"}
IDENT = r"[^\W\d][\w'!?]*(?:\.(?:[^\W\d][\w'!?]*|\d+))*"
TOKEN = re.compile(
    rf"(?P<ident>{IDENT})|(?P<num>\d[\w.]*)"
    r"|(?P<open>[(\[{⟨⦃])|(?P<close>[)\]}⟩⦄])|(?P<space>\s+)|(?P<other>.)", re.S)
# Words that end an application instead of supplying an argument.
KEYWORDS = {"fun", "by", "do", "then", "else", "with", "at", "in", "from", "if", "match", "let",
            "have", "show", "calc", "where", "deriving", "forall", "exists", "using", "λ"}
# Binders of a term: quantifiers and big operators take `x y : T,`, `x ∈ s,` or `(x : T),`.
QUANTIFIERS = frozenset("∀∃ΠΣ∑∏⨆⨅⋃⋂∫")
BINDER_PREDICATES = frozenset("∈∉<≤>≥⊆⊂≠") | {"in"}
TYPE_END = re.compile(r"(?P<open>[(\[{⟨⦃])|(?P<close>[)\]}⟩⦄])|:=|\|"
                      r"|(?<![\w'.!?])(?:where|deriving)(?![\w'!?])")
FIELD_END = re.compile(r"(?P<open>[(\[{⟨⦃])|(?P<close>[)\]}⟩⦄])|:=")
# Mentions of the combinators in raw source, to skip files that cannot hold a compound term.
COMBINATOR_NAME = re.compile(r"(?<![\w'])(?:" + "|".join(COMBINATORS) + r")(?![\w'!?])")


@dataclass
class Declaration:
    name: str
    line: int
    signature: str  # masked source
    locals: frozenset[str]  # the binders and `variable`s in scope outside the signature


@dataclass
class Violation:
    term: str  # canonical, with `?1`, `?2`, … for local variables
    spelling: str  # as first written
    declarations: list[tuple[str, int]] = field(default_factory=list)  # (name, line)


@dataclass
class Notation:
    line: int
    lhs: str  # the notation's name and parameters, as written
    rhs: str  # with whitespace normalized


@dataclass
class _Scope:
    label: str  # the name that `end` repeats, "" for an anonymous section or `mutual`
    namespace: tuple[str, ...]
    public: bool  # whether declarations are public by default
    variables: frozenset[str] = frozenset()


def _skip_brackets(text: str, pos: int) -> int:
    """The offset after the bracket group that opens at `pos`."""
    depth = 0
    for i in range(pos, len(text)):
        if text[i] in "([{⟨⦃":
            depth += 1
        elif text[i] in ")]}⟩⦄":
            depth -= 1
            if depth == 0:
                return i + 1
    return len(text)


def _skip_space(text: str, pos: int) -> int:
    while pos < len(text) and text[pos].isspace():
        pos += 1
    return pos


def _header(command: str) -> tuple[set[str], str, int, int] | None:
    """The modifiers and keyword of a command, after its attributes and `… in` prefixes, with the
    offsets where the keyword starts and ends."""
    pos = _skip_space(command, 0)
    while command.startswith("@[", pos) or PREFIX.match(command, pos):
        prefix = PREFIX.match(command, pos)
        pos = _skip_space(command, prefix.end() if prefix else _skip_brackets(command, pos + 1))
    match = HEADER.match(command, pos)
    if not match:
        return None
    return set(match[1].split()), re.sub(r"\s+", " ", match[2]), match.start(2), match.end()


def _name(command: str, pos: int, keyword: str) -> tuple[str | None, int]:
    """The name declared after the keyword that ends at `pos`, and the offset after it.
    Anonymous instances have no name."""
    pos = _skip_space(command, pos)
    if keyword == "instance" and command.startswith("(priority", pos):
        pos = _skip_space(command, _skip_brackets(command, pos))
    token = TOKEN.match(command, pos)
    if token and token.lastgroup == "ident" and token[0] not in KEYWORDS:
        return token[0], token.end()
    return None, pos


def binder_names(text: str, stop_at_colon: bool) -> set[str]:
    """The names bound by the top-level binder groups `(x y : T)`, `{x : T}`, `⦃x : T⦄` and
    `[x : T]` of `text`, up to its first top-level `:` when `stop_at_colon`."""
    names, pos = set(), 0
    while pos < len(text):
        pos = _skip_space(text, pos)
        if pos >= len(text):
            break
        if text[pos] in "({⦃[":
            end = _skip_brackets(text, pos)
            group = text[pos + 1:end - 1].lstrip("{").rstrip("}")
            colon = re.search(r"(?<![:=]):(?![=:])", group)
            if colon and "(" not in group[:colon.start()]:
                names |= {name for name in group[:colon.start()].split()
                          if name != "_" and re.fullmatch(IDENT, name)}
            pos = end
        elif stop_at_colon and text[pos] == ":":
            break
        else:
            pos += 1
    return names


def _first_top_level(text: str, ends: re.Pattern[str]) -> int:
    """The offset of the first match of `ends` outside brackets in `text`, or its length."""
    depth = 0
    for token in ends.finditer(text):
        if token.lastgroup == "open":
            depth += 1
        elif token.lastgroup == "close":
            depth = max(0, depth - 1)
        elif not depth:
            return token.start()
    return len(text)


def _signature_end(text: str, keyword: str) -> int:
    """Where the signature that starts `text` ends."""
    if keyword not in TYPE_DECLARATIONS:
        try:
            return signature_end(text)[0]
        except ValueError:  # an equation clause on the declaration's line, or no body
            pass
    return _first_top_level(text, TYPE_END)


def _fields(text: str, begin: int, end: int, owner: str, local_names: frozenset[str]
            ) -> list[Declaration]:
    """The public fields of a structure or class whose body after `where` is the masked source
    `text[begin:end]`, as declarations. A field may mention the structure's parameters and the
    fields before it."""
    body = text[begin:end]
    lines = []
    for line in re.finditer(r"^([ \t]*)(\S)", body, re.M):
        if not line[1] and line.start() > 0:
            break  # a command such as `deriving` at the start of a line
        lines.append(line)
    indent = min((len(line[1]) for line in lines if line[1]), default=0)
    starts = [line.start(2) for line in lines if len(line[1]) == indent] + [len(body)]
    found, scope = [], set(local_names)
    for start, stop in zip(starts, starts[1:]):
        chunk = body[start:stop]
        if re.match(r"\S+\s*::", chunk) or re.match(r"private\b", chunk):
            continue  # the constructor's name, or a private field
        name = re.match(IDENT, chunk)
        signature = chunk[name.end():] if name else chunk
        signature = signature[:_first_top_level(signature, FIELD_END)]
        names = {name[0]} if name else binder_names(chunk, stop_at_colon=False)
        line = text.count("\n", 0, begin + start) + 1
        found.append(Declaration(f"{owner}.{name[0] if name else min(names, default='?')}",
                                 line, signature,
                                 frozenset(scope | binder_names(signature, stop_at_colon=True))))
        scope |= names
    return found


def public_declarations(text: str, notations: list[Notation] | None = None
                        ) -> list[Declaration]:
    """The public declarations of a Lean source file outside `Internal` namespaces, with their
    signatures. If `notations` is given, append to it the `local notation`s outside `Internal`
    namespaces whose right-hand side contains a compound encoding."""
    _, syntax = masks(text)
    in_module = re.search(r"^module\b", syntax, re.M) is not None
    starts = sorted(set(command_starts(syntax)) | {m.start() for m in EXTRA_SCOPE.finditer(syntax)})
    starts.append(len(syntax))
    scopes = [_Scope("", (), not in_module)]
    found = []
    for start, end in zip(starts, starts[1:]):
        command = syntax[start:end]
        header = _header(command)
        if header is None:
            continue
        modifiers, keyword, keyword_start, pos = header
        words = command[pos:].split("\n", 1)[0].split()
        label = words[0] if words else ""
        scope = scopes[-1]
        if keyword == "namespace":
            for part in label.split("."):
                outer = scopes[-1]
                scopes.append(_Scope(part, outer.namespace + (part,), outer.public,
                                     outer.variables))
        elif keyword in ("section", "mutual"):
            scopes.append(_Scope(label if keyword == "section" else "", scope.namespace,
                                 scope.public or "public" in modifiers, scope.variables))
        elif keyword == "end":
            # `end A.B` closes the two scopes of `namespace A.B`; a bare `end` closes one.
            count, labels = 1, [scope.label]
            while label and ".".join(labels) != label and count < len(scopes) - 1:
                count += 1
                labels.insert(0, scopes[-count].label)
            if ".".join(labels) != label:
                count = 1
            del scopes[max(1, len(scopes) - count):]
        elif keyword == "variable":
            scope.variables = scope.variables | binder_names(command[pos:], stop_at_colon=False)
        elif keyword == "notation" and "local" in modifiers and notations is not None:
            arrow = command.find("=>", pos)
            if arrow < 0 or "Internal" in scope.namespace:
                continue
            rhs = command[arrow + 2:]
            if any(compound for *_, compound in encoding_terms(rhs)):
                notations.append(Notation(text.count("\n", 0, start + keyword_start) + 1,
                                          _normalize(text[start + pos:start + arrow]),
                                          _normalize(rhs)))
        elif keyword in DECLARATIONS:
            if modifiers & {"private", "local"} or not (scope.public or "public" in modifiers):
                continue
            name, pos = _name(command, pos, keyword)
            if "Internal" in scope.namespace or (name and "Internal" in name.split(".")):
                continue
            rest = command[pos:]
            split = _signature_end(rest, keyword)
            local_names = scope.variables | binder_names(rest[:split], stop_at_colon=True)
            line = text.count("\n", 0, start + keyword_start) + 1
            name = name or f"{keyword}@{line}"
            found.append(Declaration(name, line, rest[:split], local_names))
            if keyword in ("structure", "class") and re.match(r"where\b", rest[split:]):
                found += _fields(syntax, start + pos + split + 5, end, name, local_names)
    return found


def _normalize(term: str) -> str:
    term = re.sub(r"\s+", " ", term).strip()
    term = re.sub(r"([(\[{⟨⦃]) ", r"\1", term)
    return re.sub(r" ([)\]}⟩⦄])", r"\1", term)


def _tokens(text: str) -> list[re.Match[str]]:
    return [m for m in TOKEN.finditer(text) if m.lastgroup != "space"]


def _matching(tokens: list[re.Match[str]]) -> dict[int, int]:
    """The index of the bracket that closes each opening bracket (`len(tokens)` if none)."""
    match, stack = {}, []
    for k, token in enumerate(tokens):
        if token.lastgroup == "open":
            stack.append(k)
        elif token.lastgroup == "close" and stack:
            match[stack.pop()] = k
    return match | {k: len(tokens) for k in stack}


def _is_colon(tokens: list[re.Match[str]], k: int) -> bool:
    """Whether `tokens[k]` is a type ascription `:`, not part of `:=` or `::`."""
    def adjacent(j: int, text: str) -> bool:
        return 0 <= j < len(tokens) and tokens[j][0] == text and \
            (tokens[j].end() == tokens[k].start() or tokens[j].start() == tokens[k].end())
    return tokens[k][0] == ":" and not any(adjacent(k + d, t) for d in (-1, 1) for t in ":=")


def _group_names(tokens: list[re.Match[str]], match: dict[int, int], open_: int) -> list[int]:
    """The indices of the names a bracketed binder group binds: those before its top-level `:`
    (`(x y : T)`), or, in a group without a type, every name (`{x y}`, a pattern `⟨a, b⟩`); none
    for an anonymous instance binder `[C α]`."""
    close, k, names = match[open_], open_ + 1, []
    while k < close:
        if _is_colon(tokens, k):
            return names
        if tokens[k].lastgroup == "open":
            if tokens[open_][0] in "(⟨":  # a nested pattern
                names += [j for j in range(k, match[k]) if _is_name(tokens[j])]
            k = match[k] + 1
            continue
        if _is_name(tokens[k]):
            names.append(k)
        k += 1
    return [] if tokens[open_][0] == "[" else names


def _is_name(token: re.Match[str]) -> bool:
    return token.lastgroup == "ident" and token[0] not in KEYWORDS and token[0] != "_" and \
        "." not in token[0]


def _binders(tokens: list[re.Match[str]], match: dict[int, int], start: int, stop: int
             ) -> list[tuple[int, int]]:
    """The names bound by the binders `tokens[start:stop]` of a quantifier or `fun` (`x y`,
    `x : T`, `x ∈ s`, `(x : T) {y}`, `⟨a, b⟩`), as `(index, index from which it is visible)`:
    a group's names are visible after the group, so that later binder types can use them, and
    the others from the separator at `stop`."""
    names, k, typed = [], start, False
    while k < stop:
        if tokens[k].lastgroup == "open":
            if not typed:
                names += [(j, match[k] + 1) for j in _group_names(tokens, match, k)]
            k = match[k] + 1
            continue
        if _is_colon(tokens, k) or tokens[k][0] in BINDER_PREDICATES:
            typed = True
        elif not typed and _is_name(tokens[k]):
            names.append((k, stop))
        k += 1
    return names


def _separator(tokens: list[re.Match[str]], match: dict[int, int], start: int, stop: int,
               lambda_: bool) -> int:
    """The index of the `,` (or, for `fun`, `=>` or `↦`) that ends the binders from `start`."""
    k = start
    while k < stop:
        token = tokens[k]
        if token.lastgroup == "open":
            k = match[k] + 1
            continue
        if not lambda_ and token[0] == ",":
            return k
        if lambda_ and (token[0] == "↦" or token[0] == "=" and k + 1 < stop and
                        tokens[k + 1][0] == ">" and tokens[k + 1].start() == token.end()):
            return k
        k += 1
    return stop


def _let_body(text: str, tokens: list[re.Match[str]], match: dict[int, int], let: int,
              stop: int) -> int:
    """The index where the body of the `let` or `have` at `let` starts: after the `;` that ends
    its value, or at the first line that does not continue the value (one that starts no further
    right than the `let`)."""
    def column(k: int) -> int:
        return tokens[k].start() - text.rfind("\n", 0, tokens[k].start()) - 1

    k, assigned = let + 1, False
    while k < stop:
        token = tokens[k]
        if assigned and token[0] == ";":
            return k + 1
        if assigned and "\n" in text[tokens[k - 1].end():token.start()] and \
                column(k) <= column(let):
            return k
        if token.lastgroup == "open":
            k = match[k] + 1
            continue
        assigned |= token[0] == "=" and tokens[k - 1][0] == ":" and \
            tokens[k - 1].end() == token.start()
        k += 1
    return stop


def bound_names(signature: str, outer: frozenset[str] | set[str]) -> dict[int, object]:
    """For each name in `signature` that refers to a local variable, by offset, the variable it
    refers to. The variables are those of `outer` (binders and `variable`s), and those bound
    inside the signature by `∀`, `∃`, `fun`, `λ`, the big operators, `let`, `have`,
    `(x : T) → …` and `{x | …}`. Each is visible from the end of its binder (after the type of
    `(x : T)`, after the value of `let x := v`) to the end of the enclosing brackets, and an
    inner binder shadows an outer one with the same name."""
    tokens = _tokens(signature)
    match = _matching(tokens)
    pending: list[tuple[int, int, str, int]] = []  # (visible from, end, name, variable)
    scopes: list[tuple[int, str, int]] = []  # (end, name, variable), innermost last
    closes: list[int] = []  # the closing brackets of the enclosing groups
    found: dict[int, object] = {}
    binding: set[int] = set()

    def bind(names: list[tuple[int, int]], end: int) -> None:
        for index, visible in names:
            variable = len(binding)
            binding.add(tokens[index].start())
            found[tokens[index].start()] = variable
            pending.append((visible, end, tokens[index][0], variable))

    for k, token in enumerate(tokens):
        scopes = [scope for scope in scopes if scope[0] > k]
        scopes += [(end, name, variable) for visible, end, name, variable in pending
                   if visible <= k < end]
        pending = [entry for entry in pending if entry[0] > k]
        end = closes[-1] if closes else len(tokens)
        text = token[0]
        if token.lastgroup == "open":
            close = match[k]
            if close + 1 < len(tokens) and tokens[close + 1][0] == "→" and text in "({⦃[" and \
                    any(_is_colon(tokens, j) for j in range(k + 1, close)):
                # a dependent arrow `(x : T) → …`
                bind([(j, close + 1) for j in _group_names(tokens, match, k)], end)
            elif text == "{":
                bar = next((j for j in range(k + 1, close) if tokens[j][0] == "|"), None)
                if bar is not None:  # a set-builder `{x | p x}`
                    bind([(j, bar) for j, _ in _binders(tokens, match, k + 1, bar)], close)
            closes.append(close)
        elif token.lastgroup == "close":
            if closes:
                closes.pop()
        elif text in QUANTIFIERS or text in ("fun", "λ"):
            stop = _separator(tokens, match, k + 1, end, text in ("fun", "λ"))
            bind(_binders(tokens, match, k + 1, stop), end)
        elif text in ("let", "have") and k + 1 < len(tokens):
            recursive = tokens[k + 1][0] == "rec"  # `let rec` sees its own name
            j = k + 1 + recursive
            if j < len(tokens) and tokens[j].lastgroup == "open":
                names = _group_names(tokens, match, j)
            else:
                names = [j] if j < len(tokens) and _is_name(tokens[j]) else []
            visible = k if recursive else _let_body(signature, tokens, match, k, end)
            bind([(index, visible) for index in names], end)
        if token.lastgroup == "ident" and token.start() not in binding:
            head = text.partition(".")[0]
            for _, name, variable in reversed(scopes):
                if name == head:
                    found[token.start()] = variable
                    break
            else:
                if head in outer:
                    found[token.start()] = head
    return found


def canonical(signature: str, start: int, end: int, bound: dict[int, object]) -> str:
    """The term `signature[start:end]` with whitespace normalized and its local variables (by
    `bound_names`), also as the head of a dotted name (`F` in `F.encDesc`), replaced by `?1`,
    `?2`, … in order of first appearance."""
    numbers: dict[object, int] = {}
    out = []
    for token in TOKEN.finditer(signature, start, end):
        if token.lastgroup == "ident" and token.start() in bound:
            number = numbers.setdefault(bound[token.start()], len(numbers) + 1)
            head, dot, tail = token[0].partition(".")
            out.append(f"?{number}{dot}{tail}")
        else:
            out.append(token[0])
    return _normalize("".join(out))


def encoding_terms(signature: str) -> list[tuple[int, int, int, bool]]:
    """Every application of an encoding combinator in `signature`, as `(start, end, number of
    combinator applications it contains, whether it is compound)`."""
    tokens = _tokens(signature)
    heads = []
    for i, token in enumerate(tokens):
        if token.lastgroup != "ident" or token[0].rsplit(".", 1)[-1] not in COMBINATORS:
            continue
        if i and tokens[i - 1][0] == "@":
            continue  # explicit implicit arguments: the arity differs
        if i + 1 < len(tokens) and tokens[i + 1][0] == ":" and (
                i + 2 >= len(tokens) or tokens[i + 2][0] != "="):
            continue  # a binder named like a combinator
        heads.append(i)
    starts, head_set = [tokens[i].start() for i in heads], set(heads)
    spans = []
    for i in heads:
        end, j, compound = tokens[i].end(), i + 1, False
        for _ in range(COMBINATORS[tokens[i][0].rsplit(".", 1)[-1]]):
            if j >= len(tokens):
                break
            arg = tokens[j]
            if arg.lastgroup in ("ident", "num") and arg[0] not in KEYWORDS:
                j += 1
            elif arg.lastgroup == "open":
                compound |= arg[0] == "(" and j + 1 in head_set
                depth = 0
                while j < len(tokens):
                    depth += (tokens[j].lastgroup == "open") - (tokens[j].lastgroup == "close")
                    j += 1
                    if not depth:
                        break
            else:
                break
            end = tokens[j - 1].end()
            # A projection of the argument, as in `(f x).enc`.
            while j + 1 < len(tokens) and tokens[j][0] == "." and tokens[j].start() == end and \
                    tokens[j + 1].lastgroup == "ident" and tokens[j + 1].start() == end + 1:
                end, j = tokens[j + 1].end(), j + 2
        start = tokens[i].start()
        spans.append((start, end, sum(start <= s < end for s in starts), compound))
    return spans


def module_violations(declarations: list[Declaration]) -> list[Violation]:
    """The compound encodings that at least `MIN_DECLARATIONS` of `declarations` spell out in
    their signatures, outer terms first."""
    # term -> [(declaration index, start, end, spelling)]
    occurrences: dict[str, list[tuple[int, int, int, str]]] = defaultdict(list)
    size: dict[str, int] = {}
    for index, declaration in enumerate(declarations):
        signature = declaration.signature
        terms = [term for term in encoding_terms(signature) if term[3]]
        bound = bound_names(signature, declaration.locals) if terms else {}
        for start, end, count, _ in terms:
            term = canonical(signature, start, end, bound)
            occurrences[term].append((index, start, end, _normalize(signature[start:end])))
            size[term] = count
    reported: dict[int, list[tuple[int, int]]] = defaultdict(list)
    violations = []
    # A proper subterm has fewer combinator applications, so outer terms come first.
    for term in sorted(occurrences, key=lambda t: (-size[t], t)):
        free = [(index, start, end, spelling)
                for index, start, end, spelling in occurrences[term]
                if not any(s <= start and end <= e for s, e in reported[index])]
        users = sorted({index for index, *_ in free})
        if len(users) < MIN_DECLARATIONS:
            continue
        for index, start, end, _ in free:
            reported[index].append((start, end))
        violations.append(Violation(term, free[0][3], [
            (declarations[i].name, declarations[i].line) for i in users]))
    return violations


def checked_files(root: Path, prefix: str = "") -> list[Path]:
    """The checked modules, or those whose path relative to `root` is `prefix` or lies under it."""
    parts = Path(prefix).parts
    return sorted(path for path in (root / "CslibFrontier").rglob("*.lean")
                  if "Internal" not in path.relative_to(root).with_suffix("").parts
                  and path.relative_to(root).parts[:len(parts)] == parts)


def scan(root: Path, prefix: str = "", notations: dict[str, list[Notation]] | None = None
         ) -> dict[str, list[Violation]]:
    """The violations of each module (under `prefix`) that has any, by source path. If
    `notations` is given, record in it the `local notation`s of each module that abbreviate a
    compound encoding."""
    found = {}
    for path in checked_files(root, prefix):
        rel = path.relative_to(root).as_posix()
        text = path.read_text(encoding="utf-8")
        mentions = len(COMBINATOR_NAME.findall(text))
        # A violation mentions combinators at least this often, a compound encoding twice.
        notes = [] if notations is not None and mentions >= 2 and "notation" in text else None
        if mentions < 2 * MIN_DECLARATIONS and notes is None:
            continue
        try:
            violations = module_violations(public_declarations(text, notes))
        except ValueError as error:
            raise ValueError(f"{rel}: {error}") from error
        if violations:
            found[rel] = violations
        if notes:
            notations[rel] = notes
    return found


def counts(found: dict[str, list[Violation]]) -> dict[str, dict[str, int]]:
    return {path: {v.term: len(v.declarations) for v in violations}
            for path, violations in found.items()}


def load_baseline(path: Path) -> dict[str, dict[str, int]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict) or not all(
            isinstance(k, str) and isinstance(v, dict) and v and all(
                isinstance(t, str) and type(n) is int and n >= MIN_DECLARATIONS
                for t, n in v.items()) for k, v in data.items()):
        sys.exit(f"{path}: expected a JSON object from source paths to objects from terms to "
                 f"declaration counts of at least {MIN_DECLARATIONS}")
    return data


def baseline_text(current: dict[str, dict[str, int]]) -> str:
    return json.dumps({path: dict(sorted(terms.items())) for path, terms in sorted(current.items())
                       if terms}, indent=1, ensure_ascii=False) + "\n"


Change = tuple[str, str, int, int]  # (path, term, declarations, baseline entry)


def compare(current: dict[str, dict[str, int]], baseline: dict[str, dict[str, int]]
            ) -> tuple[list[Change], list[Change]]:
    """`(over, under)`: the violations that are new or have more declarations than their entry,
    and the entries that record more declarations than remain, or that no longer occur. A
    missing entry or violation counts 0."""
    over, under = [], []
    for path in sorted(set(current) | set(baseline)):
        now, then = current.get(path, {}), baseline.get(path, {})
        for term in sorted(set(now) | set(then)):
            count, entry = now.get(term, 0), then.get(term, 0)
            if count > entry:
                over.append((path, term, count, entry))
            elif count < entry:
                under.append((path, term, count, entry))
    return over, under


def violation_lines(path: str, violation: Violation, entry: int = 0) -> list[str]:
    """A violation with its declarations, and its baseline entry if it has one."""
    spelling = f" (as `{violation.spelling}`)" if violation.spelling != violation.term else ""
    recorded = f", baseline {entry}" if entry else ""
    return [f"{path}: `{violation.term}`{spelling} in {len(violation.declarations)} public "
            f"signatures{recorded}:",
            *(f"  {path}:{line}: {name}" for name, line in violation.declarations)]


def over_report(over: list[Change], found: dict[str, list[Violation]]) -> str:
    out = [f"A compound encoding that {MIN_DECLARATIONS} or more public statements of a module "
           "spell out needs a name (#1656; AGENTS.md, \"Encodings in statements\"). Name each "
           "term below with a documented reducible `abbrev`, or reuse one with the same meaning, "
           "and write the name in these statements:"]
    for path, term, _, entry in over:
        out += ["", *violation_lines(path, next(v for v in found[path] if v.term == term), entry)]
    return "\n".join(out)


def listing(found: dict[str, list[Violation]], notations: dict[str, list[Notation]],
            prefix: str, modules: int) -> str:
    """Every violation and compound-encoding notation of the `modules` checked modules under
    `prefix`, for `--list`."""
    out = []
    for path, violations in sorted(found.items()):
        for violation in violations:
            out += [*violation_lines(path, violation), ""]
    if notations:
        out.append("Local notations that abbreviate a compound encoding; replace each with a "
                   "documented reducible `abbrev` (AGENTS.md, \"Encodings in statements\", "
                   "rule 3):")
        out += [f"  {path}:{notation.line}: local notation {notation.lhs} => {notation.rhs}"
                for path, found_here in sorted(notations.items()) for notation in found_here]
        out.append("")
    where = f" under {prefix}" if prefix else ""
    total = sum(len(violations) for violations in found.values())
    count = sum(len(found_here) for found_here in notations.values())
    out.append(f"{total} repeated compound encoding(s) in {len(found)} of {modules} checked "
               f"module(s){where}, and {count} local notation(s) that abbreviate a compound "
               "encoding; listing only, the baseline is ignored and nothing is enforced.")
    return "\n".join(out)


def area(path: str) -> str:
    """The top-level directory of `CslibFrontier/` that holds `path`."""
    parts = Path(path).parts
    return parts[1] if len(parts) > 2 else Path(parts[-1]).stem


def summary(current: dict[str, dict[str, int]], top: int) -> str:
    total = sum(len(terms) for terms in current.values())
    uses = sum(sum(terms.values()) for terms in current.values())
    terms_by_area: Counter[str] = Counter()
    modules_by_area: Counter[str] = Counter()
    modules_by_term: Counter[str] = Counter()
    for path, terms in current.items():
        terms_by_area[area(path)] += len(terms)
        modules_by_area[area(path)] += 1
        modules_by_term.update(terms.keys())
    out = [f"{total} repeated compound encoding(s) in {len(current)} module(s), spelled out in "
           f"{uses} public signature(s).", "", "Area\tTerms\tModules"]
    out += [f"{name}\t{count}\t{modules_by_area[name]}"
            for name, count in sorted(terms_by_area.items(), key=lambda i: (-i[1], i[0]))]
    out += ["", "Terms\tSignatures\tModule"]
    worst = sorted(current.items(), key=lambda i: (-len(i[1]), -sum(i[1].values()), i[0]))
    out += [f"{len(terms)}\t{sum(terms.values())}\t{path}" for path, terms in worst[:top]]
    shared = [(count, term) for term, count in modules_by_term.items() if count > 1]
    if shared:
        out += ["", "Modules\tTerm repeated in several modules (one shared name may serve)"]
        out += [f"{count}\t{term}" for count, term in sorted(shared, key=lambda i: (-i[0], i[1]))]
    return "\n".join(out)


def touched_modules(root: Path, ref: str) -> set[str]:
    """The modules under `CslibFrontier/` that the change adds, modifies or deletes, against the
    merge base of `ref` and `HEAD` (see `check_changed_files.changed_files`) and the working
    tree."""
    added, modified = ccf.changed_files(root, ref)
    deleted = ccf.git(root, "diff", "--no-ext-diff", "--no-renames", "--name-only", "-z",
                      "--diff-filter=D", ccf.comparison_base(root, ref), "--")
    if deleted.returncode:
        sys.exit(f"git diff failed: {deleted.stderr.strip()}")
    return {path for path in [*added, *modified, *deleted.stdout.split("\0")]
            if path.startswith("CslibFrontier/") and path.endswith(".lean")}


def under_report(under: list[Change]) -> str:
    return "\n".join(f"  {path}: `{term}` in {count} public signature(s), baseline {entry}"
                     for path, term, count, entry in under)


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
                       help="ignore the baseline and list every repeated compound encoding with "
                            "its declarations, and the local notations that abbreviate a compound "
                            "encoding, in the modules under the path PREFIX (such as "
                            "CslibFrontier/Logics) or in every module; always succeeds")
    parser.add_argument("--update-baseline", action="store_true",
                        help="rewrite the baseline entries of the enforced modules")
    parser.add_argument("--allow-increase", action="store_true",
                        help="with --update-baseline, allow adding and raising entries")
    parser.add_argument("--summary", nargs="?", type=int, const=15, metavar="N",
                        help="print the totals, the counts per area and the N worst modules "
                             "(default 15) instead of checking")
    parser.add_argument("--root", type=Path, default=ROOT, help="the repository to check")
    parser.add_argument("--baseline", type=Path, help="default: the root's baseline file")
    args = parser.parse_args(argv)
    if args.allow_increase and not args.update_baseline:
        parser.error("--allow-increase needs --update-baseline")
    if args.summary is not None and args.update_baseline:
        parser.error("--summary does not combine with --update-baseline")
    if args.report and args.update_baseline:
        parser.error("--report does not combine with --update-baseline")
    if args.list is not None and (args.update_baseline or args.summary is not None):
        parser.error("--list does not combine with --update-baseline or --summary")
    if args.list is not None:
        notations: dict[str, list[Notation]] = {}
        found = scan(args.root, args.list, notations)
        print(listing(found, notations, args.list, len(checked_files(args.root, args.list))))
        return 0
    baseline_path = args.baseline or args.root / BASELINE.relative_to(ROOT)
    found = scan(args.root)
    current = counts(found)
    if args.summary is not None:
        print(summary(current, args.summary))
        return 0
    baseline = load_baseline(baseline_path) if baseline_path.exists() else {}
    over, under = compare(current, baseline)
    status = (f"{sum(len(terms) for terms in current.values())} repeated compound encoding(s) "
              f"in {len(current)} module(s)")
    touched = None if args.all or args.report else touched_modules(args.root, args.base)
    enforced = (lambda path: True) if touched is None else touched.__contains__
    if args.report:
        if over:
            print(over_report(over, found))
        if under:
            print(("\n" if over else "") + "Stale baseline entries:\n" + under_report(under))
        print(("\n" if over or under else "") + f"{status}; report only, nothing is enforced.")
        return 0
    over_here = [change for change in over if enforced(change[0])]
    under_here = [change for change in under if enforced(change[0])]
    elsewhere = len(over) + len(under) - len(over_here) - len(under_here)
    if args.update_baseline:
        if over_here and not args.allow_increase:
            print(over_report(over_here, found), file=sys.stderr)
            print("\nThe baseline only goes down; pass --allow-increase to raise it on purpose, "
                  "for instance for a moved module or a renamed encoding.", file=sys.stderr)
            return 1
        kept = {path: terms for path, terms in baseline.items() if not enforced(path)}
        kept |= {path: terms for path, terms in current.items() if enforced(path)}
        baseline_path.write_text(baseline_text(kept), encoding="utf-8")
        scope_text = "every module" if touched is None else f"{len(touched)} changed module(s)"
        print(f"Wrote {baseline_path} for {scope_text}: {status}.")
        return 0
    if elsewhere:
        print(f"Not enforced: {elsewhere} difference(s) from the baseline in modules this change "
              "does not touch. The next change to those modules resolves them; run with --all "
              "to list them.")
    if over_here:
        print(over_report(over_here, found), file=sys.stderr)
    if under_here:
        print(("\n" if over_here else "") + "Repeated encodings were named or removed, so the "
              f"baseline is stale. Lower it with `{UPDATE}` and commit the result, so that they "
              "cannot come back:\n" + under_report(under_here), file=sys.stderr)
    if over_here or under_here:
        return 1
    checked = ("every module matches" if touched is None
               else f"the {len(touched)} changed module(s) match")
    print(f"{status}; {checked} the baseline.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
