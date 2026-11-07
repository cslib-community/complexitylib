#!/usr/bin/env python3
"""Name compound encodings that public statements repeat (#1656).

Usage: python3 scripts/check_encoding_readability.py [--update-baseline [--allow-increase]]
                                                     [--summary [N]] [--root DIR] [--baseline FILE]

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
whitespace, comments and the names of local variables: the binders of the declaration, the
`variable`s in scope and, for a field, the structure's parameters and earlier fields become `?1`,
`?2`, … in order of first appearance. So `encPair encS (encOption encBool)` and
`encPair encT (encOption encBool)` are the same term `encPair ?1 (encOption encBool)` when `encS`
and `encT` are local, and `enc.index` is `?1.index` when `enc` is. Everything else is compared
verbatim: `Turing.encPair` differs from `encPair`. Occurrences inside larger terms count, such as
the restated input encoding in `fun p => (encPair encS (encOption encBool) p).length`.

Only public declarations count: in a `module`, those inside a `public section` or marked `public`,
and not `private` or `local`. Declarations in a namespace with an `Internal` component, and modules with an
`Internal` path component, are not counted. Every module under `Complexity/` is checked; the
abstracts and the tests are not.

A declaration counts towards a term when it spells the term out other than inside an occurrence
of a longer violation, which is reported instead: naming the longer term fixes both. The result is
the same pass or fail as counting every occurrence; only the numbers differ.

`scripts/encoding_readability_baseline.json` records the violations that the #1656 sweep has yet
to name, as `{module path: {term: number of declarations}}`, and every violation must match its
entry exactly. A violation without an entry, or with more declarations than its entry, fails. An
entry that records more declarations than remain, or that no longer occurs, fails too until the
baseline is lowered in the same change, so that a named encoding cannot be spelled out again later.
`--update-baseline` rewrites the baseline with the current violations; it refuses to add or raise
an entry unless `--allow-increase` is given, for instance when a module moves or a rename changes
the spelling of recorded terms. `--summary` prints the totals, the counts per top-level directory
of `Complexity/`, the modules with the most violations and the terms repeated in several modules.

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
from proof_lengths import command_starts, masks, signature_end  # noqa: E402

BASELINE = ROOT / "scripts/encoding_readability_baseline.json"
UPDATE = "python3 scripts/check_encoding_readability.py --update-baseline"
# The generic encoding combinators (`Complexity/Computability/Machines/Turing/MultiTape/
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
    locals: frozenset[str]  # binder and `variable` names in scope


@dataclass
class Violation:
    term: str  # canonical, with `?1`, `?2`, … for local variables
    spelling: str  # as first written
    declarations: list[tuple[str, int]] = field(default_factory=list)  # (name, line)


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


def public_declarations(text: str) -> list[Declaration]:
    """The public declarations of a Lean source file outside `Internal` namespaces, with their
    signatures."""
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


def canonical(term: str, local_names: frozenset[str] | set[str]) -> str:
    """`term` with whitespace normalized and its local variables, also as the head of a dotted
    name (`F` in `F.encDesc`), replaced by `?1`, `?2`, … in order of first appearance."""
    numbers: dict[str, int] = {}
    out = []
    for token in TOKEN.finditer(_normalize(term)):
        head, dot, tail = token[0].partition(".")
        if token.lastgroup == "ident" and head in local_names:
            out.append(f"?{numbers.setdefault(head, len(numbers) + 1)}{dot}{tail}")
        else:
            out.append(token[0])
    return "".join(out)


def encoding_terms(signature: str) -> list[tuple[int, int, int, bool]]:
    """Every application of an encoding combinator in `signature`, as `(start, end, number of
    combinator applications it contains, whether it is compound)`."""
    tokens = [m for m in TOKEN.finditer(signature) if m.lastgroup != "space"]
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
        for start, end, count, compound in encoding_terms(declaration.signature):
            if compound:
                spelling = declaration.signature[start:end]
                term = canonical(spelling, declaration.locals)
                occurrences[term].append((index, start, end, _normalize(spelling)))
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


def checked_files(root: Path) -> list[Path]:
    return sorted(path for path in (root / "Complexity").rglob("*.lean")
                  if "Internal" not in path.relative_to(root).with_suffix("").parts)


def scan(root: Path) -> dict[str, list[Violation]]:
    """The violations of each module that has any, by source path."""
    found = {}
    for path in checked_files(root):
        rel = path.relative_to(root).as_posix()
        text = path.read_text(encoding="utf-8")
        # A violation mentions combinators at least this often.
        if len(COMBINATOR_NAME.findall(text)) < 2 * MIN_DECLARATIONS:
            continue
        try:
            violations = module_violations(public_declarations(text))
        except ValueError as error:
            raise ValueError(f"{rel}: {error}") from error
        if violations:
            found[rel] = violations
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


def over_report(over: list[Change], found: dict[str, list[Violation]]) -> str:
    out = [f"A compound encoding that {MIN_DECLARATIONS} or more public statements of a module "
           "spell out needs a name (#1656; AGENTS.md, \"Encodings in statements\"). Name each "
           "term below with a documented reducible `abbrev`, or reuse one with the same meaning, "
           "and write the name in these statements:"]
    for path, term, count, entry in over:
        violation = next(v for v in found[path] if v.term == term)
        spelling = f" (as `{violation.spelling}`)" if violation.spelling != term else ""
        recorded = f", baseline {entry}" if entry else ""
        out += ["", f"{path}: `{term}`{spelling} in {count} public signatures{recorded}:"]
        out += [f"  {path}:{line}: {name}" for name, line in violation.declarations]
    return "\n".join(out)


def area(path: str) -> str:
    """The top-level directory of `Complexity/` that holds `path`."""
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


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--update-baseline", action="store_true",
                        help="rewrite the baseline with the current violations")
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
    if args.update_baseline:
        if over and not args.allow_increase:
            print(over_report(over, found), file=sys.stderr)
            print("\nThe baseline only goes down; pass --allow-increase to raise it on purpose, "
                  "for instance for a moved module or a renamed encoding.", file=sys.stderr)
            return 1
        baseline_path.write_text(baseline_text(current), encoding="utf-8")
        print(f"Wrote {baseline_path}: {status}.")
        return 0
    if over:
        print(over_report(over, found), file=sys.stderr)
    if under:
        print(("\n" if over else "") + "Repeated encodings were named or removed, so the baseline "
              f"is stale. Lower it with `{UPDATE}` and commit the result, so that they cannot "
              "come back:", file=sys.stderr)
        print("\n".join(f"  {path}: `{term}` in {count} public signature(s), baseline {entry}"
                        for path, term, count, entry in under), file=sys.stderr)
    if over or under:
        return 1
    print(f"{status}, matching the baseline.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
