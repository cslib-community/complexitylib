#!/usr/bin/env python3
"""Keep word plumbing out of security experiments and adversary types (#4817).

Usage: python3 scripts/check_experiment_readability.py
           [--base REF | --all | --report | --list [PREFIX]]
           [--update-baseline [--allow-increase]] [--root DIR] [--baseline FILE]

This checks rules 1 and 2 of "Readable security experiments" in CONTRIBUTING.md: an experiment
reads like its textbook figure on typed values, and an adversary is typed, its word encoding
appearing only in a named efficiency predicate such as `A.IsPPT`. It reads the public `def`,
`abbrev`, `instance`, `opaque`, `structure`, `class` and `inductive` declarations of the modules
under `CslibFrontier/Crypto/`, outside `Internal` namespaces and modules and leaving out
declarations marked `@[program_certificate]` or `@[fun_prop]`. It classifies them by type and name:

* an *experiment* returns `Game`, `PMF Bool`, `ProbComp Bool` or an oracle computation of a
  `Bool` (the codomain after the last top-level arrow), and the last word of its name is `Game`,
  `Experiment` or `Hybrid`, possibly extended (`cdhGame`, `treeGameWith`, `cramerShoupGame3Half`),
  or `Exp`, optionally followed by `On`, `Of`, digits, subscripts or primes (`prvIndExp`); or it
  is named `game`, `gameOn` or `experiment`;
* a *reduction* has the same codomain, and the last word of its name is `Adversary`,
  `Distinguisher`, `Forger`, `Inverter`, `Predictor`, `Attacker` or `Reduction`, possibly
  extended, or its name contains `To` before a capital, as in `cdhToDDH`;
* an *adversary type* is a `structure`, `class` or `inductive`, or a `def` or `abbrev` of type
  `Type …` or without a type, named `…Adversary`, `…Distinguisher`, `…Forger`, `…Inverter`,
  `…Predictor` or `…Attacker`, optionally followed by `Of`.

Honest algorithms (`verify`, `test`, `sign`, …) are not checked, whatever they return; this is why
experiments follow the naming convention. In the body of each experiment and reduction (leaving out
tactic blocks, comments and strings, as `scripts/check_projection_chains.py` does) it counts

* `encoding`: each use of a word codec. A codec is one of the generic combinators (`encPair`,
  `encList`, `encOption`, `encSum`, `encFramed`, `encPi`, `encDPi`), or a declaration, structure
  field, `enc_structure` or `enc_inductive` anywhere under `CslibFrontier/`, a section `variable`
  or a binder of the declaration, whose name is shaped like a codec (`enc…` with a capital, digit
  or `_` next, `encode…`, `decode…`, `e` followed by a capital, or containing `Encoding`,
  `Encode` or `Decode`) *and* whose type ends in `↪ List Bool` or `→ List Bool` (for a decoder,
  mentions `List Bool`). Names are matched by their last component, so `F.encode` and
  `F.withSeed.encDesc` count; a binder of the declaration of another type shadows a codec of the
  same name when it is used unqualified;
* `eval`: each `ProbComp.eval…`, `OracleComp.eval…`, `WordOracleComp.eval…` or `evalWith`, except
  where its argument is an experiment (`ProbComp.eval (cdhExperiment …)`: a family game draws the
  setup and then runs the fixed experiment, as rule 3 asks) and where it samples an eager
  random-oracle table inside the argument of `pi` or `PMF.pi`, on the same line;
* `chain`: each positional projection chain such as `.1.2`, read as the projection-chain check
  reads it.

and it counts `word_adversary`: each `List Bool` or `WordOracleComp` in an adversary type, and in
the type of an adversary binder (`A`, `B`, `D`, `adversary`, `adv`, `distinguisher`, `forger`,
`inverter`, `predictor`, `attacker`, optionally followed by digits, subscripts or primes) of an
experiment or reduction, outside applications of efficiency predicates (`IsPPT…`,
`Computable…In…`, `PolyTimeComputable…`, `Refines`).

The reader is syntactic, so the counts are a measure of the debt, not a proof that an experiment
reads well; setup plumbing (rule 3) and the other rules are left to review.

`scripts/experiment_readability_allowlist.txt` lists reviewed exceptions, one per line as
`<module path> <declaration or *> <category>  # reason`, such as a scheme whose own algorithms are
named `encode` and `decode`. The reason is required. An entry suppresses the findings of that
category in that declaration (or, with `*`, in the module); an entry that suppresses nothing in an
enforced module fails, so the list only shrinks. Debt is recorded in the baseline instead.

`scripts/experiment_readability_baseline.json` records the counts of each module that has any, as
`{module path: {category: count}}`, and is ratcheted as `scripts/count_ratchet.py` describes: in a
module that the change touches, a count above its entry fails and a new module's entry is 0; a
count below its entry passes and prints `--update-baseline`, which lowers the entry. Merge groups
and pushes to `main` run `--report`. `--list [PREFIX]` prints every finding under PREFIX (such as
`CslibFrontier/Crypto/Computational/ElGamal`), ignoring the baseline; it is the sweep tool.

The codec vocabulary is read from every module under `CslibFrontier/`, so a new codec elsewhere can
raise the count of a module that uses a name it shares; record such a change with
`--update-baseline --allow-increase` and say why. The check reads only the sources: it needs no
build outputs.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import check_encoding_readability as cer  # noqa: E402
import check_projection_chains as cpc  # noqa: E402
import count_ratchet as ratchet  # noqa: E402
from proof_lengths import masks  # noqa: E402

BASELINE = ROOT / "scripts/experiment_readability_baseline.json"
ALLOWLIST = ROOT / "scripts/experiment_readability_allowlist.txt"
UPDATE = "python3 scripts/check_experiment_readability.py --update-baseline"
RULE = "CONTRIBUTING.md, Readable security experiments"
TREE = "CslibFrontier/Crypto"
CATEGORIES = ("encoding", "eval", "chain", "word_adversary")

EXPERIMENT_NAME = re.compile(r"(?:Game|Experiment|Hybrid)[\w'₀-₉]*$|Exp(?:On|Of|[0-9₀-₉'])*$"
                             r"|^(?:game|gameOn|experiment)$")
ROLES = r"(?:Adversary|Distinguisher|Forger|Inverter|Predictor|Attacker)"
REDUCTION_NAME = re.compile(rf"(?:{ROLES}|Reduction)[\w'₀-₉]*$|To[A-Z]")
ADVERSARY_TYPE_NAME = re.compile(rf"{ROLES}(?:Of)?$")
ADVERSARY_BINDER = re.compile(
    r"(?:A|B|D|adversary|adv|distinguisher|forger|inverter|predictor|attacker)[0-9₀-₉']*$")
EXPERIMENT_TYPE = re.compile(
    r"\(?\s*(?:[\w']+\.)*(?:Game|PMF\s+Bool|ProbComp\s+Bool|(?:Word|Prob)?OracleComp\b.*\bBool)"
    r"\s*\)?", re.S)
WORD = re.compile(r"(?<![\w'.])(?:List\s+Bool|WordOracleComp)(?![\w'!?])")
EVAL = re.compile(r"(?<![\w'!?])(?:[\w']+\.)*(?:ProbComp|OracleComp|WordOracleComp)\.eval[\w']*"
                  r"(?![\w'!?])|(?<![\w'!?])(?:[\w']+\.)*evalWith(?![\w'!?])")
EVAL_HEAD = re.compile(r"(?:\s|\(|<\|)*((?:[^\W\d][\w'!?]*\.)*[^\W\d][\w'!?]*)")
PI = re.compile(r"(?<![\w'!?.])(?:(?:[\w']+\.)*PMF\.)?pi(?![\w'!?])")
NAME_TOKEN = re.compile(r"(?<![\w'!?])(\.)?((?:[^\W\d][\w'!?]*\.)*[^\W\d][\w'!?]*)")
CODEC_NAME = re.compile(
    r"^(?:enc(?:[A-Z0-9_]|$)|encode|decode|e[A-Z][\w'!?]*$)|Encoding$|Encode|Decode")
# Raw-source candidates for the vocabulary: declarations and fields with a codec-shaped name.
_NAME = (r"(?:enc(?:[A-Z0-9_][\w'!?]*)?|(?:en|de)code[\w'!?]*|e[A-Z][\w'!?]*"
         r"|[\w'!?]*(?:Encoding|Encode|Decode)[\w'!?]*)")
DECLARED_CODEC = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]\n]*\][ \t]*)*(?:(?:public|private|protected|noncomputable|scoped|local"
    r"|nonrec|unsafe|partial)[ \t]+)*(def|abbrev|opaque|axiom|instance)[ \t]+(?:[\w'!?]+\.)*("
    + _NAME + r")(?![\w'!?])")
FIELD_CODEC = re.compile(r"^[ \t]+(?:\(\s*)?(" + _NAME + r")\s*:\s*(.*)$")
GENERATED_CODEC = re.compile(r"(?m)^[ \t]*(?:public[ \t]+|private[ \t]+)?"
                             r"enc_(?:structure|inductive)"
                             r"[ \t]+(?:[\w'!?]+\.)*([\w'!?]+)")
BODY_KEYWORDS = {"def", "abbrev", "instance", "opaque"}


@dataclass(frozen=True)
class Finding:
    declaration: str
    line: int
    category: str
    text: str


def is_codec(name: str, type_: str) -> bool:
    """Whether a name and type describe a word codec: a codec-shaped name, and a type ending in
    `↪ List Bool` or `→ List Bool` (for a decoder, mentioning `List Bool`)."""
    type_ = re.sub(r"\s+", " ", type_).strip()
    if not CODEC_NAME.search(name):
        return False
    if re.search(r"(?:↪|→) ?List Bool ?\)?$", type_):
        return True
    return "→" in type_ and "List Bool" in type_ and bool(re.search("decode|Decode", name))


def _top_level(text: str, accept) -> list[int]:
    depth, found = 0, []
    for i, char in enumerate(text):
        if char in "([{⟨⦃":
            depth += 1
        elif char in ")]}⟩⦄":
            depth -= 1
        elif depth == 0 and accept(text, i):
            found.append(i)
    return found


def signature_type(signature: str) -> str:
    """The type of a signature `binders : type`: after its first top-level `:`."""
    colons = _top_level(signature, lambda t, i: t[i] == ":" and t[i:i + 2] != ":="
                        and (i == 0 or t[i - 1] != ":"))
    return signature[colons[0] + 1:].strip() if colons else ""


def codomain(type_: str) -> str:
    arrows = _top_level(type_, lambda t, i: t[i] in "→↪")
    return type_[arrows[-1] + 1:].strip() if arrows else type_.strip()


def binders(signature: str) -> list[tuple[list[str], str]]:
    """The top-level binder groups `(x y : T)`, `{x : T}`, `[x : T]` and `⦃x : T⦄` of a signature,
    before its type, as `(names, type)`."""
    groups, pos = [], 0
    while pos < len(signature):
        char = signature[pos]
        if char in "({⦃[":
            end = cer._skip_brackets(signature, pos)
            group = signature[pos + 1:end - 1].lstrip("{").rstrip("}")
            colon = re.search(r"(?<![:=]):(?![=:])", group)
            if colon and "(" not in group[:colon.start()]:
                groups.append((group[:colon.start()].split(), group[colon.end():]))
            pos = end
        elif char == ":":
            break
        else:
            pos += 1
    return groups


def vocabulary(root: Path) -> frozenset[str]:
    """The last components of the names of the word codecs declared under `CslibFrontier/`."""
    names = set(cer.COMBINATORS)
    for path in sorted((root / "CslibFrontier").rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if "List Bool" not in text and "enc_" not in text:
            continue
        names.update(m[1].split(".")[-1] for m in GENERATED_CODEC.finditer(text))
        names.update(m[1] for line in text.splitlines() if "List Bool" in line
                     for m in FIELD_CODEC.finditer(line) if is_codec(m[1], m[2]))
        if not DECLARED_CODEC.search(text):
            continue
        _, syntax = masks(text)  # only here: masking every file would dominate the run time
        for match in DECLARED_CODEC.finditer(syntax):
            rest = syntax[match.end():]
            signature = rest[:cer._signature_end(rest, match[1])]
            if "List Bool" in signature and is_codec(match[2], signature_type(signature)):
                names.add(match[2])
    return frozenset(names)


def _pi_ranges(text: str) -> list[tuple[int, int]]:
    """The arguments of each `pi`/`PMF.pi`: to the first newline outside brackets, or to the end
    of the enclosing bracket group."""
    ranges = []
    for match in PI.finditer(text):
        depth, end = 0, len(text)
        for i in range(match.end(), len(text)):
            if text[i] in "([{⟨⦃":
                depth += 1
            elif text[i] in ")]}⟩⦄":
                if depth == 0:
                    end = i
                    break
                depth -= 1
            elif text[i] == "\n" and depth == 0:
                end = i
                break
        ranges.append((match.end(), end))
    return ranges


def _efficiency_ranges(text: str) -> list[tuple[int, int]]:
    """The applications of efficiency predicates: to the end of the enclosing bracket group, or to
    the next line indented no deeper than the predicate's line (the next field of a structure)."""
    ranges = []
    for match in cpc.EFFICIENCY.finditer(text):
        end = cpc._group_end(text, match.end())
        line_start = text.rfind("\n", 0, match.start()) + 1
        indent = len(text[line_start:]) - len(text[line_start:].lstrip(" "))
        for line in re.finditer(r"\n( *)(?=\S)", text[match.end():end]):
            if len(line[1]) <= indent:
                end = match.end() + line.start()
                break
        ranges.append((match.start(), end))
    return ranges


def _outside(ranges: list[tuple[int, int]], offset: int) -> bool:
    return not any(start <= offset < end for start, end in ranges)


def _words(text: str) -> list[tuple[int, str]]:
    exempt = _efficiency_ranges(text)
    return [(m.start(), re.sub(r"\s+", " ", m[0])) for m in WORD.finditer(text)
            if _outside(exempt, m.start())]


def module_findings(text: str, vocab: frozenset[str]) -> list[Finding]:
    """The findings of a Lean source file under `CslibFrontier/Crypto/`, in order."""
    found: list[Finding] = []
    codec_variables: dict[str, bool] = {}
    for command in cer.commands(text):
        keyword = command.keyword
        if keyword == "variable":
            for names, type_ in binders(command.text[command.pos:]):
                for name in names:
                    codec_variables[name] = is_codec(name, type_)
            continue
        if keyword not in cer.DECLARATIONS or keyword in ("theorem", "lemma", "axiom"):
            continue
        if not command.public or "Internal" in command.scope.namespace:
            continue
        attributes = {item.split()[0] for group in cpc.ATTRIBUTES.finditer(
            command.text[:command.keyword_start]) for item in group[1].split(",") if item.split()}
        if attributes & cpc.CERTIFICATE_ATTRIBUTES:
            continue
        name, pos, split = command.parts()
        if not name or "Internal" in name.split("."):
            continue
        short = name.split(".")[-1]
        source = command.text

        def emit(offset: int, category: str, token: str) -> None:
            line = command.syntax.count("\n", 0, command.start + offset) + 1
            found.append(Finding(name, line, category, token))

        signature = source[pos:split]
        type_ = signature_type(signature)
        is_type = keyword in cer.TYPE_DECLARATIONS or (
            keyword in ("def", "abbrev") and re.fullmatch(r"(?:Type\S*(?:\s+\S+)?)?", type_))
        if ADVERSARY_TYPE_NAME.search(short) and is_type:
            masked = cpc.mask_tactics(source[pos:])
            for offset, token in _words(masked):
                emit(pos + offset, "word_adversary", token)
            continue
        if (keyword not in BODY_KEYWORDS or not type_
                or not EXPERIMENT_TYPE.fullmatch(codomain(type_))):
            continue
        if not (EXPERIMENT_NAME.search(short) or REDUCTION_NAME.search(short)):
            continue
        local, shadow = {n for n, codec in codec_variables.items()
                         if codec and n in command.scope.variables}, set()
        shadow |= {n for n, codec in codec_variables.items()
                   if not codec and n in command.scope.variables}
        for names, binder_type in binders(signature):
            for binder in names:
                if is_codec(binder, binder_type):
                    local.add(binder)
                    shadow.discard(binder)
                else:
                    shadow.add(binder)
                    local.discard(binder)
                if ADVERSARY_BINDER.fullmatch(binder):
                    start = signature.find(binder_type)
                    for offset, token in _words(binder_type):
                        emit(pos + max(start, 0) + offset, "word_adversary", token)
        body = cpc.mask_tactics(source[split:])
        for match in NAME_TOKEN.finditer(body):
            last = match[2].split(".")[-1]
            qualified = bool(match[1]) or "." in match[2]
            if last in local and not qualified or (
                    last in vocab and (qualified or last not in shadow)):
                emit(split + match.start(2), "encoding", (match[1] or "") + match[2])
        pis = _pi_ranges(body)
        for match in EVAL.finditer(body):
            head = EVAL_HEAD.match(body, match.end())
            if head and EXPERIMENT_NAME.search(head[1].split(".")[-1]):
                continue  # the family form: draw the setup, then run the fixed experiment
            if not _outside(pis, match.start()):
                continue  # an eager random-oracle table
            emit(split + match.start(), "eval", match[0])
        for offset, chain in cpc.chains(body):
            emit(split + offset, "chain", chain)
    return found


@dataclass(frozen=True)
class Entry:
    path: str
    declaration: str  # or "*"
    category: str
    line: int  # in the allowlist


def load_allowlist(path: Path) -> list[Entry]:
    return parse_allowlist(path.read_text(encoding="utf-8"), path) if path.exists() else []


def parse_allowlist(text: str, path: Path) -> list[Entry]:
    entries = []
    for number, raw in enumerate(text.splitlines(), 1):
        content, _, reason = raw.partition("#")
        if not content.strip():
            continue
        parts = content.split()
        if len(parts) != 3 or parts[2] not in CATEGORIES or not reason.strip():
            sys.exit(f"{path}:{number}: expected `<module path> <declaration or *> <category>  "
                     f"# reason`, with a category among {', '.join(CATEGORIES)}")
        entries.append(Entry(parts[0], parts[1], parts[2], number))
    return entries


@dataclass
class Scanner:
    """Scans modules, applying the allowlist and remembering which entries the last scan used."""
    used: set[Entry] = field(default_factory=set)
    entries: list[Entry] = field(default_factory=list)

    def scan(self, root: Path, paths: list[str]) -> dict[str, list[Finding]]:
        self.entries = load_allowlist(root / ALLOWLIST.relative_to(ROOT))
        self.used = set()
        existing = [rel for rel in paths if (root / rel).is_file()]
        if not existing:
            return {}
        vocab = vocabulary(root)
        found = {}
        for rel in existing:
            try:
                rows = module_findings((root / rel).read_text(encoding="utf-8"), vocab)
            except ValueError as error:
                raise ValueError(f"{rel}: {error}") from error
            kept = []
            for row in rows:
                entry = next((e for e in self.entries
                              if (e.path, e.category) == (rel, row.category)
                              and e.declaration in ("*", row.declaration)), None)
                if entry:
                    self.used.add(entry)
                else:
                    kept.append(row)
            if kept:
                found[rel] = kept
        return found

    @staticmethod
    def affected(root: Path, base: str) -> set[str]:
        """The modules of the allowlist entries that the change adds or removes, since removing
        one can raise its module above the baseline without touching the module."""
        relative = ALLOWLIST.relative_to(ROOT)
        old = cer.ccf.git(root, "show", f"{base}:{relative.as_posix()}")
        before = parse_allowlist(old.stdout, relative) if old.returncode == 0 else []
        after = load_allowlist(root / relative)

        def key(entry: Entry) -> tuple[str, str, str]:
            return entry.path, entry.declaration, entry.category

        return {path for path, _, _ in {key(e) for e in before} ^ {key(e) for e in after}}

    def stale(self, root: Path, paths: list[str]) -> list[str]:
        checked = set(paths)
        stale = [e for e in self.entries if e.path in checked and e not in self.used]
        if not stale:
            return []
        return [f"{ALLOWLIST.relative_to(ROOT)} has entries that no longer suppress anything; "
                "remove them:\n" + "\n".join(
                    f"  line {e.line}: {e.path} {e.declaration} {e.category}" for e in stale)]


SCANNER = Scanner()
RATCHET = ratchet.Ratchet(
    description=__doc__, baseline=BASELINE, update=UPDATE, unit="experiment readability finding(s)",
    short="finding(s)",
    intro=("Security experiments read like their textbook figures on typed values, and adversaries "
           "are typed, their encodings appearing only in a named efficiency predicate such as "
           f"`A.IsPPT` (#4817; {RULE}). These modules have more findings than their baseline "
           "entry; the counted findings are:"),
    removed="Experiment readability findings were removed", scan=SCANNER.scan,
    render=lambda row: f"{row.category} `{row.text}`", tree=TREE, categories=CATEGORIES,
    category=lambda row: row.category, extra=SCANNER.stale, affected=SCANNER.affected)


def main(argv: list[str] | None = None) -> int:
    return ratchet.main(RATCHET, argv)


if __name__ == "__main__":
    sys.exit(main())
