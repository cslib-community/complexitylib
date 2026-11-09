#!/usr/bin/env python3
"""Count handwritten theorem/lemma body lines in the library's Lean sources.

Usage: python3 scripts/proof_lengths.py [--ref REV] [--json OUTPUT] [--top N]

This is a source-layout metric, not proof-term size or elaboration cost. Blank
lines, comments, statements, and the initial "by" are excluded. Term proofs are
included. Proofs inside definitions/instances and generated declarations are not.
The scanner relies on the project's unindented top-level command convention;
unrecognized theorem bodies cause an error rather than being silently omitted.

The command and statement scanner here is shared with the formal-abstract renderer
(`abstract_to_tex.py`) and the hygiene checks.
"""

from __future__ import annotations

import argparse
import bisect
import io
import json
import math
import re
import statistics
import subprocess
import tarfile
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
# Lean.Parser.charLitFnAux/quotedCharCoreFn: one character, or a supported escape.
# Apostrophes inside identifiers are primes, not the start of character literals.
CHAR_LITERAL = re.compile(r"(?<![\w'!?])'(?:\\(?:[\\\"'rnt]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4})|[^\\'])'")
MODIFIERS = r"(?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)\s+)*"
DECL = re.compile(
    r"^(?:@\[[^\]\n]*\]\s*)*" + MODIFIERS + r"(theorem|lemma)\s+(\S+)", re.M
)
COMMAND = re.compile(
    r"^(?:@\[|#|" + MODIFIERS
    + r"(?:theorem|lemma|def|abbrev|opaque|axiom|constant|instance|structure|class|inductive|"
    r"example|namespace|section|end|open|universe|variable|include|omit|attribute|set_option|"
    r"syntax|macro|macro_rules|elab|elab_rules|notation|infixl|infixr|infix|prefix|postfix|"
    r"initialize|builtin_initialize|mutual|export|alias|irreducible_def|add_decl_doc|run_cmd|"
    r"deriving\s+instance)\b)", re.M
)
# `open Foo in`, `set_option … in` and `#guard_msgs in` prefix the command that follows.
COMMAND_PREFIX = re.compile(r"(?<![\w'.!?])in\Z")
# Tokens that decide where a theorem statement ends: brackets, `:=`, binders in the statement
# that take their own `:=`, `match`/`fun` alternatives, a `where` body and equation clauses.
STATEMENT_TOKEN = re.compile(
    r"(?P<open>[([{⟨⦃])|(?P<close>[)\]}⟩⦄])|(?P<assign>:=)|(?P<bar>\|(?![|>]))"
    r"|(?<![\w'.!?])(?:(?P<binder>let|letI|have|haveI)|(?P<alternatives>match|fun(?=\s*\|))"
    r"|(?P<where>where))(?![\w'!?])"
)
# `let x ← e` in `do` notation binds without a `:=` of its own.
DO_BIND = re.compile(r"[^=←\n]*←")
# The last character of a complete term, after which a line starting with `|` may begin
# equation clauses rather than continue the statement (as in `:\n    |x| ≤ 1`).
TERM_END = "_'!?)]}⟩⦄|⊤⊥∅"
# What decides whether such a line is an equation clause (see `_starts_equations`).
CLAUSE_TOKEN = re.compile(r"(?P<open>[([{⟨⦃])|(?P<close>[)\]}⟩⦄])|(?P<arrow>=>)|(?P<assign>:=)")
GROUPS = [
    ("Circuits: frontier", "Computability/Circuit/Frontier/"),
    ("Circuits: Boolean", "Computability/Circuit/Boolean/"),
    ("Circuits: monotone", "Computability/Circuit/Monotone/"),
    ("Circuits: arithmetic", "Computability/Circuit/Arithmetic/"),
    ("Circuits: shared infrastructure", "Computability/Circuit/"),
    ("Machines: universal interpreter", "Computability/Machines/Turing/MultiTape/Universal/"),
    ("Machines: complexity calculus", "Computability/Machines/Turing/MultiTape/Complexity/"),
    ("Machines: other", "Computability/Machines/"),
    ("Cook-Levin", "Computability/Complexity/CookLevin/"),
    ("Complexity classes and reductions", "Computability/Complexity/"),
    ("PCP", "Computability/PCP/"),
    ("Logspace derandomization", "Computability/LogSpaceDerandomization/"),
    ("Boolean analysis", "Foundations/BooleanAnalysis/"),
    ("Expanders", "Foundations/Combinatorics/Expander/"),
    ("Linear algebra", "Foundations/LinearAlgebra/"),
    ("Combinatorics: other", "Foundations/Combinatorics/"),
    ("Shared data structures", "Foundations/Data/"),
    ("Probability foundations", "Foundations/Probability/"),
    ("Probability constructions", "Probability/"),
    ("Propositional logic", "Logics/Propositional/"),
    ("First/second-order logic", "Logics/"),
    ("Decision trees", "Computability/DecisionTree/"),
    ("Communication complexity", "Computability/Communication/"),
    ("Cryptography", "Crypto/"),
]


NORMAL_SPECIAL = re.compile(r"--|/-|['\"]|(?<![\w'!?.])r#*\"")
COMMENT_SPECIAL = re.compile(r"/-|-/")
STRING_SPECIAL = re.compile(r'[\\"]')


def masks(text: str) -> tuple[str, str]:
    """Preserve offsets and newlines while masking nested comments, then string, raw-string
    and character literals."""
    code, syntax = list(text), list(text)
    size = len(text)

    def blank(target: list[str], start: int, end: int) -> None:
        for j in range(start, end):
            if text[j] != "\n":
                target[j] = " "

    depth, quoted, i = 0, False, 0
    while i < size:
        if depth:
            match = COMMENT_SPECIAL.search(text, i)
            if not match:
                break
            blank(code, i, match.end())
            blank(syntax, i, match.end())
            depth += 1 if match[0] == "/-" else -1
            i = match.end()
        elif quoted:
            match = STRING_SPECIAL.search(text, i)
            if not match:
                break
            j = match.start()
            blank(syntax, i, j)
            if text[j] == "\\" and j + 1 < size:
                blank(syntax, j, j + 2)  # Keeps the newline of a string gap.
                i = j + 2
            else:
                syntax[j], quoted, i = " ", text[j] != '"', j + 1
        else:
            match = NORMAL_SPECIAL.search(text, i)
            if not match:
                break
            j = match.start()
            if match[0] == "--":
                end = text.find("\n", j)
                end = size if end < 0 else end
                code[j:end] = syntax[j:end] = [" "] * (end - j)
                i = end
            elif match[0] == "/-":
                code[j:j + 2] = syntax[j:j + 2] = [" ", " "]
                depth, i = 1, j + 2
            elif match[0] == "'":
                literal = CHAR_LITERAL.match(text, j)
                if literal:
                    blank(syntax, j, literal.end())
                i = literal.end() if literal else j + 1
            elif match[0] != '"':
                # A raw string `r#"…"#` ends at the first quote followed by as many hashes.
                close = '"' + match[0][1:-1]
                end = text.find(close, match.end())
                if end < 0:
                    raise ValueError("Unterminated comment or string")
                blank(syntax, j, end + len(close))
                i = end + len(close)
            else:
                syntax[j], quoted, i = " ", True, j + 1
    if depth or quoted:
        raise ValueError("Unterminated comment or string")
    return "".join(code), "".join(syntax)


def command_starts(syntax: str) -> list[int]:
    """Return the offsets of the top-level commands in masked source (see `masks`).

    A command begins at column 0 with a `COMMAND` keyword or attribute. Its attribute and
    modifier prefixes, and `… in` prefix commands, belong to the command they precede. Blank
    lines are not boundaries, and masked docstrings and comments never contain one.
    """
    starts, header_end = [], -1
    for match in COMMAND.finditer(syntax):
        start = match.start()
        if start <= header_end:
            continue
        header_end = start
        while syntax.startswith("@[", header_end):
            depth, header_end = 1, header_end + 2
            while header_end < len(syntax) and depth:
                depth += (syntax[header_end] == "[") - (syntax[header_end] == "]")
                header_end += 1
            while header_end < len(syntax) and syntax[header_end].isspace():
                header_end += 1
        if not starts or not COMMAND_PREFIX.search(syntax[starts[-1]:start].rstrip()):
            starts.append(start)
    return starts


def _starts_equations(statement: str, bar: int) -> bool:
    """Whether a `|` begins equation clauses `| pattern => …` rather than continuing the
    statement, as the absolute value in `Eq\n    |x| |x| := rfl` does.

    The `|` must start its line after a complete term, and its first alternative must reach
    `=>` before any `:=` outside brackets. Mathlib's `|a|` allows no space after the opening
    bar, so a clause-like line whose `|` is not followed by a space is rejected as ambiguous.
    """
    line = statement.rfind("\n", 0, bar) + 1
    before = statement[:line].rstrip()
    if statement[line:bar].strip() or not before or not (
            before[-1].isalnum() or before[-1] in TERM_END):
        return False
    depth = 0
    for token in CLAUSE_TOKEN.finditer(statement, bar + 1):
        if token.lastgroup == "open":
            depth += 1
        elif token.lastgroup == "close":
            depth = max(0, depth - 1)
        elif depth:
            continue
        elif token.lastgroup == "assign":
            return False
        elif statement[bar + 1:bar + 2].isspace():
            return True
        else:
            raise ValueError("Ambiguous `|` starting a statement line: write an absolute value "
                             "inside parentheses, or an equation clause as `| pattern => …`")
    return False


def signature_end(statement: str) -> tuple[int, int]:
    """Return where a theorem's statement ends and its body begins, in masked source.

    The body begins at the first `:=` outside brackets that does not complete a `let`, `letI`,
    `have` or `haveI` in the statement; at a `where` structure-instance body; or at a line that
    begins equation clauses `| pattern => …`. A `let x ← e` in `do` notation has no `:=`, and
    a `|` after `match` or `fun` begins one of its alternatives.
    """
    depth, pending, alternatives = 0, 0, False
    for token in STATEMENT_TOKEN.finditer(statement):
        kind, start = token.lastgroup, token.start()
        if kind == "open":
            depth += 1
        elif kind == "close":
            depth = max(0, depth - 1)
        elif depth:
            continue
        elif kind == "binder":
            pending += not DO_BIND.match(statement, token.end())
        elif kind == "assign":
            if not pending:
                return start, token.end()
            pending -= 1
        elif kind == "alternatives":
            alternatives = True
        elif kind == "where":
            return start, token.end()
        elif kind == "bar" and not (pending or alternatives) and _starts_equations(statement, start):
            return start, start
    raise ValueError("Theorem has neither a top-level := body nor equation clauses")


def scan(text: str, path: str) -> list[dict]:
    code, syntax = masks(text)
    boundaries = command_starts(syntax) + [len(syntax)]
    upstream = re.search(r"^-- upstream: (\S+)", text, re.M)
    status = upstream[1] if upstream else "unmarked"
    relative = path.removeprefix("Complexity/")
    group = next((name for name, prefix in GROUPS if relative.startswith(prefix)), "Other library modules")
    rows = []
    for match in DECL.finditer(syntax):
        start = match.start()
        end = boundaries[bisect.bisect_right(boundaries, match.end())]
        try:
            offset = start + signature_end(syntax[start:end])[1]
        except ValueError as error:
            raise ValueError(f"{match[2]}: {error}") from error
        body = re.sub(r"^\s*by\b", "", code[offset:end], count=1)
        lines = sum(bool(line.strip()) for line in body.splitlines())
        rows.append({
            "file": path, "line": text.count("\n", 0, start) + 1,
            "name": match[2], "kind": match[1], "status": status, "group": group,
            "body_lines": lines,
            "statement_lines": text.count("\n", start, offset) + 1,
        })
    return rows


def summarize(rows: list[dict]) -> dict:
    lengths = sorted(row["body_lines"] for row in rows)
    return {
        "proofs": len(rows), "body_lines": sum(lengths),
        "median": statistics.median(lengths) if lengths else 0,
        "p90": lengths[math.ceil(len(lengths) * .9) - 1] if lengths else 0,
        "max": max(lengths, default=0),
        "at_least_40": sum(n >= 40 for n in lengths),
    }


def self_check() -> None:
    sample = """
/- theorem bogus : True := by trivial /- nested -/ -/
@[simp] public theorem short (n : Nat := 1) : n = n := by
  -- := is not a second body
  rfl
private lemma term : True :=
  True.intro
def excluded : True := by trivial
theorem quoted : ("-- /- :=" = "-- /- :=") := by
  rfl
@[simp]
theorem separate_attribute : True := True.intro
theorem equations : ∀ n : Nat, n = n
  | 0 => rfl
  | n + 1 => rfl
theorem type_let (n : Nat) :
    let k := n + 1
    let j : Nat := k
    j = k := by
  rfl
@[expose] public def annotated : List Nat := []
@[simp] public lemma after_annotated : annotated = [] := rfl
@[expose] def multi_line : List Nat := [0]

lemma after_multi_line : multi_line = [0] := by
  rfl
theorem do_let : some 1 = do
    let n ← some 1
    let m := n
    return m := by
  rfl
theorem absolute (x : Int) :
    |x| ≤ |x| := by
  exact le_rfl
theorem absolute_argument (x : Int) : Eq
    |x| |x| := rfl
theorem or_patterns : ∀ n : Nat, n = n
  | 0 | 1 => rfl
  | _ => rfl
theorem structure_body : Nonempty Nat where
  out := ⟨0⟩
theorem statement_have (i : Fin 3) :
    have := i.isLt
    (⟨i.val, by have := i.isLt; omega⟩ : Fin 3) = i := by
  rfl
set_option maxRecDepth 1000 in
theorem prefixed : True := by
  trivial
universe u
end Sample
"""
    rows = scan(sample, "Complexity/Sample.lean")
    assert [(r["name"], r["body_lines"]) for r in rows] == [
        ("short", 1), ("term", 1), ("quoted", 1), ("separate_attribute", 1), ("equations", 2),
        ("type_let", 1), ("after_annotated", 1), ("after_multi_line", 1), ("do_let", 1),
        ("absolute", 1), ("absolute_argument", 1), ("or_patterns", 2), ("structure_body", 1),
        ("statement_have", 1), ("prefixed", 1)
    ]
    for row in rows[-2:]:
        assert row["name"] in sample.splitlines()[row["line"] - 1]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ref", help="measure a committed revision instead of the working tree")
    parser.add_argument("--json", type=Path, help="write full per-declaration data")
    parser.add_argument("--top", type=int, default=20)
    args = parser.parse_args()
    self_check()
    commit = subprocess.check_output(
        ["git", "rev-parse", "--verify", "--end-of-options", (args.ref or "HEAD") + "^{commit}"],
        cwd=ROOT, text=True,
    ).strip()
    if args.ref:
        archive = subprocess.check_output(["git", "archive", commit, "Complexity"], cwd=ROOT)
        with tarfile.open(fileobj=io.BytesIO(archive)) as source:
            files = [
                (member.name, source.extractfile(member).read().decode())
                for member in source.getmembers()
                if member.isfile() and member.name.endswith(".lean")
            ]
    else:
        files = [
            (str(path.relative_to(ROOT)), path.read_text())
            for path in sorted((ROOT / "Complexity").rglob("*.lean"))
        ]
    rows = []
    for path, text in files:
        try:
            rows.extend(scan(text, path))
        except ValueError as error:
            raise ValueError(f"{path}: {error}") from error
    groups, statuses = defaultdict(list), defaultdict(list)
    for row in rows:
        groups[row["group"]].append(row)
        statuses[row["status"]].append(row)
    report = {
        "head": commit, "source": "committed revision" if args.ref else "working tree",
        "files": len(files), "metric": __doc__,
        "total": summarize(rows),
        "groups": {k: summarize(v) for k, v in sorted(groups.items())},
        "statuses": {k: summarize(v) for k, v in sorted(statuses.items())},
        "declarations": rows,
    }
    if args.json:
        args.json.write_text(json.dumps(report, indent=2) + "\n")
    print(f'{report["source"]}, commit {commit}; {len(files)} source files')
    print("Development\tProofs\tBody lines\tMedian\tP90\tMax\t>=40")
    for name, data in sorted(report["groups"].items(), key=lambda item: -item[1]["body_lines"]):
        print(name, *data.values(), sep="\t")
    print("TOTAL", *report["total"].values(), sep="\t")
    print("\nUpstream status")
    for name, data in report["statuses"].items():
        print(name, *data.values(), sep="\t")
    print("\nLongest theorem bodies")
    for row in sorted(rows, key=lambda r: -r["body_lines"])[:args.top]:
        print(f'{row["body_lines"]:4} {row["file"]}:{row["line"]} {row["name"]}')


if __name__ == "__main__":
    main()
