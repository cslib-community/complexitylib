#!/usr/bin/env python3
"""Two narrow lints for the Lean files a change adds or modifies.

Usage: python3 scripts/check_changed_files.py [--base REF] [--no-build-check]

Only new or changed files are checked, so an existing file is brought in line when it is next
touched. Changes are taken against the merge base of REF (default `origin/main`) and the working
tree, untracked files included; when there is no merge base, as in CI's shallow checkout, against
REF itself.

1. Module-doc names. In a changed module under `Complexity/`, each backquoted name that heads a
   bullet of a "Main …" section of the module docstring (the names before the bullet's first
   colon) must name a declaration: one that some library, test or abstract module defines or
   refers to, matched exactly or as a suffix on a component boundary. Names of tactics, attributes
   and other syntax that the library declares (`syntax`, `macro`, `elab`,
   `declare_aesop_rule_sets`, `register_simp_attr`) also count, as do the upstream names in
   `UPSTREAM_SYNTAX`. Backquoted text that is not an identifier, such as notation or a pattern
   like `foo_*`, is not checked. Declarations come from the `.ilean` files of `lake build`
   (and `lake test`); stale outputs are refused unless `--no-build-check` is given.
2. Restatement-only tests. A new file under `ComplexityTests/` fails when it has examples and
   every one of them is `example … := name` (or `:= by exact name`) for a name other than `rfl`,
   `trivial` and the like (`EVALUATION`): such a line only restates a signature, which is not a
   test (CONTRIBUTING, review criterion 8). A file that imports or names a curated abstract
   (`ComplexityAbstracts`) is exempt, since restatements pin those.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import lean_outputs as lo  # noqa: E402
from check_hygiene import extract_docstrings  # noqa: E402
from proof_lengths import command_starts, masks, signature_end  # noqa: E402

# Lean's identifiers (`Lean.isIdFirst`, `Lean.isIdRest`), with `«…»` escapes; dot-separated.
_ID_FIRST = ("A-Za-z_α-κμ-ωΑ-ΟΡ-΢Τ-Ω"
             "ϊ-ϻἀ-῾℀-⅏\U0001d49c-\U0001d59f")
_ID_REST = _ID_FIRST + "0-9'!?₀-₉ₐ-ₜᵢ-ᵪⱼ"
_COMPONENT = f"(?:[{_ID_FIRST}][{_ID_REST}]*|«[^»\n]*»)"
NAME = re.compile(rf"{_COMPONENT}(?:\.{_COMPONENT})*")

# Tactic and attribute names from Lean and Mathlib that module docs may list.
UPSTREAM_SYNTAX = {"aesop", "decide", "fun_prop", "gcongr", "grind", "norm_num", "omega",
                   "positivity", "simp"}
# A `syntax`, `macro` or `elab` command whose syntax begins with an atom, such as
# `syntax (name := foo) "fo_simp" … : tactic` or `scoped macro "ppt" : tactic`.
SYNTAX_ATOM = re.compile(
    r"^(?:@\[[^\]\n]*\]\s*)?(?:(?:scoped|local)\s+)?(?:syntax|macro|elab)\b"
    r"(?:\s*\([^()\n]*\))*\s*\"([^\"\n]+)\"", re.M)
RULE_SETS = re.compile(r"^declare_aesop_rule_sets\s*\[([^\]\n]*)\]", re.M)
SIMP_ATTR = re.compile(r"^register_simp_attr\s+(\S+)", re.M)

EXAMPLE = re.compile(r"(?:@\[[^\]\n]*\]\s*)*(?:(?:private|noncomputable)\s+)*example\b")
RESTATEMENT = re.compile(rf"(?:by\s+exact\s+)?@?({NAME.pattern})")
# Bodies that check the statement by evaluation, or prove it outright: concrete tests.
EVALUATION = {"rfl", "Eq.refl", "Iff.rfl", "HEq.rfl", "le_rfl", "trivial", "True.intro"}
ABSTRACTS = re.compile(r"\bComplexityAbstracts\b")


# --- Changed files ------------------------------------------------------------------------------

def git(root: Path, *args: str) -> subprocess.CompletedProcess:
    return subprocess.run(["git", *args], cwd=root, capture_output=True, text=True)


def comparison_base(root: Path, ref: str) -> str:
    """The merge base of `ref` and `HEAD`, or `ref` itself when there is none."""
    resolved = git(root, "rev-parse", "--verify", "--end-of-options", f"{ref}^{{commit}}")
    if resolved.returncode:
        sys.exit(f"cannot resolve the comparison base {ref}: {resolved.stderr.strip()}")
    base = git(root, "merge-base", resolved.stdout.strip(), "HEAD").stdout.strip()
    return base or resolved.stdout.strip()


def changed_files(root: Path, ref: str) -> tuple[list[str], list[str]]:
    """The added and the modified files (repository-relative paths) between the merge base of
    `ref` and `HEAD`, or `ref` itself when there is none, and the working tree."""
    base = comparison_base(root, ref)
    diff = git(root, "diff", "--no-ext-diff", "--no-renames", "--name-status", "-z", base, "--")
    if diff.returncode:
        sys.exit(f"git diff failed: {diff.stderr.strip()}")
    fields = diff.stdout.split("\0")
    added, modified = [], []
    for status, path in zip(fields[0::2], fields[1::2]):
        if status == "A":
            added.append(path)
        elif status in ("M", "T"):
            modified.append(path)
    untracked = git(root, "ls-files", "--others", "--exclude-standard", "-z")
    added += [path for path in untracked.stdout.split("\0") if path]
    return sorted(added), sorted(modified)


# --- Module-doc names ---------------------------------------------------------------------------

MAIN_SECTION = re.compile(r"^##\s+Main\b", re.M)
BULLET = re.compile(r"^(\s*)[*-]\s+")
DOC_NAME = re.compile(r"@?[^\s`()\[\]{},;:]*[A-Za-z][^\s`()\[\]{},;:]*")


def doc_blocks(text: str) -> list[str]:
    """Read complete module docstrings, excluding examples in literals and ordinary comments."""
    return [body for start, body in extract_docstrings(text) if text[start - 3:start] == "/-!"]


def listed_names(doc: str) -> list[str]:
    """Names listed in the "Main …" sections of a module docstring: the backquoted names before
    the first colon (outside backquotes) of each bullet."""
    names = []
    for section in re.split(r"^(?=#)", doc, flags=re.M):
        if not MAIN_SECTION.match(section):
            continue
        items: list[str | None] = []
        for line in section.splitlines()[1:]:
            if BULLET.match(line):
                items.append(BULLET.sub("", line, count=1))
            elif items and items[-1] is not None and line.startswith(" ") and line.strip():
                items[-1] += " " + line.strip()
            else:
                items.append(None)
        for item in filter(None, items):
            head, inside = item, False
            for i, char in enumerate(item):
                if char == "`":
                    inside = not inside
                elif char == ":" and not inside:
                    head = item[:i]
                    break
            names += [token.lstrip("@.") for token in re.findall(r"`([^`]*)`", head)
                      if DOC_NAME.fullmatch(token)]
    return names


def syntax_names(text: str) -> set[str]:
    """Names of the tactics, attributes, rule sets and simp sets a source file declares."""
    names = {atom.strip() for atom in SYNTAX_ATOM.findall(text)}
    for block in RULE_SETS.findall(text):
        names |= {name.strip() for name in block.split(",")}
    names |= set(SIMP_ATTR.findall(text))
    return names - {""}


def known_names(ileans: dict[str, dict]) -> dict[str, set[str]]:
    """Every constant some module defines or refers to, without a private prefix, by its last
    component."""
    names: set[str] = set()
    for ilean in ileans.values():
        names.update(ilean.get("decls", ()))
        for key in ilean["references"]:
            constant = json.loads(key).get("c")
            if constant:
                names.add(constant["n"])
    by_last: dict[str, set[str]] = defaultdict(set)
    for name in names:
        plain = re.sub(r"^_private\..*?\.0\.", "", name)
        by_last[plain.rsplit(".", 1)[-1]].add(plain)
    return by_last


def resolves(token: str, by_last: dict[str, set[str]]) -> bool:
    return any(name == token or name.endswith("." + token)
               for name in by_last.get(token.rsplit(".", 1)[-1], ()))


def listed_identifiers(text: str) -> list[str]:
    """The identifiers listed in the "Main …" sections of a source file's module docstrings."""
    return [token for doc in doc_blocks(text) for token in listed_names(doc)
            if NAME.fullmatch(token)]


def unresolved_doc_names(rel: str, text: str, by_last: dict[str, set[str]],
                         syntax: set[str]) -> list[str]:
    errors = []
    for token in dict.fromkeys(listed_identifiers(text)):
        if token in syntax or token in UPSTREAM_SYNTAX or resolves(token, by_last):
            continue
        offset = max(text.find(f"`{token}`"), text.find(f"`@{token}`"), 0)
        errors.append(f"{rel}:{text.count(chr(10), 0, offset) + 1}: `{token}` is listed in a "
                      "\"Main …\" section of the module docstring but names no declaration")
    return errors


def check_doc_names(root: Path, modules: list[str], load_ileans) -> list[str]:
    """Check the listed names of the given library source files (repository-relative paths)."""
    texts = {rel: (root / rel).read_text(encoding="utf-8") for rel in modules}
    if not any(map(listed_identifiers, texts.values())):
        return []
    by_last = known_names(load_ileans())
    syntax = set().union(*(syntax_names(p.read_text(encoding="utf-8"))
                           for p in sorted((root / "Complexity").rglob("*.lean"))))
    return [error for rel, text in texts.items()
            for error in unresolved_doc_names(rel, text, by_last, syntax)]


# --- Restatement-only tests ---------------------------------------------------------------------

def example_bodies(text: str) -> list[str | None]:
    """The body of each `example` in a source file, after its top-level `:=`, with comments
    and literals masked; `None` for an example written with `where` or equation clauses."""
    syntax = masks(text)[1]
    starts = command_starts(syntax)
    bodies: list[str | None] = []
    for start, end in zip(starts, starts[1:] + [len(syntax)]):
        if not EXAMPLE.match(syntax, start):
            continue
        command = syntax[start:end]
        try:
            stop, body = signature_end(command)
        except ValueError:
            bodies.append(None)
            continue
        bodies.append(command[body:].strip() if command[stop:body] == ":=" else None)
    return bodies


def restatement_only(text: str) -> bool:
    """Whether a test file has examples and each only restates a declaration's signature."""
    if ABSTRACTS.search(masks(text)[0]):
        return False
    matches = [body and RESTATEMENT.fullmatch(body) for body in example_bodies(text)]
    return bool(matches) and all(m and m[1] not in EVALUATION for m in matches)


def check_new_tests(root: Path, added: list[str]) -> list[str]:
    return [f"{rel}: every example only restates a declaration (`example … := name`); test a "
            "concrete instance instead: a small input, a run or a counterexample"
            for rel in added
            if rel.startswith("ComplexityTests/") and rel.endswith(".lean")
            and restatement_only((root / rel).read_text(encoding="utf-8"))]


# --- Driver -------------------------------------------------------------------------------------

def main(argv: list[str] | None = None, root: Path = ROOT) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--base", default="origin/main",
                        help="comparison ref; changes are taken from its merge base with HEAD")
    parser.add_argument("--no-build-check", action="store_true",
                        help="do not check that the build outputs are current")
    args = parser.parse_args(argv)
    added, modified = changed_files(root, args.base)
    modules = [rel for rel in added + modified
               if rel.startswith("Complexity/") and rel.endswith(".lean")]

    def load_ileans() -> dict[str, dict]:
        lo.check_outputs(lo.DEFAULT_BUILD_DIR, args.no_build_check)
        return lo.load_ileans(lo.DEFAULT_BUILD_DIR)

    errors = check_new_tests(root, added) + check_doc_names(root, sorted(modules), load_ileans)
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    if errors:
        return 1
    print(f"Changed-file lints passed ({len(modules)} changed library module(s), "
          f"{sum(rel.startswith('ComplexityTests/') for rel in added)} new test file(s)).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
