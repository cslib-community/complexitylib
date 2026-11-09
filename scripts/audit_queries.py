#!/usr/bin/env python3
"""On-demand queries for audits: where declarations are referenced, and duplicate statements.

Usage: python3 scripts/audit_queries.py references [--unused] PREFIX...
       python3 scripts/audit_queries.py duplicates [PREFIX...]
       (either with [--build-dir DIR] [--no-build-check])

PREFIX is a repository-relative source path prefix, such as `CslibFrontier/Computability/Circuit/`.

* `references` lists each public declaration written under the prefixes with the other modules
  that refer to it: library modules and tests. `--unused` keeps only those no other
  module refers to. Declarations with an attribute through which they are used without being
  named (`simp`, `fun_prop`, `aesop`, instances, notation, …) are marked, since such uses leave
  no reference; definitional unfolding by `rfl` or `decide` leaves none either.
* `duplicates` lists groups of declarations in different modules whose statements are
  alpha-equivalent (theorems), or whose types and exposed bodies are (definitions), other than
  deprecated aliases. With prefixes, only groups with a member under one of them.

This is a tool for audits, such as finding a duplicate to delete or checking who uses an API
before changing it. It reads the build outputs through `scripts/lean_outputs.py`, refusing stale
ones unless `--no-build-check` is given. It is never run in CI and prints declarations to look at,
not counts: a declaration nobody refers to may still be wanted API.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import lean_outputs as lo  # noqa: E402
from lean_outputs import ATTR_BLOCK, ATTRIBUTE_COMMAND, COMMAND_START, IDENT  # noqa: E402

# Constants generated from a declaration; a reference to one counts as a reference to its owner.
GENERATED = {
    "eq_def", "eq_unfold", "induct", "induct_unfolding", "mutual_induct", "fun_cases",
    "fun_cases_unfolding", "rec", "recOn", "casesOn", "brecOn", "binductionOn", "below", "ibelow",
    "noConfusion", "noConfusionType", "ctorIdx", "ctorElim", "ctorElimType", "toCtorIdx", "ofNat",
    "ofNat_ctorIdx", "injEq", "inj", "sizeOf_spec", "mk", "congr_simp", "ext", "ext_iff", "elim",
    "proxyType", "proxyTypeEquiv", "decEq", "repr", "go",
}
# Generated constants whose use unfolds the owner's body.
UNFOLDING = {"eq_def", "eq_unfold", "induct", "induct_unfolding", "mutual_induct", "fun_cases",
             "fun_cases_unfolding"}
# Attributes through which a declaration can be used without being named.
IMPLICIT_ATTRS = {
    "simp", "simps", "fun_prop", "aesop", "instance", "ext", "refl", "trans", "symm", "csimp",
    "program_certificate", "fo_realize", "elab_as_elim", "induction_eliminator",
    "cases_eliminator", "default_instance", "coe", "gcongr", "positivity", "norm_num", "bound",
    "grind", "simproc", "congr", "mono", "continuity", "measurability", "app_unexpander",
}
KEYWORD = re.compile(
    r"\b(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|alias|axiom|"
    r"irreducible_def)\b")
NOTATION_COMMAND = re.compile(
    r"^(?:@\[[^\]\n]*\]\s*)?(?:(?:scoped|local)\s+)?"
    r"(?:notation3?|infixl?|infixr|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules)\b",
    re.M)
UNFOLD_TACTIC = re.compile(r"\b(?:unfold|delta|unfold_let)\b(?:\s+[^\s;⟨(\[\],]+)*\s+$")
REWRITE_HEAD = re.compile(
    r"\b(?:simp|simp_all|dsimp|simp_rw|rw|rwa|rewrite|erw|nth_rewrite|nth_rw|simpa|simp_arith|"
    r"field_simp|norm_num|grind|unfold)\b[^\[\]\n]*$")
LIST_ELEMENT = re.compile(r"\s*(?:←|<-)?\s*")


# --- Pure helpers (unit-tested in scripts/test_audit_queries.py) --------------------------------

def owner_of(name: str, owners: dict[str, str]) -> str | None:
    """The user declaration that `name` is, belongs to, or was generated from."""
    if name in owners:
        return owners[name]
    parts = name.split(".")
    for i in range(len(parts) - 1, 0, -1):
        if not (parts[i] in GENERATED or lo.is_internal(parts[i])):
            return None
        prefix = ".".join(parts[:i])
        if prefix in owners:
            return owners[prefix]
    return None


def unfolds_by_name(name: str, owner: str) -> bool:
    """Whether referring to `name` unfolds the body of `owner` (an equation lemma, say)."""
    if name == owner or not name.startswith(owner + "."):
        return False
    first = name[len(owner) + 1:].split(".")[0]
    return first in UNFOLDING or re.fullmatch(r"eq_\d+", first) is not None


def utf16_index(line: str, column: int) -> int:
    """The code-point index of a UTF-16 column, as LSP positions in `.ilean` files count."""
    if line.isascii():
        return column
    units = 0
    for i, char in enumerate(line):
        if units >= column:
            return i
        units += 2 if ord(char) > 0xFFFF else 1
    return len(line)


def unfolds_at(lines: list[str], line: int, index: int) -> bool:
    """Whether the identifier at `lines[line][index]` (masked code) is an argument of `unfold` or
    `delta`, or an element of the lemma list of a rewriting or simplifying tactic."""
    before = lines[line][:index]
    if UNFOLD_TACTIC.search(before):
        return True
    text = "\n".join(lines[max(0, line - 8):line] + [before])
    depth, element = 0, None
    for i in range(len(text) - 1, -1, -1):
        char = text[i]
        if char in ")]}⟩":
            depth += 1
        elif char in "([{⟨":
            if depth:
                depth -= 1
                continue
            if char != "[" or not LIST_ELEMENT.fullmatch(text[i + 1:] if element is None
                                                          else element):
                return False
            return REWRITE_HEAD.search(text[text.rfind("\n", 0, i) + 1:i]) is not None
        elif char == "," and not depth and element is None:
            element = text[i + 1:]
            if not LIST_ELEMENT.fullmatch(element):
                return False
    return False


def split_top_level(text: str) -> list[str]:
    items, depth, start = [], 0, 0
    for i, char in enumerate(text):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif char == "," and not depth:
            items.append(text[start:i])
            start = i + 1
    items.append(text[start:])
    return [item.strip() for item in items if item.strip()]


def attribute_names(attrs: str) -> set[str]:
    """Attribute names in the body of `@[…]` or `attribute […]`, without `local` ones."""
    names = set()
    for item in split_top_level(attrs):
        words = item.split()
        if words[0] == "local":
            continue
        if words[0] == "scoped" and len(words) > 1:
            words = words[1:]
        names.add(words[0].rstrip("!?"))
    return names


def header_info(header: str) -> tuple[str | None, set[str]]:
    """The declaration keyword and attributes in a masked declaration header."""
    attrs = set()
    for block in ATTR_BLOCK.findall(header):
        attrs |= attribute_names(block)
    keywords = KEYWORD.findall(ATTR_BLOCK.sub(" ", header))
    return (keywords[-1] if keywords else None), attrs


def matches(name: str, token: str) -> bool:
    """Whether `token` denotes `name`: the name or one of its suffixes on a component boundary,
    ignoring a private prefix."""
    plain = re.sub(r"^_private\.[^0-9]*\.0\.", "", name)
    return plain == token or plain.endswith("." + token)


def command_spans(code: str, command: re.Pattern) -> list[tuple[int, int, str]]:
    """`(start, end, header)` of each command matching `command`, up to the next command."""
    spans = []
    for match in command.finditer(code):
        end = next((m.start() for m in COMMAND_START.finditer(code, match.end())), len(code))
        spans.append((match.start(), end, match[1] if command.groups else match[0]))
    return spans


# --- Analysis -----------------------------------------------------------------------------------

def annotate_headers(lib: lo.Library, decls: dict[str, dict]) -> None:
    """Declaration keywords and attributes, including `notation` for declarations named in
    notation, macro and syntax commands, whose uses leave no references."""
    for decl in decls.values():
        keyword, attrs = None, set()
        if decl["range"]:
            line, col, _, _, sel_line, sel_col, sel_end_line, sel_end_col = decl["range"]
            src = lib.source(decl["module"])
            keyword, attrs = header_info(src.span(line, col, sel_line, sel_col))
            if keyword is None:  # the selection is the keyword, as for anonymous instances
                keyword, attrs = header_info(src.span(line, col, sel_end_line, sel_end_col))
        decl["keyword"], decl["attrs"] = keyword, attrs
    for decl in decls.values():
        if decl["role"] == "generated" and decl["parent"] in decls:
            decls[decl["parent"]]["attrs"].add("simps")
    by_last: dict[str, list[str]] = defaultdict(list)
    for name in decls:
        by_last[name.rsplit(".", 1)[-1]].append(name)
    for module in lib.modules:
        code = lib.source(module).code
        for start, end, _ in command_spans(code, NOTATION_COMMAND):
            for token in set(IDENT.findall(code, start, end)):
                token = token.rstrip(".")
                for name in by_last.get(token.rsplit(".", 1)[-1], ()):
                    if matches(name, token) and ("." in token or decls[name]["module"] == module):
                        decls[name]["attrs"].add("notation")


def collect_references(lib: lo.Library, decls: dict[str, dict], owners: dict[str, str]) -> None:
    """Record, for each declaration, the other modules that refer to it, its uses inside its own
    module, `attribute […]` commands there, and the library modules that unfold it by name."""
    attribute_spans = {m: [(start, end, attribute_names(attrs)) for start, end, attrs in
                           command_spans(lib.source(m).code, ATTRIBUTE_COMMAND)]
                       for m in lib.modules}
    for module in lib.ileans:
        if module in lo.ROOTS:
            continue
        role = lo.module_role(module)
        for name, _, info in lib.references(module):
            owner = owner_of(name, owners)
            if owner not in decls or not info["usages"]:
                continue
            decl = decls[owner]
            if module != decl["module"]:
                decl[f"{role}_refs"].add(module)
                if role == "lib" and decl["exported"] == "def":
                    src = lib.source(module)
                    if unfolds_by_name(name, owner) or any(
                            unfolds_at(src.lines, u[0], utf16_index(src.raw_lines[u[0]], u[1]))
                            for u in info["usages"]):
                        decl["unfolded_by"].add(module)
                continue
            for usage in info["usages"]:
                if len(usage) == 5:
                    decl["local_uses"] += owner_of(usage[4], owners) != owner
                    continue
                src = lib.source(module)
                offset = src.offset(usage[0], utf16_index(src.raw_lines[usage[0]], usage[1]))
                for start, end, attrs in attribute_spans[module]:
                    if start <= offset < end:
                        decl["attrs"] |= attrs


def classify(decls: dict[str, dict]) -> None:
    """Where each declaration is referenced (`category`), what it is (`sort`), and the attributes
    through which it can be used without being named (`implicit`)."""
    for decl in decls.values():
        if decl["lib_refs"]:
            category = "outside"
        elif decl["test_refs"]:
            category = "tests_only"
        elif decl["local_uses"]:
            category = "module_only"
        else:
            category = "unreferenced"
        keyword = decl["keyword"]
        if "deprecated" in decl["attrs"]:
            sort = "deprecated"
        elif keyword == "alias":
            sort = "alias"
        elif keyword == "instance" or "instance" in decl["attrs"]:
            sort = "instance"
        elif decl["kind"] == "thm":
            sort = "theorem"
        elif decl["kind"] == "induct" or keyword in ("structure", "class", "inductive"):
            sort = "type"
        else:
            sort = "definition"
        decl["category"], decl["sort"] = category, sort
        decl["implicit"] = sorted(decl["attrs"] & (IMPLICIT_ATTRS | {"notation"}))
        if sort == "instance" and "instance" not in decl["attrs"]:
            decl["implicit"].append("instance")


def find_duplicates(lib: lo.Library, decls: dict[str, dict]) -> list[dict]:
    """Groups of declarations, other than deprecated ones and aliases, in different modules."""
    duplicates = []
    for row in lib.duplicate_rows:
        members = [(m, n) for m, n in row["dup"] if n in decls and decls[n]["role"] == "decl"
                   and decls[n]["sort"] not in ("deprecated", "alias")]
        if len({m for m, _ in members}) > 1:
            duplicates.append({"kind": row["k"], "members": sorted(members)})
    return duplicates


# --- Queries ------------------------------------------------------------------------------------

def location(decl: dict) -> str:
    line = decl["range"][0] if decl["range"] else 0
    return f"CslibFrontier/{decl['path']}:{line}"


def under(path: str, prefixes: list[str]) -> bool:
    return not prefixes or path.startswith(tuple(prefixes))


def reference_lines(decls: dict[str, dict], prefixes: list[str], unused: bool) -> list[str]:
    """One line per public declaration under the prefixes: where it is referenced."""
    out = []
    selected = [d for d in decls.values() if d["role"] == "decl"
                and under(f"CslibFrontier/{d['path']}", prefixes)
                and not (unused and d["category"] in ("outside", "tests_only"))]
    for decl in sorted(selected, key=lambda d: (d["path"], d["range"] or [0])):
        users = [f"{label} {', '.join(sorted(decl[key]))}" for label, key in
                 (("library", "lib_refs"), ("tests", "test_refs"))
                 if decl[key]]
        where = "; ".join(users) or ("only its own module" if decl["local_uses"] else "nowhere")
        implicit = f" [used implicitly through {', '.join(decl['implicit'])}?]" \
            if decl["implicit"] else ""
        out.append(f"{location(decl)}: {decl['name']} ({decl['sort']}): {where}{implicit}")
    return out


def duplicate_lines(groups: list[dict], decls: dict[str, dict], prefixes: list[str]) -> list[str]:
    """One block per group of duplicates with a member under the prefixes."""
    out = []
    what = {"thm": "alpha-equivalent statements", "def": "alpha-equivalent types and bodies"}
    for group in groups:
        members = [decls[name] for _, name in group["members"]]
        if not any(under(f"CslibFrontier/{d['path']}", prefixes) for d in members):
            continue
        out.append(f"{what.get(group['kind'], group['kind'])}:")
        out += [f"  {location(d)}: {d['name']}" for d in members]
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("query", choices=("references", "duplicates"))
    parser.add_argument("prefixes", nargs="*", metavar="PREFIX",
                        help="repository-relative source path prefixes")
    parser.add_argument("--unused", action="store_true",
                        help="with `references`, only declarations no other module refers to")
    parser.add_argument("--build-dir", type=Path, default=lo.DEFAULT_BUILD_DIR)
    parser.add_argument("--no-build-check", action="store_true",
                        help="do not check that the build outputs are current")
    args = parser.parse_intermixed_args(argv)
    if args.query == "references" and not args.prefixes:
        parser.error("`references` needs at least one PREFIX")
    if args.unused and args.query != "references":
        parser.error("--unused applies to `references` only")
    lo.check_outputs(args.build_dir, args.no_build_check)
    lib = lo.Library(args.build_dir)
    decls, owners = lo.collect_declarations(lib)
    annotate_headers(lib, decls)
    if args.query == "references":
        collect_references(lib, decls, owners)
    classify(decls)
    lines = (reference_lines(decls, args.prefixes, args.unused) if args.query == "references"
             else duplicate_lines(find_duplicates(lib, decls), decls, args.prefixes))
    print("\n".join(lines) if lines else "No matching declarations.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
