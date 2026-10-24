#!/usr/bin/env python3
"""Report review signals for the library's public surface, statements, docs, placement and proofs.

Usage: python3 scripts/quality_report.py [--json OUTPUT] [--markdown OUTPUT] [--top N]
                                         [--build-dir DIR] [--no-build-check]

Reads the build outputs of `lake build Complexity ComplexityTests ComplexityAbstracts` (it refuses
stale outputs unless `--no-build-check` is given) and reports, per area of the quality program
(#587) and per top-level directory:

* where public declarations are referenced: by other library modules, only by tests or
  abstracts, or never outside their own module;
* exposed definition bodies with no evidence of being unfolded by another library module;
* tidy predicates (`ComputableTidily…`) in public statements, outside the machine combinators;
* public definitions, and theorems listed in module docstrings or used by abstracts, without
  docstrings;
* drift between module docstrings' "Main definitions/results" and the public API;
* declarations in different modules with alpha-equivalent statements (or definitions with
  alpha-equivalent types and bodies);
* hub fan-out: transitive importers of each module;
* proof-length outliers, measured by `scripts/proof_lengths.py`.

References come from the `.ilean` files Lake writes beside each `.olean`; they record every
identifier that occurs in the source, including in proofs. Declarations, kinds, export status,
docstrings, statement types and declaration ranges come from the `.olean` parts, read by
`scripts/QualityReport.lean`. These are review signals, not rules: an identifier that is only
used implicitly (simp sets, instances, `fun_prop`, Aesop rules, notation, macros) leaves no
reference, and zero in-repository references does not mean an API is unwanted.
"""

from __future__ import annotations

import argparse
import datetime
import filecmp
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from proof_lengths import masks, scan as scan_proofs  # noqa: E402

ROOTS = ("Complexity", "ComplexityTests", "ComplexityAbstracts")
# Documents outside module docstrings whose backquoted names count as intended API.
EXTERNAL_DOCS = ("README.md", "abstracts/README.md")
# The areas of #587: its table, completed by its assignment of the remaining paths
# (https://github.com/cslib-community/complexitylib/issues/587#issuecomment-6376302681).
AREAS = [
    ("Foundations", "Foundations, Probability, Languages, Computability/BitString",
     ("Foundations/", "Probability/", "Languages/", "Computability/BitString/")),
    ("Machines", "Computability/Machines, Probabilistic, RAM, GenericRAM; Tactic",
     ("Computability/Machines/", "Computability/Probabilistic/", "Computability/RAM/",
      "Computability/GenericRAM/", "Tactic/")),
    ("Classes", "Computability/Complexity, PCP, Communication, DecisionTree, QueryComplexity, "
     "TreeEval, Kolmogorov, MCSP, USTCON, Languages; MachineLearning",
     ("Computability/Complexity/", "Computability/PCP/", "Computability/Communication/",
      "Computability/DecisionTree/", "Computability/QueryComplexity/", "Computability/TreeEval/",
      "Computability/Kolmogorov/", "Computability/MCSP/", "Computability/USTCON/",
      "Computability/Languages/", "MachineLearning/")),
    ("Circuit", "Computability/Circuit, BranchingProgram",
     ("Computability/Circuit/", "Computability/BranchingProgram/")),
    ("Crypto", "Crypto", ("Crypto/",)),
    ("Logics", "Logics", ("Logics/",)),
    ("WordRAM", "Computability/WordRAM, Algorithms", ("Computability/WordRAM/", "Algorithms/")),
]
OTHER_AREA = "Other"  # `Init.lean`, held jointly by the program leads, and unassigned paths
TIDY_EXEMPT = "Computability/Machines/Turing/MultiTape/Combinators/"

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
DEFINITION_KEYWORDS = {"def", "abbrev", "structure", "class", "inductive", "opaque",
                       "irreducible_def"}
KEYWORD = re.compile(
    r"\b(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|alias|axiom|"
    r"irreducible_def)\b")
ATTR_BLOCK = re.compile(r"@\[((?:[^\[\]]|\[(?:[^\[\]]|\[[^\[\]]*\])*\])*)\]")
ATTRIBUTE_COMMAND = re.compile(
    r"^attribute\s*\[((?:[^\[\]]|\[(?:[^\[\]]|\[[^\[\]]*\])*\])*)\]", re.M)
NOTATION_COMMAND = re.compile(
    r"^(?:@\[[^\]\n]*\]\s*)?(?:(?:scoped|local)\s+)?"
    r"(?:notation3?|infixl?|infixr|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules)\b",
    re.M)
COMMAND_START = re.compile(
    r"^(?:@\[|/--|/-!|#|(?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec|"
    r"scoped|local|meta)\s+)*(?:theorem|lemma|def|abbrev|opaque|axiom|instance|structure|class|"
    r"inductive|example|namespace|section|end|open|universe|variable|include|omit|attribute|"
    r"set_option|syntax|macro|macro_rules|elab|elab_rules|notation|notation3|infixl|infixr|infix|"
    r"prefix|postfix|initialize|mutual|export|alias|register_simp_attr|declare_aesop_rule_sets|"
    r"add_decl_doc|deriving)\b)", re.M)
IDENT = re.compile(r"[A-Za-z_À-ɏͰ-Ͽᴀ-ᶿ℀-⅏]"
                   r"[\w'!?₀-ₜᵢ-ᵪ.]*")
UNFOLD_TACTIC = re.compile(r"\b(?:unfold|delta|unfold_let)\b(?:\s+[^\s;⟨(\[\],]+)*\s+$")
REWRITE_HEAD = re.compile(
    r"\b(?:simp|simp_all|dsimp|simp_rw|rw|rwa|rewrite|erw|nth_rewrite|nth_rw|simpa|simp_arith|"
    r"field_simp|norm_num|grind|unfold)\b[^\[\]\n]*$")
LIST_ELEMENT = re.compile(r"\s*(?:←|<-)?\s*")
MAIN_SECTION = re.compile(r"^##\s+Main\b", re.M)
BULLET = re.compile(r"^(\s*)[*-]\s+")
DOC_NAME = re.compile(r"@?[^\s`()\[\]{},;:]*[A-Za-z][^\s`()\[\]{},;:]*")


# --- Pure helpers (unit-tested in scripts/test_quality_report.py) -------------------------------

def area_of(path: str) -> str:
    """The #587 area of a library source path relative to `Complexity/`."""
    for name, _, prefixes in AREAS:
        if path.startswith(prefixes):
            return name
    return OTHER_AREA


def top_dir(path: str) -> str:
    return path.split("/", 1)[0] if "/" in path else "(root)"


def module_role(module: str) -> str:
    """`lib`, `test` or `abstract` for a module of one of the three libraries."""
    if module.startswith("ComplexityAbstracts.") or module.startswith("ComplexityTests.Abstracts."):
        return "abstract"
    if module.startswith("ComplexityTests."):
        return "test"
    return "lib"


def source_path(module: str) -> Path:
    rel = module.replace(".", "/") + ".lean"
    return ROOT / ("abstracts/" + rel if module.startswith("ComplexityAbstracts") else rel)


def is_internal(component: str) -> bool:
    return (component.startswith("_") or component.isdigit()
            or re.fullmatch(r"(?:eq|match|proof|omega)_[\d_]+", component) is not None)


def owner_of(name: str, owners: dict[str, str]) -> str | None:
    """The user declaration that `name` is, belongs to, or was generated from."""
    if name in owners:
        return owners[name]
    parts = name.split(".")
    for i in range(len(parts) - 1, 0, -1):
        if not (parts[i] in GENERATED or is_internal(parts[i])):
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


def doc_blocks(text: str) -> list[str]:
    return re.findall(r"/-!(.*?)-/", text, re.S)


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


def doc_named(names: list[str], tokens: set[str]) -> set[str]:
    """The names that some documentation token could denote: the token is the name or one of its
    suffixes on a component boundary. An ambiguous token, such as a short name, protects every
    declaration it could denote."""
    by_last: dict[str, list[str]] = defaultdict(list)
    for name in names:
        by_last[name.rsplit(".", 1)[-1]].append(name)
    return {name for token in tokens for name in by_last.get(token.rsplit(".", 1)[-1], ())
            if matches(name, token)}


def doc_tokens(text: str) -> set[str]:
    """The backquoted tokens of a docstring or Markdown text."""
    return {t.lstrip("@.") for t in re.findall(r"`([^`\s]+)`", text)} - {""}


def mentioned(doc_tokens: set[str], name: str) -> bool:
    return any(name == t or name.endswith("." + t) for t in doc_tokens)


def matches(name: str, token: str) -> bool:
    plain = re.sub(r"^_private\.[^0-9]*\.0\.", "", name)
    return plain == token or plain.endswith("." + token)


def rebuild_fanout(imports: dict[str, list[tuple[str, bool]]]) -> dict[str, set[str]]:
    """Modules that Lake rebuilds when a module's exported interface changes.

    `imports[m]` lists `(dependency, is_public)` pairs. A module depends on the exported `.olean`
    of each direct import and of everything those reexport through chains of `public import`s;
    it does not depend on what they import privately."""
    reexporters: dict[str, set[str]] = defaultdict(set)
    importers: dict[str, set[str]] = defaultdict(set)
    for module, deps in imports.items():
        for dep, public in deps:
            importers[dep].add(module)
            if public:
                reexporters[dep].add(module)
    result = {}
    for module in imports:
        seen, stack = {module}, [module]
        while stack:
            for parent in reexporters[stack.pop()]:
                if parent not in seen:
                    seen.add(parent)
                    stack.append(parent)
        result[module] = set().union(*(importers[m] for m in seen)) - {module}
    return result


def transitive_importers(imports: dict[str, list[tuple[str, bool]]]) -> dict[str, set[str]]:
    importers: dict[str, set[str]] = defaultdict(set)
    for module, deps in imports.items():
        for dep, _ in deps:
            importers[dep].add(module)
    result = {}
    for module in imports:
        seen, stack = set(), [module]
        while stack:
            for importer in importers[stack.pop()]:
                if importer not in seen:
                    seen.add(importer)
                    stack.append(importer)
        result[module] = seen
    return result


# --- Data loading -------------------------------------------------------------------------------

def run(cmd: list[str], **kwargs) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=ROOT, text=True, check=True, **kwargs)


DEFAULT_BUILD_DIR = ROOT / ".lake/build/lib/lean"
# The build outputs the report reads.
REPORT_INPUTS = (".ilean", ".olean", ".olean.server", ".olean.private")


def lake_outputs_current() -> bool:
    """Whether Lake finds the default build outputs of the three libraries current."""
    return subprocess.run(["lake", "build", "--no-build", *ROOTS], cwd=ROOT,
                          capture_output=True).returncode == 0


def output_differences(build_dir: Path, reference: Path) -> list[str]:
    """Report inputs that are missing, extra or different in `build_dir` compared to
    `reference`, as paths relative to them."""
    def inputs(directory: Path) -> set[Path]:
        # The roots' own outputs (`Complexity.ilean`, …) sit beside their directories, and the
        # report takes its module inventory from their imports.
        files = [p for root in ROOTS
                 for p in [*(directory / root).rglob("*"), *directory.glob(f"{root}.*")]]
        return {p.relative_to(directory) for p in files
                if p.name.endswith(REPORT_INPUTS) and p.is_file()}
    ours, theirs = inputs(build_dir), inputs(reference)
    changed = {p for p in ours & theirs
               if not filecmp.cmp(build_dir / p, reference / p, shallow=False)}
    return sorted(map(str, (ours ^ theirs) | changed))


def check_outputs(build_dir: Path, skip: bool, current=lake_outputs_current,
                  reference: Path = DEFAULT_BUILD_DIR) -> str:
    """How the build outputs were checked, or exit when they are not current.

    Lake checks only the default build directory, so another directory must hold exactly the
    same report inputs as the checked default outputs."""
    if skip:
        return "not checked against the sources"
    if not current():
        sys.exit("build outputs are missing or stale; run `lake build " + " ".join(ROOTS)
                 + "` (or pass --no-build-check)")
    if build_dir.resolve() == reference.resolve():
        return "checked current by `lake build --no-build`"
    differences = output_differences(build_dir, reference)
    if differences:
        sys.exit(f"{build_dir} differs from the current build outputs in {len(differences)} "
                 f"file(s) (e.g. {', '.join(differences[:3])}); pass --no-build-check to "
                 "report on it anyway")
    return "checked identical to the current outputs of `lake build --no-build`"


ROOT_IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(\S+)", re.M)


def listed_modules(text: str) -> list[str]:
    """The modules a root source file imports."""
    return ROOT_IMPORT.findall(text)


def load_ileans(build_dir: Path, missing: list[str] | None = None) -> dict[str, dict]:
    """The `.ilean` data of the modules the three libraries' roots import, by module name.

    A long-lived build directory keeps the outputs of modules that were since deleted or moved,
    and `lake build --no-build` does not notice them, so modules are found by following imports
    from the roots rather than by listing files. Every root and every module they import must have
    one; a missing file means the build is incomplete. The roots themselves are left out.

    Given a list `missing`, the build may be partial instead (for a tree that does not build
    completely): the modules are those the roots' source files import, and the ones without an
    `.ilean` file are appended to `missing`."""
    if missing is not None:
        ileans = {}
        for root in ROOTS:
            for module in listed_modules(source_path(root).read_text()):
                path = build_dir / (module.replace(".", "/") + ".ilean")
                if path.is_file():
                    ileans[module] = json.loads(path.read_text())
                else:
                    missing.append(module)
        return ileans
    ileans, todo = {}, [(root, None) for root in ROOTS]
    while todo:
        module, importer = todo.pop()
        if module in ileans:
            continue
        path = build_dir / (module.replace(".", "/") + ".ilean")
        if not path.is_file():
            sys.exit(f"{path} is missing ({'imported by ' + importer if importer else 'a root'}); "
                     "run `lake build " + " ".join(ROOTS) + "` first")
        ileans[module] = json.loads(path.read_text())
        todo.extend((i[0], module) for i in ileans[module]["directImports"]
                    if i[0].split(".")[0] in ROOTS)
    for root in ROOTS:
        del ileans[root]
    return ileans


def load_constants(build_dir: Path, modules: list[str], pairs: str | None = None
                   ) -> tuple[dict[str, dict], list[dict]]:
    """Constants of `modules`; `pairs` (`tidy=plain,…`) adds the fields that
    `scripts/tidy_sweep.py` reads (see `scripts/QualityReport.lean`)."""
    out = run(["lake", "env", "lean", "--run", "scripts/QualityReport.lean", str(build_dir)]
              + ([pairs] if pairs else []),
              input="\n".join(modules) + "\n", capture_output=True).stdout
    constants, duplicates = {}, []
    for line in out.splitlines():
        row = json.loads(line)
        if "dup" in row:
            duplicates.append(row)
        else:
            constants[row["n"]] = row
    return constants, duplicates


class Source:
    """A source file with its masked code split into lines."""

    def __init__(self, path: Path):
        self.text = path.read_text(encoding="utf-8")
        self.code = masks(self.text)[0]
        self.raw_lines = self.text.split("\n")
        self.lines = self.code.split("\n")
        self.starts = [0]
        for raw in self.raw_lines:
            self.starts.append(self.starts[-1] + len(raw) + 1)

    def span(self, line: int, col: int, end_line: int, end_col: int) -> str:
        """Masked code between 1-based lines and code-point columns."""
        if line == end_line:
            return self.lines[line - 1][col:end_col]
        return "\n".join([self.lines[line - 1][col:]] + self.lines[line:end_line - 1]
                         + [self.lines[end_line - 1][:end_col]])

    def offset(self, line0: int, index: int) -> int:
        return self.starts[line0] + index


# --- Analysis -----------------------------------------------------------------------------------

class Library:
    """Build outputs and sources of the three libraries, loaded lazily where possible."""

    def __init__(self, build_dir: Path, pairs: str | None = None,
                 missing: list[str] | None = None):
        self.build_dir = build_dir
        self.ileans = load_ileans(build_dir, missing)
        self.modules = sorted(m for m in self.ileans if m.startswith("Complexity."))
        self.constants, self.duplicate_rows = load_constants(build_dir, self.modules, pairs)
        self.sources: dict[str, Source] = {}

    def source(self, module: str) -> Source:
        if module not in self.sources:
            self.sources[module] = Source(source_path(module))
        return self.sources[module]

    def references(self, module: str):
        """`(name, defining module, info)` for each constant referenced in `module`."""
        for key, info in self.ileans[module]["references"].items():
            ident = json.loads(key).get("c")
            if ident:
                yield ident["n"], ident["m"], info


def collect_declarations(lib: Library) -> tuple[dict[str, dict], dict[str, str], Counter]:
    """Public declarations written in library sources (the binders recorded in `.ilean` files),
    and the owner of every such name: a structure for its fields and constructors, a definition
    for the lemmas `@[simps]` generates, and the declaration itself otherwise."""
    decls: dict[str, dict] = {}
    owners: dict[str, str] = {}
    private_count: Counter = Counter()
    for module in lib.modules:
        rel = module.removeprefix("Complexity.").replace(".", "/") + ".lean"
        for name, defined_in, info in lib.references(module):
            if defined_in != module or not info["definition"]:
                continue
            if name.startswith("_private."):
                private_count[module] += 1
                owners[name] = name
                continue
            const = lib.constants.get(name)
            if not const or not const["e"]:
                continue
            parent = info["definition"][4] if len(info["definition"]) == 5 else None
            role = "decl"
            if const["k"] == "ctor":
                role = "member"
            elif parent and parent != name:
                if not name.startswith(parent + "."):
                    role = "generated"
                elif lib.constants.get(parent, {}).get("k") == "induct":
                    role = "member"
            decls[name] = {
                "name": name, "module": module, "path": rel, "area": area_of(rel[:-5] + "/"),
                "role": role, "kind": const["k"], "exported": const["e"], "doc": const["doc"],
                "tidy": const["tidy"], "range": const["r"], "parent": parent,
                "lib_refs": set(), "test_refs": set(), "abstract_refs": set(), "local_uses": 0,
                "unfolded_by": set(),
            }
    for name, decl in decls.items():
        owned = decl["role"] != "decl" and decl["parent"] in decls
        owners[name] = decl["parent"] if owned else name
    return decls, owners, private_count


def command_spans(code: str, command: re.Pattern) -> list[tuple[int, int, str]]:
    """`(start, end, header)` of each command matching `command`, up to the next command."""
    spans = []
    for match in command.finditer(code):
        end = next((m.start() for m in COMMAND_START.finditer(code, match.end())), len(code))
        spans.append((match.start(), end, match[1] if command.groups else match[0]))
    return spans


# Report-only S4 measurement. These prefixes describe the proposed target, not an exemption
# from S3 or an assertion that the boundary migration has already happened.
TIDY_INTERNAL_PREFIXES = (
    "Complexity/Computability/Machines/Turing/MultiTape/Internal/",
    "ComplexityTests/Machines/Turing/MultiTape/Internal/",
)
BRIDGE_TOKEN = re.compile(r"\.(?:tidy|of_tidy)(?![\w'!?])")
LOCAL_FUN_PROP = re.compile(r"(?:^|,)\s*local\s+fun_prop\s*(?:,|$)")


def tidy_source_signals(text: str, tidy_names: set[str], known_names: set[str] | None = None
                        ) -> dict:
    """Lexical bridge occurrences and local registrations of known tidy-typed constants.

    Reuse the comment/string/character masks and attribute parser. Name suffix matching is
    conservative: an ambiguous suffix counts if any candidate has a tidy type. Unresolved
    local registrations are retained for review, not silently called plain. This does not
    expand macros, resolve local notation, or count semantic pairs of bridge applications.
    """
    code = masks(text)[1]
    bridges = [{"line": code.count("\n", 0, m.start()) + 1,
                "bridge": m[0][1:]} for m in BRIDGE_TOKEN.finditer(code)]
    local, unresolved = [], []
    blocks = [(m, False) for m in ATTR_BLOCK.finditer(code)]
    blocks += [(m, True) for m in ATTRIBUTE_COMMAND.finditer(code)]
    for block, command in sorted(blocks, key=lambda x: x[0].start()):
        if not LOCAL_FUN_PROP.search(block[1]):
            continue
        after = code[block.end():]
        # An attribute command names one or more targets; an inline attribute precedes a decl.
        if command:
            following = next(COMMAND_START.finditer(code, block.end()), None)
            target_text = code[block.end():following.start() if following else len(code)]
            targets = IDENT.findall(target_text)
            targets = targets[:targets.index("in")] if "in" in targets else targets
        else:
            decl = re.match(r"\s*(?:(?:public|private|protected|noncomputable|unsafe|partial|"
                            r"nonrec|meta)\s+)*(?:theorem|lemma|def|abbrev|instance|opaque)\s+",
                            after)
            target = IDENT.match(after, decl.end()) if decl else None
            targets = [target[0]] if target else []
        line = code.count("\n", 0, block.start()) + 1
        if not targets:
            unresolved.append({"line": line, "target": None})
        for target in targets:
            row = {"line": line, "target": target}
            candidates = [n for n in tidy_names if n == target or n.endswith("." + target)]
            if candidates:
                local.append({**row, "candidates": sorted(candidates)})
            elif target not in (known_names or set()):
                unresolved.append(row)
    return {"bridges": bridges, "local_tidy_fun_prop": local,
            "unresolved_local_fun_prop": unresolved}


def private_tidy_declarations(constants: dict[str, dict], source) -> dict[str, list[dict]]:
    """Private source declarations with tidy in their type, excluding generated children."""
    found: dict[str, list[dict]] = defaultdict(list)
    for name, c in constants.items():
        if not (name.startswith("_private.") and c["tidy"] and c["r"]):
            continue
        r = c["r"]
        selected = source(c["m"]).span(*r[4:]).strip()
        if selected and name.endswith("." + selected):
            found[c["m"]].append({"name": name, "line": r[4], "mentions": c["tidy"]})
    return found


def tidy_usage_report(lib: Library, prefixes: tuple[str, ...] = TIDY_INTERNAL_PREFIXES) -> dict:
    """Per-module report of the S4 boundary, with no baseline comparison or enforcement.

    Public statement counts use exactly S3's source-declaration/type rule. Private counts
    require a source declaration range and a tidy constant in its elaborated type; generated
    constants sharing the owner's range are excluded by matching the selected source name.
    Tests/abstracts use their own metadata. Guide files have source-only signals and explicitly
    unknown statement counts, since the root build does not elaborate the separate guide.
    """
    modules = sorted(m for m in lib.ileans if m.startswith(
        ("Complexity.", "ComplexityTests.", "ComplexityAbstracts.")))
    extra = [m for m in modules if m not in lib.modules]
    constants = dict(lib.constants)
    if extra:
        more, _ = load_constants(lib.build_dir, extra)
        constants.update(more)
    tidy_names = {n for n, c in constants.items() if c["tidy"]}
    # Known suffixes distinguish resolved plain targets from unknown ones without rescanning
    # the entire constant inventory for every source attribute.
    known_suffixes = {".".join(parts[i:]) for n in constants
                      for parts in [n.split(".")] for i in range(len(parts))}
    public_tidy_names = {n for n in tidy_names if not n.startswith("_private.")}
    private_tidy_names: dict[str, set[str]] = defaultdict(set)
    for n in tidy_names - public_tidy_names:
        private_tidy_names[constants[n]["m"]].add(n)
    public, _, _ = collect_declarations(lib)
    public_by_module = Counter(d["module"] for n, d in public.items()
                               if d["role"] != "generated" and
                               (constants[n]["tidy"] or constants[n].get("tb")))
    private_by_module = private_tidy_declarations(constants, lib.source)
    rows = []
    sources = [(m, source_path(m), True) for m in modules]
    sources += [(str(p.relative_to(ROOT)), p, False) for p in sorted(
        (ROOT / "guide").rglob("*.lean")) if ".lake" not in p.parts]
    for module, path, metadata in sources:
        rel = path.relative_to(ROOT).as_posix()
        if any(rel.startswith(p) for p in prefixes):
            continue
        text = path.read_text()
        signals = tidy_source_signals(text,
                                      public_tidy_names | private_tidy_names[module],
                                      known_suffixes)
        private = private_by_module[module] if metadata else None
        counts = {"public_tidy_statements": public_by_module[module]
                  if module.startswith("Complexity.") else None,
                  "private_tidy_declarations": len(private) if metadata else None,
                  "local_tidy_fun_prop": len(signals["local_tidy_fun_prop"]),
                  "bridge_occurrences": len(signals["bridges"])}
        rows.append({"module": module, "path": rel,
                     "role": module_role(module) if metadata else "guide", "counts": counts,
                     "mentions_tidy": bool(re.search(r"Tidily|IsTidy|\.(?:of_)?tidy\b",
                                                       masks(text)[1])),
                     "private_tidy_declarations": private, **signals})
    keys = ("public_tidy_statements", "private_tidy_declarations",
            "local_tidy_fun_prop", "bridge_occurrences")
    source_hash = hashlib.sha256()
    for path in [source_path(root) for root in ROOTS] + [p for _, p, _ in sources]:
        source_hash.update(path.relative_to(ROOT).as_posix().encode() + b"\0")
        source_hash.update(path.read_bytes() + b"\0")
    provenance = {"revision": run(["git", "rev-parse", "HEAD"], capture_output=True).stdout.strip(),
                  "tree": run(["git", "rev-parse", "HEAD^{tree}"], capture_output=True).stdout.strip(),
                  "dirty": bool(run(["git", "status", "--porcelain"],
                                    capture_output=True).stdout.strip()),
                  "source_dirty": bool(run(["git", "status", "--porcelain", "--",
                      "Complexity", "ComplexityTests", "abstracts", "guide",
                      "Complexity.lean", "ComplexityTests.lean"],
                      capture_output=True).stdout.strip()),
                  "scanned_source_sha256": source_hash.hexdigest(),
                  "scanned_files": len(sources), "build_dir": str(lib.build_dir)}
    return {"provenance": provenance, "internal_prefixes": list(prefixes), "report_only": True,
            "totals": {k: sum(r["counts"][k] or 0 for r in rows) for k in keys},
            "files_mentioning_tidy": sum(r["mentions_tidy"] for r in rows),
            "modules": rows,
            "notes": ["The prefixes are a proposed measurement boundary, not S3 exemptions.",
                "Public counts use S3's declaration/type rule only for library modules, but "
                "this report's stated boundary replaces S3's allowlist. Null is not zero.",
                "Private counts inspect elaborated types, not names or proof bodies; generated "
                "constants are excluded by source selection. Type aliases are not unfolded. "
                "Guide metadata is unavailable.",
                "Bridge counts are lexical occurrences, not semantic round-trip pairs; comments "
                "and literals are masked. Other named erasure APIs are not included.",
                "Local registration targets use conservative suffix matching, without elaborated "
                "name resolution; unresolved targets are listed, not assumed plain."]}


def tidy_usage_markdown(report: dict, top: int = 20) -> str:
    """Human view of the same report-only per-module data, with full detail in JSON."""
    out = ["### Proof-internal tidy usage (S4, report only)", "",
           "Measurement excludes: " + ", ".join(f"`{p}`" for p in report["internal_prefixes"]),
           "", "| Module | Public tidy statements | Private tidy declarations | Local tidy "
           "fun_prop targets | Bridge occurrences |", "|---|---:|---:|---:|---:|"]
    rows = sorted(report["modules"], key=lambda r: (
        -sum(v or 0 for v in r["counts"].values()), r["path"]))
    for row in [r for r in rows if any(r["counts"].values())][:top]:
        values = ["unknown" if v is None else str(v) for v in row["counts"].values()]
        out.append(f"| `{row['path']}` | " + " | ".join(values) + " |")
    out += ["| Total (known counts) | " + " | ".join(map(str, report["totals"].values())) + " |",
            "", f"{report['files_mentioning_tidy']} files mention tidy outside the measurement "
            "boundary. Full per-module locations and unresolved targets are in the JSON report.",
            "", *["- " + note for note in report["notes"]]]
    return "\n".join(out) + "\n"


def annotate_headers(lib: Library, decls: dict[str, dict]) -> None:
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


def collect_references(lib: Library, decls: dict[str, dict], owners: dict[str, str]) -> None:
    """Record, for each declaration, the other modules that refer to it, its uses inside its own
    module, `attribute […]` commands there, and the library modules that unfold it by name."""
    attribute_spans = {m: [(start, end, attribute_names(attrs)) for start, end, attrs in
                           command_spans(lib.source(m).code, ATTRIBUTE_COMMAND)]
                       for m in lib.modules}
    for module in lib.ileans:
        if module in ROOTS:
            continue
        role = module_role(module)
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


def check_module_docs(lib: Library, decls: dict[str, dict], owners: dict[str, str]) -> dict:
    """Compare each module docstring's "Main …" lists with the module's declarations, and mark
    declarations named in module docstrings or the README files."""
    names_by_module: dict[str, list[str]] = defaultdict(list)
    for name in owners:
        if name.startswith("_private."):
            names_by_module[name.removeprefix("_private.").split(".0.", 1)[0]].append(name)
    for name, decl in decls.items():
        names_by_module[decl["module"]].append(name)
    by_last: dict[str, list[str]] = defaultdict(list)
    for name in decls:
        by_last[name.rsplit(".", 1)[-1]].append(name)
    const_by_last: dict[str, list[str]] = defaultdict(list)
    for name in lib.constants:
        const_by_last[name.rsplit(".", 1)[-1]].append(name)
    all_tokens = set().union(*(doc_tokens((ROOT / path).read_text()) for path in EXTERNAL_DOCS))
    drift_by_module = {}
    for module in lib.modules:
        docs = doc_blocks(lib.source(module).text)
        tokens = set().union(*map(doc_tokens, docs))
        all_tokens |= tokens
        in_module = names_by_module[module]
        upstream = [name for name, defined_in, _ in lib.references(module)
                    if not defined_in.startswith("Complexity")]
        listed = [name for doc in docs for name in listed_names(doc)]
        drift = {"listed": len(listed), "missing": [], "private": [], "elsewhere": [],
                 "unlisted": [], "has_main": any(MAIN_SECTION.search(d) for d in docs)}
        for token in listed:
            last = token.rsplit(".", 1)[-1]
            here = [n for n in in_module if matches(n, token)]
            if any(not n.startswith("_private.") for n in here):
                for name in here:
                    if name in decls:
                        decls[name]["listed"] = True
            elif here:
                drift["private"].append(token)
            elif any(matches(n, token) for n in by_last.get(last, ())):
                drift["elsewhere"].append(token)
            elif not any(matches(n, token) for n in upstream + const_by_last.get(last, [])):
                drift["missing"].append(token)
        for name in in_module:
            decl = decls.get(name)
            if decl is None:
                continue
            if (decl["role"] == "decl" and decl["keyword"] in DEFINITION_KEYWORDS
                    and "deprecated" not in decl["attrs"] and not mentioned(tokens, name)):
                drift["unlisted"].append(name)
        drift_by_module[module] = drift
    named = doc_named(list(decls), all_tokens)
    for name, decl in decls.items():
        decl["doc_named"] = name in named
    return drift_by_module


def classify(decls: dict[str, dict]) -> None:
    for decl in decls.values():
        if decl["lib_refs"]:
            category = "outside"
        elif decl["test_refs"] or decl["abstract_refs"]:
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
        decl["listed"] = decl.get("listed", False)
        decl["headline"] = decl["listed"] or bool(decl["abstract_refs"])


def find_candidates(lib: Library, decls: dict[str, dict], owners: dict[str, str]) -> None:
    """Privatization candidates: never referenced outside their module, without implicit uses,
    not named in documentation, not deprecated, and not mentioned by the exported statement or
    exposed body of a declaration that stays public (a fixed point, since candidates in the same
    module can become private together)."""
    pins: dict[str, set[str]] = defaultdict(set)
    for name, const in lib.constants.items():
        if const["e"]:
            holder = owner_of(name, owners) or name
            for used in const["u"]:
                target = owner_of(used, owners)
                if target in decls and target != holder:
                    pins[target].add(holder)
    candidates = {n for n, d in decls.items() if d["role"] == "decl" and d["category"] in
                  ("module_only", "unreferenced") and d["sort"] != "deprecated"
                  and not d["implicit"] and not d["doc_named"]}
    while pinned := {n for n in candidates if pins[n] - candidates}:
        candidates -= pinned
    for name, decl in decls.items():
        decl["candidate"] = name in candidates
        decl["pinned_by"] = sorted(pins[name] - candidates)


def find_duplicates(lib: Library, decls: dict[str, dict]) -> list[dict]:
    """Groups of declarations, other than deprecated ones and aliases, in different modules."""
    duplicates = []
    for row in lib.duplicate_rows:
        members = [(m, n) for m, n in row["dup"] if n in decls and decls[n]["role"] == "decl"
                   and decls[n]["sort"] not in ("deprecated", "alias")]
        if len({m for m, _ in members}) > 1:
            duplicates.append({"kind": row["k"], "members": sorted(members)})
            for _, n in members:
                decls[n]["duplicate"] = row["k"]
    return duplicates


def analyse(build_dir: Path) -> dict:
    lib = Library(build_dir)
    decls, owners, private_count = collect_declarations(lib)
    generated_public = sum(1 for name, const in lib.constants.items() if const["e"]
                           and name not in decls and not any(map(is_internal, name.split("."))))
    annotate_headers(lib, decls)
    collect_references(lib, decls, owners)
    doc_drift = check_module_docs(lib, decls, owners)
    classify(decls)
    find_candidates(lib, decls, owners)
    duplicates = find_duplicates(lib, decls)
    imports = {m: [(i[0], not i[1]) for i in lib.ileans[m]["directImports"]
                   if i[0].startswith("Complexity.") and i[0] in lib.ileans] for m in lib.modules}
    proofs, unparsed = {}, []
    for m in lib.modules:
        try:
            proofs[m] = scan_proofs(lib.source(m).text, str(source_path(m).relative_to(ROOT)))
        except ValueError as error:  # keep the other signals when one module defeats the scanner
            proofs[m] = []
            unparsed.append(f"{m}: {error}")
    return {
        "decls": decls, "doc_drift": doc_drift, "duplicates": duplicates, "proofs": proofs,
        "fanout": rebuild_fanout(imports), "importers": transitive_importers(imports),
        "private_count": sum(private_count.values()), "generated_public": generated_public,
        "lib_modules": lib.modules, "proofs_unparsed": unparsed,
        "tidy_usage": tidy_usage_report(lib),
    }


# --- Reporting ----------------------------------------------------------------------------------

def surface_counts(decls: list[dict]) -> Counter:
    counts = Counter({"public": 0, "never_outside": 0, "candidates": 0})
    for d in decls:
        counts["public"] += 1
        counts[d["category"]] += 1
        if d["category"] in ("module_only", "unreferenced"):
            counts["never_outside"] += 1
            if d["sort"] == "deprecated":
                counts["never_outside_deprecated"] += 1
            elif d["implicit"]:
                counts["never_outside_implicit"] += 1
            elif d["doc_named"]:
                counts["never_outside_doc_named"] += 1
            elif not d["candidate"]:
                counts["never_outside_pinned"] += 1
            else:
                counts["candidates"] += 1
                kind = "theorems" if d["sort"] == "theorem" else "definitions"
                counts["candidate_" + kind] += 1
        if d["category"] == "tests_only":
            counts["tests_only_" + ("both" if d["test_refs"] and d["abstract_refs"] else
                                    "abstracts" if d["abstract_refs"] else "tests")] += 1
    return counts


def group_metrics(decls: list[dict], modules: list[str], result: dict) -> dict:
    surface = surface_counts(decls)
    live = [d for d in decls if d["sort"] not in ("deprecated", "alias")]
    tidy = [d for d in live if d["tidy"] and not d["path"].startswith(TIDY_EXEMPT)]
    defs = [d for d in live if d["sort"] in ("definition", "type")]
    thms = [d for d in live if d["sort"] == "theorem"]
    heads = [d for d in thms if d["headline"]]
    drift = [result["doc_drift"][m] for m in modules]
    exposed = [d for d in live if d["exported"] == "def" and d["sort"] == "definition"
               and d["keyword"] not in ("abbrev", "instance")]
    proofs = [p for m in modules for p in result["proofs"][m]]
    hubs = sorted(modules, key=lambda m: -len(result["importers"][m]))
    return {
        "modules": len(modules), "surface": dict(surface),
        "tidy_statements": len(tidy),
        "tidy_statements_used_outside": sum(d["category"] == "outside" for d in tidy),
        "definitions": len(defs), "definitions_undocumented": sum(not d["doc"] for d in defs),
        "theorems": len(thms), "theorems_undocumented": sum(not d["doc"] for d in thms),
        "listed_theorems": len(heads),
        "listed_theorems_undocumented": sum(not d["doc"] for d in heads),
        "doc_listed": sum(x["listed"] for x in drift),
        "doc_listed_missing": sum(len(x["missing"]) for x in drift),
        "doc_listed_private": sum(len(x["private"]) for x in drift),
        "doc_listed_elsewhere": sum(len(x["elsewhere"]) for x in drift),
        "doc_unlisted_definitions": sum(len(x["unlisted"]) for x in drift),
        "modules_without_main_section": sum(not x["has_main"] for x in drift),
        "duplicate_theorems": sum(d.get("duplicate") == "thm" for d in decls),
        "duplicate_definitions": sum(d.get("duplicate") == "def" for d in decls),
        "exposed_definitions": len(exposed),
        "exposed_unreferenced_elsewhere": sum(not d["lib_refs"] for d in exposed),
        "exposed_not_unfolded_elsewhere": sum(bool(d["lib_refs"]) and not d["unfolded_by"]
                                              and "simp" not in d["attrs"] for d in exposed),
        "top_hubs": [(m, len(result["importers"][m]), len(result["fanout"][m])) for m in hubs[:5]],
        "proofs": len(proofs), "proofs_at_least_40": sum(p["body_lines"] >= 40 for p in proofs),
        "proofs_at_least_100": sum(p["body_lines"] >= 100 for p in proofs),
        "longest_proofs": [(p["name"], p["file"], p["body_lines"]) for p in
                           sorted(proofs, key=lambda p: -p["body_lines"])[:3]],
    }


def pct(part: int, whole: int) -> str:
    return f"{part:,} ({100 * part / whole:.0f}%)" if whole else "0"


def area_table(report: dict) -> list[str]:
    out = ["| Area | Modules | Public | (a) Never referenced outside module | (b) Tests or "
           "abstracts only | (c) Tidy in statements | (d) Undocumented defs · listed thms · all "
           "thms | (e) Doc drift: listed missing · unlisted defs | (f) Duplicates: thms · defs | "
           "(g) Top hub: importers (rebuild fan-out) | (h) Proofs ≥100 (≥40) lines |",
           "|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|"]
    for name, g in list(report["areas"].items()) + [("Total", report["totals"])]:
        s = g["surface"]
        hub = g["top_hubs"][0] if g["top_hubs"] else ("", 0, 0)
        out.append(
            f"| {name} | {g['modules']:,} | {s['public']:,} | "
            f"{pct(s['never_outside'], s['public'])} | {s.get('tests_only', 0):,} | "
            f"{g['tidy_statements']:,} | {g['definitions_undocumented']:,} · "
            f"{g['listed_theorems_undocumented']:,} / {g['listed_theorems']:,} · "
            f"{g['theorems_undocumented']:,} / {g['theorems']:,} | "
            f"{g['doc_listed_missing'] + g['doc_listed_private']:,} · "
            f"{g['doc_unlisted_definitions']:,} | {g['duplicate_theorems']:,} · "
            f"{g['duplicate_definitions']:,} | "
            f"{hub[1]:,} ({hub[2]:,}) | {g['proofs_at_least_100']:,} "
            f"({g['proofs_at_least_40']:,}) |")
    return out


def surface_table(groups: dict) -> list[str]:
    out = ["| Directory | Public | Used by other library modules | Tests or abstracts only | "
           "Never referenced outside module | … used in own module | … implicit-use attribute | "
           "… named in docs | … deprecated | … in a public statement | Privatization candidates "
           "(thm / def) |",
           "|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|"]
    for name, g in groups.items():
        s = g["surface"]
        out.append(
            f"| {name} | {s['public']:,} | {s.get('outside', 0):,} | {s.get('tests_only', 0):,} | "
            f"{pct(s['never_outside'], s['public'])} | {s.get('module_only', 0):,} | "
            f"{s.get('never_outside_implicit', 0):,} | {s.get('never_outside_doc_named', 0):,} | "
            f"{s.get('never_outside_deprecated', 0):,} | {s.get('never_outside_pinned', 0):,} | "
            f"{s['candidates']:,} "
            f"({s.get('candidate_theorems', 0):,} / {s.get('candidate_definitions', 0):,}) |")
    return out


def markdown(report: dict, top: int) -> str:
    t = report["totals"]
    s = t["surface"]
    dirty = " with uncommitted changes" if report["dirty"] else ""
    out = [f"Revision `{report['revision']}`{dirty} ({report['date']}); build outputs "
           f"{report['outputs']}. {t['modules']:,} library modules, {s['public']:,} public "
           f"declarations written in source, {report['private_declarations']:,} private ones. "
           f"References to the {report['generated_public']:,} public constants Lean generates "
           "(constructors, recursors, equation lemmas, `simps` lemmas, …) count for the "
           "declaration they come from; structure fields and constructors count for their type.",
           "", "### Quality signals by area (#587)", ""] + area_table(report)
    out += ["", "Areas (#587): " + "; ".join(f"**{n}** = {d}" for n, d, _ in AREAS)
            + f"; **{OTHER_AREA}** = `Init` and any unassigned path. (c) excludes "
            f"`{TIDY_EXEMPT}`. (d) lists theorems named in a module's \"Main …\" sections or used "
            "by an abstract. (f) counts declarations whose statement is alpha-equivalent to one "
            "in another module, and definitions whose type and exposed body both are. (g) counts "
            "library modules only.", ""]
    out += ["### Public surface by top-level directory (#584)", ""]
    out += surface_table({**report["directories"], "Total": t})
    out += ["",
            f"\"Tests or abstracts only\": {s.get('tests_only_tests', 0):,} by tests, "
            f"{s.get('tests_only_abstracts', 0):,} by abstracts, {s.get('tests_only_both', 0):,} "
            "by both. Candidates are never referenced outside their module, carry no attribute "
            "through which they can be used without being named (`simp`, `fun_prop`, `aesop`, "
            "instances, notation, …), are not named in any module docstring or README, are not "
            "deprecated, and are not mentioned by the exported statement or exposed body of a "
            "declaration that stays public.",
            f"Definitions exposed by `@[expose]` (not instances or abbreviations): "
            f"{t['exposed_definitions']:,}. Of these, {t['exposed_unreferenced_elsewhere']:,} are "
            "not referenced by any other library module, and "
            f"{t['exposed_not_unfolded_elsewhere']:,} more are referenced but never unfolded by "
            "name there (`unfold`, `delta`, an element of a `simp`/`rw` list, an equation lemma).",
            "", f"### Modules with the most declarations never referenced outside (top {top})", "",
            "| Module | Never referenced outside | Candidates | Public | Transitive importers | "
            "Rebuild fan-out |", "|---|--:|--:|--:|--:|--:|"]
    for row in report["top_modules"][:top]:
        out.append(f"| `{row['module'].removeprefix('Complexity.')}` | {row['never_outside']} | "
                   f"{row['candidates']} | {row['public']} | {row['importers']} | "
                   f"{row['fanout']} |")
    out += ["", f"### Most imported modules (top {top})", "",
            "| Module | Transitive importers | Rebuild fan-out | Public | "
            "Never referenced outside |",
            "|---|--:|--:|--:|--:|"]
    for row in report["hubs"][:top]:
        out.append(f"| `{row['module'].removeprefix('Complexity.')}` | {row['importers']} | "
                   f"{row['fanout']} | {row['public']} | {row['never_outside']} |")
    out += ["", "Rebuild fan-out: the modules Lake rebuilds when the module's exported interface "
            "changes, namely its direct importers and the importers of modules that reexport it "
            "through `public import` chains.", "", "Limitations: " + " ".join(report["notes"])]
    out += ["", tidy_usage_markdown(report["tidy_usage"], top)]
    return "\n".join(out) + "\n"


NOTES = [
    "Counts are review signals, not rules: zero in-repository references does not mean that a "
    "declaration is unwanted API.",
    "Uses through simp sets, instances, fun_prop, Aesop rules, notation and macros leave no "
    "reference; such declarations are flagged and never candidates.",
    "Definitional unfolding without naming a definition (rfl, decide) is not detected.",
    "The guide (#585) is scanned only for S4 source-level tidy signals, not API quality.",
]


def build_report(result: dict, top: int) -> dict:
    decls = [d for d in result["decls"].values() if d["role"] == "decl"]
    by_area, by_dir, by_module = defaultdict(list), defaultdict(list), defaultdict(list)
    for d in decls:
        by_area[d["area"]].append(d)
        by_dir[top_dir(d["path"])].append(d)
        by_module[d["module"]].append(d)
    modules_by_area, modules_by_dir = defaultdict(list), defaultdict(list)
    for m in result["lib_modules"]:
        rel = m.removeprefix("Complexity.").replace(".", "/")
        modules_by_area[area_of(rel + "/")].append(m)
        modules_by_dir[top_dir(rel)].append(m)
    revision = run(["git", "rev-parse", "HEAD"], capture_output=True).stdout.strip()
    dirty = bool(run(["git", "status", "--porcelain", "--", "Complexity", "ComplexityTests",
                      "abstracts"], capture_output=True).stdout.strip())
    module_rows = []
    for m in result["lib_modules"]:
        s = surface_counts(by_module[m])
        module_rows.append({"module": m, "public": s["public"], "candidates": s["candidates"],
                            "never_outside": s["never_outside"],
                            "importers": len(result["importers"][m]),
                            "fanout": len(result["fanout"][m])})
    order = [name for name, _, _ in AREAS] + [OTHER_AREA]
    return {
        "revision": revision, "dirty": dirty, "date": datetime.date.today().isoformat(),
        "build_dir": str(DEFAULT_BUILD_DIR), "outputs": "",
        "notes": NOTES + [f"Proof lengths skip {len(result['proofs_unparsed'])} modules the "
                          "scanner cannot parse; see `proofs_unparsed`."] * bool(
                              result["proofs_unparsed"]),
        "proofs_unparsed": result["proofs_unparsed"],
        "tidy_usage": result["tidy_usage"],
        "private_declarations": result["private_count"],
        "generated_public": result["generated_public"],
        "areas": {a: group_metrics(by_area[a], modules_by_area[a], result) for a in order},
        "directories": {k: group_metrics(by_dir[k], modules_by_dir[k], result)
                        for k in sorted(modules_by_dir) if by_dir[k]},
        "totals": group_metrics(decls, result["lib_modules"], result),
        "top_modules": sorted(module_rows, key=lambda r: (-r["never_outside"], -r["candidates"],
                                                          r["module"])),
        "hubs": sorted(module_rows, key=lambda r: (-r["importers"], r["module"])),
        "duplicates": result["duplicates"],
        "doc_drift": {m: x for m, x in result["doc_drift"].items()
                      if x["missing"] or x["private"] or x["elsewhere"] or x["unlisted"]},
        "declarations": [{k: (sorted(v) if isinstance(v, set) else v) for k, v in d.items()
                          if k not in ("range", "parent", "role")} for d in decls],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--build-dir", type=Path, default=DEFAULT_BUILD_DIR,
                        help="read build outputs from here; unless --no-build-check is given, "
                        "they must equal the current default outputs")
    parser.add_argument("--json", type=Path, help="write the full report, with every declaration")
    parser.add_argument("--markdown", type=Path, help="write the tables to a file")
    parser.add_argument("--top", type=int, default=20)
    parser.add_argument("--no-build-check", action="store_true",
                        help="do not check that the build outputs are current")
    args = parser.parse_args()
    outputs = check_outputs(args.build_dir, args.no_build_check)
    report = build_report(analyse(args.build_dir), args.top)
    report["build_dir"], report["outputs"] = str(args.build_dir), outputs
    report["tidy_usage"]["provenance"]["outputs"] = outputs
    text = markdown(report, args.top)
    if args.markdown:
        args.markdown.write_text(text)
    else:
        print(text)
    if args.json:
        args.json.write_text(json.dumps(report, indent=1, ensure_ascii=False) + "\n")


if __name__ == "__main__":
    main()
