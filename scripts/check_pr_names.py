#!/usr/bin/env python3
"""Advisory check that the Lean names a PR description mentions exist at the checked-out revision.

Usage: python3 scripts/check_pr_names.py (--pr N | --file PATH | --event PATH) [--strict]
           [--base REF] [--root DIR] [--github] [--no-core]

A pull request's description maps its source to the Lean declarations that formalize it, and a
reviewer reads it against the code. A name that the code does not declare, usually one renamed or
dropped while the PR evolved, costs a review round. This tool extracts the backticked tokens of a
Markdown text (the body of PR N fetched with `gh pr view N --json body`, a file, `-` for standard
input, or the `pull_request` event payload that GitHub Actions stores at `$GITHUB_EVENT_PATH`),
keeps those that look like Lean names, and reports the ones not declared in the sources of the
checked-out revision (or of `--root DIR`): `Complexity/`, `ComplexityTests/`, `abstracts/`,
`scripts/`, every package under `.lake/packages` (cslib, Mathlib, Batteries, ...) and, when `lean`
is on the path, the toolchain's `Init`, `Std` and `Lean` sources. Run it on the PR's head checkout.

The check reads source text, not the compiled environment, and errs towards accepting a name:

* it skips fenced code blocks, HTML comments and tokens that are not names: expressions with
  spaces or operators, numbers and hashes, file names, all-caps words, Lean keywords and tactic
  names, single letters, `_`-led fragments and lowercase words without an underscore (`simp`,
  `trace`, `ε`), which are usually variables or prose; a name shaped like a hypothesis (`hfA`,
  `h_le`) is dropped from the report when it is not declared but occurs in the sources;
* a declaration's full name combines its `namespace` blocks with its declared name, and a token
  is declared when it equals a full name or is a dot-separated suffix of one (`Nodup` and
  `List.Nodup` both match `List.Nodup`); a namespace name matches its `namespace` block or any
  declaration under it, and a module name or a dotted suffix of one (`Complexity.Crypto.PRF`,
  `Crypto.PRF`) matches its file;
* structure fields and parent projections, inductive constructors, `where` auxiliaries, `alias`
  and `irreducible_def` names, and the names Lean generates (`.mk`, `.rec`, `.ext_iff`, `.eq_1`,
  ...) count as declarations, as do Mathlib's `to_additive` names (explicit, or by the usual
  `prod`/`sum`, `mul`/`add` translation) and `simps` lemmas (`foo_apply`);
* field notation on a theorem (`foo_le.trans`, `bar_iff.mp`) counts when the theorem is declared;
* the module, function and class names of `scripts/*.py` count too, for tooling PRs.

Each name that is not declared is reported with what the sources say about it: a name declared
in this repository under another namespace (`did you mean ...`), one mentioned only in other
ways (a variable, binder, notation or private name, or a slip), or one found nowhere, which is
almost certainly a slip. Names that this repository declared at the base commit (`--base`, by
default the merge base of HEAD with `origin/main`) are marked as removed or renamed by the change:
a refactoring PR names what it removes. The tool is advisory and exits 0; `--strict` makes it exit
1 when a name is reported that the change did not remove. With `--github` it also writes the
report to the job summary (`$GITHUB_STEP_SUMMARY`) and as a notice annotation. CI runs it on pull
requests after the build, so the package sources are present, with the PR body from the event
payload, the checked-out merge commit of the PR head into its base, and that commit's first parent
as the base.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LOCAL_DIRS = ("Complexity", "ComplexityTests", "abstracts", "scripts")

# --- Extracting candidate names from Markdown -----------------------------------------------------

FENCE = re.compile(r"^[ \t]*(`{3,}|~{3,}).*?^[ \t]*\1[ \t]*$", re.M | re.S)
HTML_COMMENT = re.compile(r"<!--.*?-->", re.S)
# A backtick span: a run of backticks, content without that run, the same run (CommonMark).
SPAN = re.compile(r"(?<!`)(`+)(?!`)(.+?)(?<!`)\1(?!`)", re.S)
IDENT_CHARS = r"[^\W\d]|_"
COMPONENT = rf"(?:{IDENT_CHARS})[\w'!?]*"
NAME = re.compile(rf"^\.?{COMPONENT}(?:\.{COMPONENT})*$")
FILE_SUFFIXES = {"lean", "md", "py", "sh", "json", "toml", "yml", "yaml", "txt", "bib", "tex",
                 "olean", "ilean", "pdf", "html", "js", "csv", "jsonl", "lock", "cfg"}
HYPOTHESIS = re.compile(r"^h[a-z]{0,2}[A-Z0-9_'₀-₉]|^h[a-z]{0,3}$|^this$")
LEAN_KEYWORDS = {
    "abbrev", "alias", "axiom", "by", "class", "def", "deriving", "do", "else", "end", "example",
    "export", "extends", "fun", "have", "if", "import", "in", "inductive", "instance", "lemma",
    "let", "match", "module", "mutual", "namespace", "noncomputable", "open", "opaque", "private",
    "protected", "public", "section", "show", "sorry", "structure", "suffices", "then", "theorem",
    "universe", "variable", "where", "with", "Type", "Prop", "Sort",
}
# Tactics, commands and options that a description may name; the sources' `syntax`, `macro` and
# `elab` keywords are added to this set as they are read.
TACTICS = {
    "all_goals", "any_goals", "apply_fun", "by_cases", "by_contra", "change_at", "exact_mod_cast",
    "field_simp", "fin_cases", "first_order", "interval_cases", "native_decide", "norm_cast",
    "norm_num", "push_cast", "push_neg", "rw_mod_cast", "simp_all", "simp_arith", "simp_rw",
    "split_ifs", "nlinarith", "decide_eq_true", "ring_nf", "set_option", "maxHeartbeats",
    "maxRecDepth", "autoImplicit", "relaxedAutoImplicit", "check_abstract", "print_axioms",
    "lake", "mk_all", "lint_style", "checkInitImports", "runLinter", "pull_request",
    "merge_group", "workflow_dispatch", "to_additive", "to_dual", "simps", "irreducible_def",
    "fun_prop", "reducible_and_instances",
}


def strip_markdown(text: str) -> str:
    """The text with fenced code blocks and HTML comments removed."""
    return FENCE.sub("", HTML_COMMENT.sub("", text))


def extract_tokens(text: str) -> list[str]:
    """The distinct backticked tokens of a Markdown text, in order of first appearance."""
    seen: dict[str, None] = {}
    for match in SPAN.finditer(strip_markdown(text)):
        token = match.group(2).strip()
        if token:
            seen.setdefault(token, None)
    return list(seen)


def is_candidate(token: str) -> bool:
    """Whether a backticked token looks like a Lean declaration or module name worth checking."""
    if not NAME.match(token):
        return False
    bare = token.lstrip(".").removeprefix("_root_.")
    if bare.startswith("_"):
        return False  # a fragment such as `_leaf_le`
    parts = bare.split(".")
    if len(parts) > 1 and parts[-1].lower() in FILE_SUFFIXES:
        return False
    if bare in LEAN_KEYWORDS or bare in TACTICS:
        return False
    if any(p.startswith("linter") for p in parts[:1]):
        return False
    letters = [c for c in bare if c.isalpha()]
    if letters and all(c.isupper() for c in letters) and len(letters) > 1:
        return False  # environment variables and acronyms: `GITHUB_EVENT_PATH`, `PRF`
    if len(parts) == 1:
        if len(bare) < 2:
            return False
        if "_" not in bare and not any(c.isupper() for c in bare):
            return False  # lowercase prose, variables and tactics: `simp`, `trace`, `ε`
    return True


# --- Reading declarations from Lean sources -------------------------------------------------------

MODIFIERS = (r"(?:(?:private|protected|public|noncomputable|partial|unsafe|nonrec|scoped|local|"
             r"meta)\s+)*")
ATTRS = r"(?:@\[[^\]]*\]\s*)*"
IDENT = r"[^\s:({\[⦃⟨,|@]+"
DECL = re.compile(
    rf"^\s*{ATTRS}{MODIFIERS}(theorem|lemma|def|abbrev|instance|axiom|opaque|irreducible_def|"
    rf"class\s+inductive|structure|class|inductive|coinductive|alias)\s+(.*)$")
NAMESPACE = re.compile(r"^\s*namespace\s+(\S+)")
SECTION = re.compile(rf"^\s*{ATTRS}{MODIFIERS}(?:section|mutual)\b")
END = re.compile(r"^\s*end\b\s*(\S*)")
TO_ADDITIVE = re.compile(r"to_additive\b((?:\s*\([^)]*\))*)\s+(?:existing\s+)?([^\s\"\]\[,()]+)")
SYNTAX_KEYWORD = re.compile(r"^\s*" + ATTRS + MODIFIERS +
                            r"(?:syntax|macro|elab|elab_rules|macro_rules)\b.*?\"([\w!?']+)")
SIMPS_SUFFIX = re.compile(r"^(.+?)_(?:symm_apply|apply|coe|toFun|invFun|fst|snd|val|mk)$")
GENERATED = {"mk", "rec", "recOn", "casesOn", "noConfusion", "noConfusionType", "ext", "ext_iff",
             "inj", "injEq", "inj_iff", "eq_def", "sizeOf_spec", "below", "brecOn", "induct",
             "ctorIdx", "match_1", "proof_1", "out", "elim", "mk_iff", "fun_cases", "eq_iff"}
ADDITIVE = [("nsmul", "pow"), ("zsmul", "zpow"), ("vadd", "smul"), ("vsub", "sdiv"),
            ("sum", "prod"), ("Sum", "Prod"), ("add", "mul"), ("Add", ""), ("zero", "one"),
            ("Zero", "One"), ("neg", "inv"), ("Neg", "Inv"), ("sub", "div"), ("Sub", "Div")]
WORD_BOUNDARY = r"(?<![\w'!?])"


COMMENT_MARK = re.compile(r"/-|-/|--")


def strip_comments(text: str) -> str:
    """Lean source with comments and docstrings blanked, newlines kept."""
    out: list[str] = []
    depth, pos = 0, 0
    for mark in COMMENT_MARK.finditer(text):
        start = mark.start()
        if start < pos:
            continue
        token = mark.group(0)
        if depth == 0:
            if token == "-/":
                continue
            out.append(text[pos:start])
            if token == "--":
                end = text.find("\n", start)
                pos = len(text) if end < 0 else end
            else:
                depth, pos = 1, mark.end()
        else:
            out.append("\n" * text.count("\n", pos, start))
            depth += 1 if token == "/-" else -1 if token == "-/" else 0
            pos = mark.end()
    out.append(text[pos:] if depth == 0 else "\n" * text.count("\n", pos))
    return "".join(out)


@dataclass
class Declarations:
    """Names declared in a set of sources, indexed by their last component."""
    by_last: dict[str, set[str]] = field(default_factory=lambda: defaultdict(set))
    namespaces: set[str] = field(default_factory=set)
    keywords: set[str] = field(default_factory=set)

    def add(self, full: str) -> None:
        full = full.removeprefix("_root_.")
        if not full or full.startswith("«"):
            return
        self.by_last[full.rsplit(".", 1)[-1]].add(full)
        parts = full.split(".")
        for k in range(1, len(parts)):
            self.namespaces.add(".".join(parts[:k]))

    def declared(self, token: str) -> bool:
        """Whether `token` names a declaration, as a full name or a dotted suffix of one."""
        last = token.rsplit(".", 1)[-1]
        return any(full == token or full.endswith("." + token)
                   for full in self.by_last.get(last, ()))

    def namespace(self, token: str) -> bool:
        return any(ns == token or ns.endswith("." + token) for ns in self.namespaces
                   if ns.endswith(token))


def first_ident(rest: str) -> str | None:
    match = re.match(IDENT, rest.strip())
    return match.group(0) if match else None


def parse_source(text: str, decls: Declarations) -> None:
    """Add the declarations of one Lean file to `decls`."""
    stack: list[str] = []  # namespace components, "" for a section or mutual block
    member_of: str | None = None  # declaration whose fields, constructors or auxiliaries follow
    member_kind = ""
    member_indent: int | None = None
    awaiting_where = False

    def prefix() -> str:
        return ".".join(s for s in stack if s)

    def full(name: str) -> str:
        if name.startswith("_root_."):
            return name
        return f"{prefix()}.{name}" if prefix() else name

    for raw in strip_comments(text).splitlines():
        line = raw.rstrip()
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip())
        keyword = SYNTAX_KEYWORD.match(line)
        if keyword:
            decls.keywords.add(keyword.group(1))
        for attr in TO_ADDITIVE.finditer(line):
            name = attr.group(2)
            if NAME.match(name):
                decls.add(full(name))
        if indent == 0 and line == "where" and member_of is not None:
            awaiting_where = False  # `where` auxiliaries after a body
            continue
        if indent == 0:
            member_of, member_indent, awaiting_where = None, None, False
        elif member_of is not None:
            if awaiting_where:
                if re.search(r"(^|\s)where\b", line):
                    awaiting_where = False
                continue
            if member_kind == "inductive":
                for ctor in re.finditer(rf"\|\s*({IDENT})", line):
                    decls.add(f"{member_of}.{ctor.group(1)}")
                continue
            if member_indent is None:
                member_indent = indent
            if indent == member_indent:
                fields = re.match(rf"^\s*(?:\|\s*)?{ATTRS}{MODIFIERS}[({{\[⦃]?\s*"
                                  rf"((?:{IDENT}\s+)*?{IDENT})\s*"
                                  r"(?:::|:=|:|\(|\{|\[|⦃)", line)
                if fields:
                    for name in fields.group(1).split():
                        decls.add(f"{member_of}.{name}")
            continue
        if m := NAMESPACE.match(line):
            stack.append(m.group(1))
            continue
        if SECTION.match(line):
            stack.append("")
            continue
        if m := END.match(line):
            if stack:
                stack.pop()
            continue
        m = DECL.match(line)
        if not m:
            continue
        kind, rest = m.group(1), m.group(2)
        if kind == "alias":
            names = re.findall(rf"{IDENT}", rest.split(":=")[0].replace("⟨", " ").replace("⟩", " "))
            for name in names:
                if name != "_":
                    decls.add(full(name))
            continue
        if kind == "instance":
            rest = re.sub(r"^\(priority\s*:=[^)]*\)\s*", "", rest.strip())
        name = first_ident(rest)
        if not name or name.startswith(("(", "{", "[")):
            continue
        name_full = full(name)
        decls.add(name_full)
        member_of, member_indent = name_full, None
        if kind in ("structure", "class"):
            member_kind = "structure"
            head = rest.split(" where", 1)[0]
            if ext := re.search(r"\bextends\b(.*?)(?::|$)", head):
                for parent in ext.group(1).split(","):
                    if ident := first_ident(parent):
                        decls.add(f"{name_full}.to{ident.rsplit('.', 1)[-1]}")
            awaiting_where = not re.search(r"\swhere\b|:=", rest)
            for ctor in re.finditer(rf"\bwhere\s+({IDENT})\s*::", rest):
                decls.add(f"{name_full}.{ctor.group(1)}")
        elif kind.endswith("inductive"):
            member_kind = "inductive"
            for ctor in re.finditer(rf"\|\s*({IDENT})", rest):
                decls.add(f"{name_full}.{ctor.group(1)}")
        else:
            member_kind = "where"
            awaiting_where = not re.search(r"(^|\s)where\s*$", rest)


# --- Finding the sources --------------------------------------------------------------------------

def source_roots(root: Path, core: bool = True) -> list[Path]:
    """Directories whose `.lean` files are searched for declarations."""
    roots = [root / d for d in LOCAL_DIRS if (root / d).is_dir()]
    packages = root / ".lake" / "packages"
    if packages.is_dir():
        roots += sorted(p for p in packages.iterdir() if p.is_dir())
    if core and shutil.which("lean"):
        try:
            prefix = subprocess.run(["lean", "--print-prefix"], cwd=root, capture_output=True,
                                    text=True, timeout=60).stdout.strip()
        except (OSError, subprocess.SubprocessError):
            prefix = ""
        src = Path(prefix) / "src" / "lean" if prefix else None
        if src and src.is_dir():
            roots += [src / d for d in ("Init", "Std", "Lean") if (src / d).is_dir()]
    return roots


def lean_files(roots: list[Path]) -> list[Path]:
    files: list[Path] = []
    for r in roots:
        for dirpath, dirnames, filenames in os.walk(r):
            dirnames[:] = [d for d in dirnames if d not in (".lake", ".git", "build")]
            files += [Path(dirpath) / f for f in filenames if f.endswith(".lean")]
    return files


def files_mentioning(roots: list[Path], words: set[str]) -> list[Path]:
    """The `.lean` files under `roots` containing one of `words`, by ripgrep when available."""
    if not words or not roots:
        return []
    rg = shutil.which("rg")
    if rg:
        result = subprocess.run(
            [rg, "--files-with-matches", "--no-messages", "--fixed-strings", "--word-regexp",
             "--no-ignore", "--glob", "*.lean", "--glob", "!.lake/build/**",
             *[arg for w in sorted(words) for arg in ("-e", w)],
             *map(str, roots)], capture_output=True, text=True)
        if result.returncode in (0, 1):
            return [Path(p) for p in result.stdout.splitlines() if "/.lake/build/" not in p]
    pattern = re.compile(r"\b(?:" + "|".join(map(re.escape, sorted(words))) + r")\b")
    found = []
    for path in lean_files(roots):
        try:
            if pattern.search(path.read_text(encoding="utf-8", errors="replace")):
                found.append(path)
        except OSError:
            continue
    return found


# --- Resolving tokens -----------------------------------------------------------------------------

def additive_variants(token: str) -> set[str]:
    """Multiplicative names from which Mathlib's `to_additive` could have generated `token`."""
    variants = set()
    combined = token
    for add, mul in ADDITIVE:
        if add in token:
            variants.add(token.replace(add, mul))
            combined = combined.replace(add, mul)
    variants.add(combined)
    variants.discard(token)
    return {v for v in variants if NAME.match(v)}


def search_words(token: str) -> set[str]:
    """Words whose files must be read to resolve `token` as a declaration in its own right."""
    bare = token.lstrip(".").removeprefix("_root_.")
    last = bare.rsplit(".", 1)[-1]
    words = {last.rstrip("'!?")}
    if m := SIMPS_SUFFIX.match(last):
        words.add(m.group(1))
    if re.fullmatch(r"to[A-Z]\w*", last):  # `extends Inhabited` declares `toInhabited`
        words.add(last[2:].rstrip("'!?"))
    for variant in additive_variants(bare):
        words.add(variant.rsplit(".", 1)[-1].rstrip("'!?"))
    return {w for w in words if w}


def head_words(token: str) -> set[str]:
    """Words whose files are also needed when `token` is a generated name (`Pair.mk`) or field
    notation on a theorem (`foo_iff.mp`): the last component of its head.

    Only these tokens look at the head, so that a qualified name in a large namespace (`Nat.foo`)
    does not read every file mentioning `Nat`."""
    parts = token.lstrip(".").removeprefix("_root_.").split(".")
    if len(parts) < 2:
        return set()
    head, last = parts[-2], parts[-1]
    generated = last in GENERATED or re.fullmatch(r"eq_\d+|proof_\d+|match_\d+", last)
    return {head.rstrip("'!?")} if generated or head[:1].islower() else set()


def module_suffixes(roots: list[Path]) -> set[str]:
    """Every dotted suffix of the module names of the `.lean` files under `roots`.

    `Homomorphic.Layered` and `Layered` are suffixes of `Complexity.Crypto.Homomorphic.Layered`."""
    rg = shutil.which("rg")
    paths: list[Path] = []
    if rg and roots:
        result = subprocess.run([rg, "--files", "--no-messages", "--no-ignore", "--glob", "*.lean",
                                 "--glob", "!.lake/build/**", *map(str, roots)],
                                capture_output=True, text=True)
        if result.returncode in (0, 1):
            paths = [Path(p) for p in result.stdout.splitlines() if "/.lake/build/" not in p]
    if not paths:
        paths = lean_files(roots)
    suffixes: set[str] = set()
    for path in paths:
        parts = path.with_suffix("").parts
        for k in range(1, min(len(parts), 8)):
            suffixes.add(".".join(parts[-k:]))
    return suffixes


def python_names(root: Path) -> set[str]:
    """Module, function and class names of the repository's Python scripts, which a tooling PR's
    description may mention (`check_changed_files.comparison_base`)."""
    names: set[str] = set()
    for path in (root / "scripts").rglob("*.py"):
        names.add(path.stem)
        try:
            text = path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        names.update(re.findall(r"^\s*(?:async\s+)?(?:def|class)\s+(\w+)", text, re.M))
    return names


def resolves(token: str, decls: Declarations, modules: set[str]) -> bool:
    """Whether `token` names a declaration, generated declaration, namespace or module."""
    if token.startswith("."):  # bare field notation such as `.symm`
        return token[1:] in decls.by_last
    bare = token.removeprefix("_root_.")
    if bare in decls.keywords or decls.declared(bare) or decls.namespace(bare) or bare in modules:
        return True
    parts = bare.split(".")
    head, last = ".".join(parts[:-1]), parts[-1]
    if head:
        if (last in GENERATED or re.fullmatch(r"eq_\d+|proof_\d+|match_\d+", last)) and (
                decls.declared(head) or decls.namespace(head)):
            return True
        # Field notation on a theorem: `foo_le.trans`, `Nat.succ_le.mpr`.
        if head.rsplit(".", 1)[-1][:1].islower() and decls.declared(head) and last in decls.by_last:
            return True
    if m := SIMPS_SUFFIX.match(last):
        stem = f"{head}.{m.group(1)}" if head else m.group(1)
        if decls.declared(stem):
            return True
    return any(decls.declared(v) or decls.namespace(v) for v in additive_variants(bare))


@dataclass
class Finding:
    """A backticked name that the checked-out revision does not declare."""
    token: str
    mentions: int = 0  # source files mentioning its last component
    declared_as: list[str] = field(default_factory=list)  # full names with its last component
    removed: bool = False  # declared at the base revision: removed or renamed by the change

    def note(self, base: str | None) -> str:
        if self.removed:
            text = f"declared at the base `{base}`, not at the head (removed or renamed here)"
        elif self.declared_as:
            text = "not declared; did you mean " + ", ".join(f"`{d}`" for d in self.declared_as)
        elif self.mentions:
            plural = "s" if self.mentions != 1 else ""
            text = (f"not declared; mentioned in {self.mentions} source file{plural} "
                    "(a variable, binder, notation or private name?)")
        else:
            text = "not found in any source file"
        return text + ("" if not self.removed or len(self.declared_as) != 1 else
                       f"; now `{self.declared_as[0]}`?")


@dataclass
class Report:
    checked: list[str]
    findings: list[Finding]
    base: str | None = None

    @property
    def unexplained(self) -> list[Finding]:
        """Findings not accounted for by a removal or rename in the change itself."""
        return [f for f in self.findings if not f.removed]


def git(root: Path, *args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["git", *args], cwd=root, capture_output=True, text=True)


def base_declarations(root: Path, base: str, words: set[str]) -> Declarations:
    """Declarations of the repository's own `.lean` files at `base` that mention one of `words`."""
    decls = Declarations()
    if not words:
        return decls
    listed = git(root, "grep", "-l", "-w", "-F", *[a for w in sorted(words) for a in ("-e", w)],
                 base, "--", *[f"{d}/*.lean" for d in LOCAL_DIRS])
    objects = listed.stdout.splitlines()  # `base:path`, which `git cat-file` reads as an object
    if not objects:
        return decls
    batch = subprocess.run(["git", "cat-file", "--batch"], cwd=root, capture_output=True,
                           input="".join(f"{o}\n" for o in objects).encode())
    data, pos = batch.stdout, 0
    while pos < len(data):
        end = data.index(b"\n", pos)
        header = data[pos:end].split()
        pos = end + 1
        if len(header) != 3 or header[1] != b"blob":  # `<object> missing`; a path may hold spaces
            continue
        size = int(header[2])
        parse_source(data[pos:pos + size].decode("utf-8", errors="replace"), decls)
        pos += size + 1
    return decls


def resolve_base(root: Path, base: str | None) -> str | None:
    """The commit to compare with: `base` itself, or the merge base of HEAD with `origin/main`."""
    if base:
        result = git(root, "rev-parse", "--verify", "--quiet", f"{base}^{{commit}}")
        return result.stdout.strip() or None
    result = git(root, "merge-base", "HEAD", "origin/main")
    head = git(root, "rev-parse", "HEAD").stdout.strip()
    merge_base = result.stdout.strip()
    return merge_base if merge_base and merge_base != head else None


def check(text: str, root: Path = ROOT, core: bool = True, base: str | None = None) -> Report:
    """Check the candidate names of a Markdown text against the sources under `root`.

    Names that are not declared are compared with the repository at the commit `base`, if given."""
    tokens = [t for t in extract_tokens(text) if is_candidate(t)]
    if not tokens:
        return Report([], [], base)
    roots = source_roots(root, core)
    decls, local = Declarations(), Declarations()
    local_roots = tuple(str(root / d) + os.sep for d in LOCAL_DIRS)
    texts: dict[Path, str] = {}

    def read(words: set[str]) -> None:
        for path in files_mentioning(roots, words):
            if path in texts:
                continue
            try:
                texts[path] = path.read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            parse_source(texts[path], decls)
            if str(path).startswith(local_roots):
                parse_source(texts[path], local)

    # Module names (`Init`, `Crypto.PRF`), script names and generated names in field notation
    # (`.ext_iff`) need no source files; checking them first avoids reading every file that
    # mentions a word as common as `Lean`.
    modules, python = module_suffixes(roots), python_names(root)
    unresolved = [t for t in tokens if t.removeprefix("_root_.") not in modules
                  and not all(part in python for part in t.split("."))
                  and not (t.startswith(".") and t[1:] in GENERATED)]
    read(set().union(set(), *(search_words(t) for t in unresolved)))
    unresolved = [t for t in unresolved if not resolves(t, decls, set())]
    if more := set().union(set(), *(head_words(t) for t in unresolved)):
        read(more)
        unresolved = [t for t in unresolved if not resolves(t, decls, set())]
    findings = []
    for token in unresolved:
        last = token.lstrip(".").rsplit(".", 1)[-1]
        pattern = re.compile(WORD_BOUNDARY + re.escape(last) + r"(?![\w'!?])")
        mentions = sum(1 for t in texts.values() if last in t and pattern.search(t))
        if mentions and "." not in token and HYPOTHESIS.match(token):
            continue  # a hypothesis or other binder such as `hfA` or `h_le`
        findings.append(Finding(token, mentions, sorted(local.by_last.get(last, ()))[:3]))
    if findings and base:
        before = base_declarations(root, base, {w for f in findings for w in
                                                search_words(f.token) | head_words(f.token)})
        for finding in findings:
            finding.removed = resolves(finding.token, before, set())
    return Report(tokens, findings, base)


# --- Output ---------------------------------------------------------------------------------------

def revision(root: Path) -> str:
    result = git(root, "rev-parse", "--short=12", "HEAD")
    return result.stdout.strip() if result.returncode == 0 else "the working tree"


def markdown(report: Report, rev: str) -> str:
    lines = ["### PR description names (advisory)", ""]
    if not report.findings:
        lines.append(f"All {len(report.checked)} backticked names in the description are declared "
                     f"at `{rev}`.")
        return "\n".join(lines) + "\n"
    base = report.base[:12] if report.base else None
    lines.append(f"Checked {len(report.checked)} backticked names against `{rev}`; "
                 f"{len(report.findings)} {'is' if len(report.findings) == 1 else 'are'} "
                 "not declared there:")
    lines.append("")
    lines += [f"- `{f.token}`: {f.note(base)}" for f in report.findings]
    lines += ["", "Fix the description, or ignore a name that is not meant to be a declaration. "
              "See `scripts/check_pr_names.py`."]
    return "\n".join(lines) + "\n"


def escape(text: str) -> str:
    return text.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")


def load_body(args: argparse.Namespace, root: Path) -> str:
    if args.pr is not None:
        result = subprocess.run(["gh", "pr", "view", str(args.pr), "--json", "body", "-q", ".body"],
                                cwd=root, capture_output=True, text=True)
        if result.returncode != 0:
            raise SystemExit(f"gh pr view {args.pr} failed: {result.stderr.strip()}")
        return result.stdout
    if args.event is not None:
        event = json.loads(Path(args.event).read_text(encoding="utf-8"))
        return (event.get("pull_request") or {}).get("body") or ""
    if args.file == "-":
        return sys.stdin.read()
    return Path(args.file).read_text(encoding="utf-8")


def main(argv: list[str] | None = None, root: Path = ROOT) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--pr", type=int, help="check the body of this pull request (uses `gh`)")
    source.add_argument("--file", help="check this Markdown file (`-` for standard input)")
    source.add_argument("--event",
                        help="check the body in this GitHub `pull_request` event payload")
    parser.add_argument("--strict", action="store_true",
                        help="exit 1 when a name is reported that the change did not remove")
    parser.add_argument("--github", action="store_true",
                        help="also write the job summary and a notice annotation")
    parser.add_argument("--no-core", action="store_true",
                        help="do not search the Lean toolchain's Init, Std and Lean sources")
    parser.add_argument("--root", type=Path, default=root,
                        help="checkout to check against (default: this script's checkout)")
    parser.add_argument("--base", help="commit before the change, to recognize names it removed "
                        "(default: the merge base of HEAD with origin/main)")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    base = resolve_base(root, args.base)
    report = check(load_body(args, root), root, core=not args.no_core, base=base)
    text = markdown(report, revision(root))
    print(text, end="")
    if args.github and report.unexplained:
        names = ", ".join(f"`{f.token}`" for f in report.unexplained)
        message = f"Not declared at the PR head: {names}. Advisory only; see the job summary."
        print(f"::notice title=PR description names::{escape(message)}")
    if args.github and os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as summary:
            summary.write(text)
    return 1 if args.strict and report.unexplained else 0


if __name__ == "__main__":
    sys.exit(main())
