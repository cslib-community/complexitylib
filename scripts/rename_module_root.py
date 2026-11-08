#!/usr/bin/env python3
"""Rename the Lean module root `Complexity` to `CslibFrontier`, and restack branches across it.

The flag-day rename changes module names and source paths only. Declarations keep their
namespaces (`Cslib.*`, `Cslib.Complexity.*`, `Turing.*`, and the test and script namespaces
`ComplexityTests.*`, `ComplexityScripts.*`, ...), so no identifier in Lean code changes.

Apply mode (the default) transforms the checkout in the current directory in place:

    python3 scripts/rename_module_root.py [--no-mk-all]

1. `git mv` renames the roots: `Complexity/` and `Complexity.lean` become `CslibFrontier/` and
   `CslibFrontier.lean`; likewise `ComplexityTests`, `ComplexityResults`, `ComplexityAbstracts`,
   `ComplexityComparator*` and the guide's `ComplexityGuide*` (each where it exists).
2. Every tracked text file is rewritten, except `EXCLUDED` and lines carrying the pragma
   `rename-module-root: keep`. The rules (`Rewriter`) touch only
   * `import` lines and single-backtick module-name literals in Lean code;
   * module names in comments, strings and non-Lean files that name an existing module, a
     directory of modules or a top-level area of `Complexity/` (`Complexity.Init`,
     `Complexity.Computability.…`), or a root followed by a file extension (`Complexity.lean`);
   * paths that start at a root (`Complexity/…`, `../../ComplexityTests/…`, `blob/main/…`, the
     API documentation site), never a nested `…/Computability/Complexity/…` nor a path inside a
     permalink to a fixed commit;
   * a bare root in Lake targets, quotes, backticks, commands and phrases such as "`Complexity`
     modules";
   * the GitHub repository and documentation URLs, and the Lake package name in `name = …`,
     manifests, `@complexitylib` targets and `lake update` commands.
   Python and shell sources are tooling, whose dotted root tokens are module names even when the
   module does not exist (test fixtures), so they are rewritten too.
   `manual/development-history/` and `manual/data/` describe and analyse the pinned historical
   snapshot, so only their URLs change.
3. The aggregators are regenerated: with `lake exe mk_all` unless `--no-mk-all`, otherwise by the
   same rule in Python (`regenerate_aggregates`).

A second run is a no-op. `--report` lists the old-root tokens that remain and why.

Restack mode brings a branch that forked before the rename onto the renamed tree:

    python3 <post-rename checkout>/scripts/rename_module_root.py --restack [--onto REF]

Run it in a clean checkout of the branch. `--onto` (default: the rename commit, the first commit
on the first-parent history of `origin/main` that has `CslibFrontier.lean`) is the post-rename
commit to merge, such as the rename commit or the restacked head of a lower stacked branch. Its
pre-rename counterpart `PRE` is the nearest first-parent ancestor of `--onto` without
`CslibFrontier.lean` (the rename commit's parent).
1. If `PRE` is not an ancestor of HEAD, merge it normally (the `leanagg` and `bibkeys` drivers are
   enabled for this merge; aggregate conflicts are regenerated). Other conflicts stop the tool:
   resolve and commit them, then run it again.
2. Merge `--onto`. Git's rename detection would carry the branch's edits to renamed files, but
   the rename rewrote every import line, so a branch that edits an import block would conflict
   with it. The tree is therefore computed as a three-way merge of already converted trees: base
   `apply(PRE)`, ours `apply(HEAD)` and theirs `--onto`. Apply mode is deterministic and acts on
   each file alone, so `apply(HEAD)` differs from `apply(PRE)` exactly by the branch's own
   changes, converted, and `--onto` differs from `apply(PRE)` by the hand edits of the rename
   commit (and any later commits). Only those can conflict.
3. Apply mode runs again on the result as a safety net (it is normally a no-op), and the
   aggregates are regenerated.
4. The merge is committed with parents HEAD and `--onto`. When files conflict, the merge is left
   in progress with conflict markers instead: resolve, `git add` and `git commit`.
5. A summary lists the branch's changed files and those needing attention: conflicts, and
   remaining old-root tokens in the branch's changed files.

The tool never pushes, fetches or rewrites existing commits. Converted trees are cached in the Git
directory (`rename-module-root/`), keyed by commit and by this script's own digest.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from proof_lengths import masks  # noqa: E402  (the shared Lean comment and string lexer)

TOOL = Path(__file__).resolve()

# (old root, new root, source directory). Longest first, so that alternations prefer them.
ROOTS = (
    ("ComplexityComparatorChallenges", "CslibFrontierComparatorChallenges", "comparator"),
    ("ComplexityComparator", "CslibFrontierComparator", "comparator"),
    ("ComplexityAbstracts", "CslibFrontierAbstracts", "abstracts"),
    ("ComplexityGuideMain", "CslibFrontierGuideMain", "guide"),
    ("ComplexityGuide", "CslibFrontierGuide", "guide"),
    ("ComplexityResults", "CslibFrontierResults", ""),
    ("ComplexityTests", "CslibFrontierTests", ""),
    ("Complexity", "CslibFrontier", ""),
)
NEW_ROOT = {old: new for old, new, _ in ROOTS}
SOURCE_DIR = {old: src for old, _, src in ROOTS}
OLD_LIB, NEW_LIB = "Complexity", "CslibFrontier"
# A tree is post-rename exactly when it has this file.
MARKER = "CslibFrontier.lean"
PRE_MARKER = "Complexity.lean"

OLD_PACKAGE, NEW_PACKAGE = "complexitylib", "cslib-frontier"
OLD_REPOSITORY, NEW_REPOSITORY = "cslib-community/complexitylib", "cslib-community/cslib-frontier"
OLD_SITE, NEW_SITE = "cslib.io/complexitylib", "cslib.io/cslib-frontier"

# Never rewritten: bibliography titles, this tool and its tests (which spell both names), the
# documentation site's redirect page, and the cloud setup script (bucket, project and identity
# names; the shared cache's storage keys must not change).
EXCLUDED = frozenset({
    "references.bib",
    "scripts/rename_module_root.py",
    "scripts/test_rename_module_root.py",
    "docbuild/404.html",
    "scripts/cache/setup-gcs.sh",
})
# Historical analyses of the pinned snapshot: only URLs change.
URL_ONLY = ("manual/development-history/", "manual/data/")
# Tooling sources: their dotted root tokens are module names even for nonexistent (fixture) modules.
TOOLING_SUFFIXES = (".py", ".sh", ".cjs", ".js", ".yml", ".yaml")
PRAGMA = "rename-module-root: keep"
# Roots that tooling fixtures use for nonexistent modules. The others (`ComplexityTests.*`, ...)
# are also namespaces of test and abstract declarations, so only existing modules are renamed.
FIXTURE_ROOTS = ("Complexity", "ComplexityAbstracts")

# Module name components; a `'` after a token makes it a Lean identifier, not a module name.
IDENT = r"[A-Za-z_][A-Za-z0-9_]*"
# Not inside a longer identifier; an escape such as `\n` or regex `\b` before a root is a boundary.
ROOT_TOKEN = re.compile(r"(?:(?<![A-Za-z0-9_])|(?<=\\[nrtb]))("
                        + "|".join(old for old, _, _ in ROOTS) + r")(?![A-Za-z0-9_])")
DOTTED_REST = re.compile(rf"(?:\.{IDENT})*")
# In tooling: `Complexity.{name}` (format strings), `Complexity\.` (regexes), `(?:Complexity|`.
TOOLING_AFTER = re.compile(r"\.\{|\\\.|[|)(]")
EXTENSIONS = frozenset({"lean", "html", "ilean", "olean", "json", "jsonl", "md", "trace", "hash"})
# "`Complexity` modules", "the Complexity library", ...
PHRASE_AFTER = re.compile(r"[ \t]+(?:modules?|librar(?:y|ies)|roots?|declarations?|targets?|"
                          r"package|tree|director(?:y|ies)|aggregat(?:or|e)s?|sources?|files?)\b")
# A command line that takes the root as a directory or target argument.
COMMAND = re.compile(r"(?:^|[\s`$(])(?:lake|rg|grep|git|find|ls|wc|du|cd)\s", re.M)
IMPORT_BEFORE = re.compile(r"\bimport\s+(?:all\s+)?$")
# Verso's references to a chapter's module: `%doc M` and `{include N M}`.
VERSO_MODULE_BEFORE = re.compile(r"(?:%doc|\{include[ \t]+\d+)[ \t]+$")
QUOTES = "`\"'"
URL_RULES = (
    (re.compile(r"(?<=github\.com/)cslib-community/complexitylib(?![\w-])"), NEW_REPOSITORY),
    (re.compile(r"(?<=cslib\.io/)complexitylib(?![\w-])"), NEW_PACKAGE),
)
PACKAGE_RULES = (
    (re.compile(r'(?<=name = ")complexitylib(?=")'), NEW_PACKAGE),
    (re.compile(r'(?<="name": ")complexitylib(?=")'), NEW_PACKAGE),
    (re.compile(r"(?<![\w/.-])@complexitylib(?![\w-])"), "@" + NEW_PACKAGE),
)
UPDATE_LINE = re.compile(r"\blake\b[^\n]*\bupdate\b")
UPDATE_PACKAGE = re.compile(r"(?<![\w/.-])complexitylib(?![\w-])")
# Path contexts after a `/` in which a root still starts the path.
PATH_PREFIXES = ("blob/main", "tree/main", "edit/main", "raw/main", "blame/main", "commits/main",
                 NEW_SITE, OLD_SITE, "build/doc", "lib/lean", "build/ir")
SEGMENT = re.compile(r"[^\s/\"'`()<>\[\]{},;=|*]*\Z")
SHELL_VARIABLE = re.compile(r"\$\{?\w+\}?")

MODULE_PREAMBLE = "module  -- shake: keep-all --deprecated_module: ignore\n\n"


class ToolError(Exception):
    pass


# --- The rewriting rules -------------------------------------------------------------------------

@dataclass
class Inventory:
    """Module names (old spelling) of a tree, with their directories and `Complexity/` areas."""
    modules: set[str] = field(default_factory=set)
    dirs: set[str] = field(default_factory=set)
    areas: set[str] = field(default_factory=set)

    @classmethod
    def from_paths(cls, paths) -> "Inventory":
        inv = cls()
        for path in paths:
            if not path.endswith(".lean"):
                continue
            parts = path[:-5].split("/")
            for old, new, src in ROOTS:
                prefix = src.split("/") if src else []
                if parts[:len(prefix)] == prefix and len(parts) > len(prefix) and \
                        parts[len(prefix)] in (old, new):
                    names = [old] + parts[len(prefix) + 1:]
                    break
            else:
                continue
            inv.modules.add(".".join(names))
            for i in range(1, len(names)):
                inv.dirs.add(".".join(names[:i]))
            if names[0] == OLD_LIB and len(names) > 1:
                inv.areas.add(names[1])
        return inv

    def known(self, name: str) -> bool:
        return name in self.modules or name in self.dirs or name in NEW_ROOT


HEADER_KEYWORDS = frozenset({"module", "prelude", "public", "private", "meta", "import", "all"})
HEADER_MODULE = re.compile(r"[\w.«»']+")


def lean_regions(text: str):
    """Classify each offset of a Lean file: `c` code, `m` comment, `s` string literal, and `h` the
    module header (`module`, and the `import` commands, which may span lines)."""
    code, syntax = masks(text)
    header_end = len(text)
    previous = None
    for token in re.finditer(r"\S+", syntax):
        word = token.group(0)
        if previous == "import" and word == "all":
            previous = "all"
        elif previous in ("import", "all"):
            if not HEADER_MODULE.fullmatch(word):
                header_end = token.start()
                break
            previous = "name"  # one module per `import` command
        elif word in HEADER_KEYWORDS:
            previous = word
        else:
            header_end = token.start()
            break

    def kind(i: int) -> str:
        if syntax[i] == text[i]:
            return "h" if i < header_end else "c"
        return "m" if code[i] != text[i] else "s"
    return kind


# Mathlib's `linter.style.longLine` limit, which the library's `mathlibStandardSet` enables.
MAX_LINE = 100
LIST_ITEM = re.compile(r"[ \t]*(?:/-[-!]?[ \t]*)?(?:[-*+][ \t]+|\d+[.)][ \t]+)?")
# A continuation must not start a new Markdown block.
BLOCK_START = re.compile(r"(?:[-*+][ \t]|\d+[.)][ \t]|#|>|\||```|=+$|-+$|-/)")


def wrap_lengthened_lines(before: str, after: str) -> str:
    """Re-wrap the lines of a Lean file that the rewriting pushed past `MAX_LINE`.

    A lengthened comment line is split at spaces into lines within the limit, continuing at the
    indentation of its text (after a docstring opener or list marker), or as `-- ` comments. A
    module name that continues an `import` line joins it, since import lines are exempt. Lines in
    code, fenced code blocks or tables, lines with URLs, and `#guard_msgs` expectations (whose
    whitespace can matter) are left alone; the long-line linter reports them."""
    old_lines, new_lines = before.split("\n"), after.split("\n")
    if len(old_lines) != len(new_lines) or not any(
            len(n) > MAX_LINE and n != o for o, n in zip(old_lines, new_lines)):
        return after
    kind = lean_regions(after)
    out: list[str] = []
    offset, fenced = 0, False
    for old, line in zip(old_lines, new_lines):
        start = offset + len(line) - len(line.lstrip())
        offset += len(line) + 1
        stripped = line.strip()
        if stripped.startswith("```") and kind(start) == "m":
            fenced = not fenced
        if (line != old and len(line) > MAX_LINE and stripped and kind(start) == "h" and out
                and re.search(r"\bimport(?:\s+all)?\s*$", out[-1])):
            out[-1] = out[-1].rstrip() + " " + stripped
            continue
        if (line == old or len(line) <= MAX_LINE or fenced or "http" in line or
                not stripped or kind(start) != "m" or stripped.startswith("|") or
                guard_msgs_follows(after, offset - len(line) - 1, kind)):
            out.append(line)
            continue
        out += wrap_line(line)
    return "\n".join(out)


def guard_msgs_follows(text: str, line_start: int, kind) -> bool:
    """Whether the comment holding the line at `line_start` is followed by `#guard_msgs`."""
    if text[line_start:].lstrip().startswith("--"):
        end = text.find("\n", line_start)
    else:
        end = text.find("-/", line_start)
        while end != -1 and kind(end) != "m":
            end = text.find("-/", end + 1)
        end = -1 if end == -1 else end + 2
    return end != -1 and text[end:].lstrip().startswith("#guard_msgs")


def wrap_line(line: str) -> list[str]:
    """Split a comment line at spaces into lines within `MAX_LINE`."""
    if line.lstrip().startswith("--"):
        prefix = line[:len(line) - len(line.lstrip())] + "-- "
    elif line.lstrip().startswith(("/--", "/-!")):
        prefix = line[:len(line) - len(line.lstrip())]
    else:
        prefix = " " * len(LIST_ITEM.match(line).group(0).expandtabs())
    lines = []
    while len(line) > MAX_LINE:
        for cut in range(MAX_LINE, len(prefix), -1):
            rest = line[cut:].lstrip()
            if line[cut] == " " and line[:cut].strip() and rest and not BLOCK_START.match(rest):
                break
        else:
            break
        lines.append(line[:cut].rstrip())
        line = prefix + rest
    return lines + [line]


class Rewriter:
    def __init__(self, inventory: Inventory):
        self.inv = inventory

    # Each rule returns the replacement of the root token or None.
    def text_rule(self, text: str, s: int, e: int, root: str, tooling: bool) -> str | None:
        """A root token in prose, a comment, a string or a non-Lean file."""
        c = text[s - 1] if s else "\n"
        if c in ".-@$\\":
            return None
        if c == "/":
            before = text[max(0, s - 400):s - 1]
            segment = SEGMENT.search(before).group(0)
            if not (segment in ("", ".", "..")
                    or (SOURCE_DIR[root] and segment == SOURCE_DIR[root])
                    or before.endswith(PATH_PREFIXES) or SHELL_VARIABLE.fullmatch(segment)):
                return None
        rest = DOTTED_REST.match(text, e).group(0)
        new = NEW_ROOT[root]
        if text[e + len(rest):e + len(rest) + 1] == "'" and not tooling and c != "'":
            return None  # a Lean identifier such as `Complexity.foo'`
        if rest:
            parts = rest[1:].split(".")
            full = root + rest
            if parts[-1] in EXTENSIONS and self.inv.known(full[:-len(parts[-1]) - 1]):
                return new
            if self.inv.known(full):
                return new
            if root == OLD_LIB and parts[0] in self.inv.areas:
                return new
            if tooling and root in FIXTURE_ROOTS and parts[0][:1].isupper():
                return new  # a fixture module
            return None
        nxt = text[e:e + 1]
        if nxt == "/":
            return new
        if nxt == ":" and re.match(r":[a-z]", text[e:e + 2]):
            return new  # a Lake facet such as `Complexity:docs`
        if nxt == "." and text[e + 1:e + 2] and text[e + 1:e + 2] in QUOTES + "*":
            return new  # "`Complexity.`", the module prefix, or the glob `Complexity.*`
        if tooling and TOOLING_AFTER.match(text, e) and \
                (nxt != "|" and nxt != ")" or text[s - 3:s] == "(?:" or c == "|"):
            return new
        line_start = text.rfind("\n", 0, s) + 1
        if IMPORT_BEFORE.search(text, line_start, s):
            return new
        if root != OLD_LIB:
            return new  # the other roots are not English words
        if c in QUOTES and nxt == c:
            return new
        if PHRASE_AFTER.match(text, e):
            return new
        if c in " \t" and (nxt in " \t\n`'\")" or not nxt) and COMMAND.search(text, line_start, s):
            return new
        return None

    def code_rule(self, text: str, s: int, e: int, root: str) -> str | None:
        """A root token in Lean code after the header: module-name literals and Verso's module
        references."""
        c = text[s - 1] if s else "\n"
        if c == ".":
            return None
        line_start = text.rfind("\n", 0, s) + 1
        rest = DOTTED_REST.match(text, e).group(0)
        full = root + rest
        if c == "`" and text[s - 2:s - 1] != "`" and (not rest or self.inv.known(full)):
            return NEW_ROOT[root]
        if VERSO_MODULE_BEFORE.search(text, line_start, s) and self.inv.known(full):
            return NEW_ROOT[root]
        if root == OLD_LIB and rest and full in self.inv.modules:
            # A module named in code, such as an audit's allow-list. `Cslib.Complexity.*`
            # declarations are written `Complexity.P` inside `namespace Cslib`, but no module
            # shares such a name; the other roots are also namespaces, so they are left alone.
            return NEW_ROOT[root]
        return None

    def rewrite(self, path: str, text: str) -> str:
        if path in EXCLUDED:
            return text
        text = self.rewrite_lines(text, lambda t: self.rewrite_urls(t))
        if path.startswith(URL_ONLY):
            return text
        text = self.rewrite_lines(text, self.rewrite_package)
        new = self.rewrite_lines(text, lambda t: self.rewrite_roots(path, t))
        if path.endswith(".lean") and new != text:
            new = wrap_lengthened_lines(text, new)
        return new

    @staticmethod
    def rewrite_lines(text: str, rule) -> str:
        """Apply `rule` to the text, except on lines that carry the pragma."""
        if PRAGMA not in text:
            return rule(text)
        lines = text.split("\n")
        kept = {i: line for i, line in enumerate(lines) if PRAGMA in line}
        out = rule("\n".join("" if i in kept else line for i, line in enumerate(lines))).split("\n")
        if len(out) != len(lines):
            raise ToolError("a rule changed the number of lines")
        return "\n".join(kept.get(i, line) for i, line in enumerate(out))

    @staticmethod
    def rewrite_urls(text: str) -> str:
        for pattern, replacement in URL_RULES:
            text = pattern.sub(replacement, text)
        return text

    @staticmethod
    def rewrite_package(text: str) -> str:
        for pattern, replacement in PACKAGE_RULES:
            text = pattern.sub(replacement, text)
        if "complexitylib" in text and UPDATE_LINE.search(text):
            text = "\n".join(UPDATE_PACKAGE.sub(NEW_PACKAGE, line) if UPDATE_LINE.search(line)
                             else line for line in text.split("\n"))
        return text

    def rewrite_roots(self, path: str, text: str) -> str:
        matches = list(ROOT_TOKEN.finditer(text))
        if not matches:
            return text
        tooling = path.endswith(TOOLING_SUFFIXES)
        kind = None
        prose_from = len(text) + 1
        if path.endswith(".lean"):
            kind = lean_regions(text)
            if path.startswith("guide/"):
                doc = re.search(r"^#doc\b", text, re.M)
                prose_from = doc.start() if doc else prose_from
        out, last = [], 0
        for match in matches:
            s, e, root = match.start(), match.end(), match.group(1)
            region = kind(s) if kind else "t"
            if region == "h":
                new = NEW_ROOT[root] if text[s - 1:s] != "." else None
            elif region != "c" or s >= prose_from:
                new = self.text_rule(text, s, e, root, tooling)
            else:
                new = self.code_rule(text, s, e, root)
            if new is not None:
                out += [text[last:s], new]
                last = e
        out.append(text[last:])
        return "".join(out)

    def residue(self, path: str, text: str):
        """Old-root tokens that remain after rewriting, with a classification."""
        if path in EXCLUDED or path.startswith(URL_ONLY):
            return
        kind = lean_regions(text) if path.endswith(".lean") else None
        for match in ROOT_TOKEN.finditer(text):
            s, e, root = match.start(), match.end(), match.group(1)
            c = text[s - 1] if s else "\n"
            rest = DOTTED_REST.match(text, e).group(0)
            line = text.count("\n", 0, s) + 1
            if c == ".":
                continue  # a namespace component such as `Cslib.Complexity`
            where = "text" if kind is None else \
                {"c": "code", "h": "header", "m": "comment", "s": "string"}[kind(s)]
            if c == "/":
                category = "nested path component"
            elif rest:
                category = "declaration or namespace" if (rest[1:2].islower() or where == "code") \
                    else "dotted name, not a module"
            else:
                category = "bare word"
            yield line, where, category, root + rest


# --- Git helpers ---------------------------------------------------------------------------------

def git(repo: Path, *args: str, check: bool = True, env: dict | None = None,
        input: str | None = None) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(["git", "-C", str(repo), *args], capture_output=True, text=True,
                            env={**os.environ, **(env or {})}, input=input)
    if check and result.returncode != 0:
        raise ToolError(f"git {' '.join(args)} failed:\n{result.stderr.strip()}")
    return result


def tracked(repo: Path) -> list[str]:
    out = git(repo, "ls-files", "-z").stdout
    return list(dict.fromkeys(p for p in out.split("\0") if p))


def has_path(repo: Path, rev: str, path: str) -> bool:
    return git(repo, "cat-file", "-e", f"{rev}:{path}", check=False).returncode == 0


def rev(repo: Path, ref: str) -> str:
    return git(repo, "rev-parse", "--verify", f"{ref}^{{commit}}").stdout.strip()


def is_ancestor(repo: Path, a: str, b: str) -> bool:
    return git(repo, "merge-base", "--is-ancestor", a, b, check=False).returncode == 0


# --- Apply mode ----------------------------------------------------------------------------------

def move_roots(repo: Path, files: list[str]) -> list[tuple[str, str]]:
    """`git mv` every tracked file below an old root to the new root. Returns the moves."""
    moves: list[tuple[str, str]] = []
    existing = set(files)
    for old, new, src in ROOTS:
        base = f"{src}/" if src else ""
        old_dir, new_dir = f"{base}{old}/", f"{base}{new}/"
        below = [p for p in files if p.startswith(old_dir)]
        if below:
            if not any(p.startswith(new_dir) for p in existing) and not (repo / new_dir).exists():
                git(repo, "mv", old_dir.rstrip("/"), new_dir.rstrip("/"))
            else:
                by_target: dict[str, list[str]] = {}
                for p in below:
                    target = new_dir + p[len(old_dir):]
                    if target in existing:
                        raise ToolError(f"cannot move {p}: {target} exists")
                    by_target.setdefault(os.path.dirname(target), []).append(p)
                for directory, sources in sorted(by_target.items()):
                    (repo / directory).mkdir(parents=True, exist_ok=True)
                    for i in range(0, len(sources), 200):
                        git(repo, "mv", *sources[i:i + 200], directory + "/")
            moves += [(p, new_dir + p[len(old_dir):]) for p in below]
        old_file, new_file = f"{base}{old}.lean", f"{base}{new}.lean"
        if old_file in existing:
            if new_file in existing:
                # Both exist after a merge: the aggregate is regenerated, and a hand-written root
                # (the guide's) needs a person.
                git(repo, "rm", "-q", old_file)
                print(f"note: removed {old_file}; {new_file} already exists", file=sys.stderr)
            else:
                git(repo, "mv", old_file, new_file)
                moves.append((old_file, new_file))
    # Directories left empty by per-file moves.
    for old, _, src in ROOTS:
        root_dir = repo / (f"{src}/{old}" if src else old)
        if root_dir.is_dir():
            for directory in sorted(root_dir.rglob("*"), key=lambda p: -len(p.parts)):
                if directory.is_dir() and not any(directory.iterdir()):
                    directory.rmdir()
            if not any(root_dir.iterdir()):
                root_dir.rmdir()
    return moves


def rewrite_files(repo: Path, files: list[str], rewriter: Rewriter) -> list[str]:
    changed = []
    for path in files:
        full = repo / path
        if path in EXCLUDED or full.is_symlink() or not full.is_file():
            continue
        data = full.read_bytes()
        if b"\0" in data:
            continue
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError:
            continue
        new = rewriter.rewrite(path, text)
        if new != text:
            full.write_bytes(new.encode("utf-8"))
            changed.append(path)
    return changed


def lake_libraries(repo: Path) -> list[dict]:
    config = tomllib.loads((repo / "lakefile.toml").read_text())
    return [lib for lib in config.get("lean_lib", []) if isinstance(lib, dict)]


def regenerate_aggregates(repo: Path) -> list[str]:
    """Write what `lake exe mk_all` writes: for each root of each `lean_lib`, the sorted imports
    of every module below it, in the style of the existing file. Returns the changed files."""
    files = tracked(repo)
    changed = []
    for lib in lake_libraries(repo):
        src = lib.get("srcDir", ".").strip("/")
        prefix = "" if src in ("", ".") else src + "/"
        for root in lib.get("roots", [lib.get("name")]):
            if not root:
                continue
            aggregate = f"{prefix}{root.replace('.', '/')}.lean"
            target = repo / aggregate
            if not target.is_file():
                continue
            below = f"{prefix}{root.replace('.', '/')}/"
            modules = sorted(p[len(prefix):-5].replace("/", ".") for p in files
                             if p.startswith(below) and p.endswith(".lean")
                             and (repo / p).is_file())
            existing = target.read_text()
            module_style = existing.lstrip().startswith("module")
            if module_style:
                content = MODULE_PREAMBLE + "".join(f"public import {m}\n" for m in modules)
            else:
                content = "".join(f"import {m}\n" for m in modules)
            if content != existing:
                target.write_text(content)
                changed.append(aggregate)
    return changed


def aggregate_paths(repo: Path) -> set[str]:
    paths = set()
    for lib in lake_libraries(repo):
        src = lib.get("srcDir", ".").strip("/")
        prefix = "" if src in ("", ".") else src + "/"
        for root in lib.get("roots", [lib.get("name")]):
            if root:
                paths.add(f"{prefix}{root.replace('.', '/')}.lean")
    return paths


def apply(repo: Path, mk_all: bool = False, quiet: bool = False) -> list[str]:
    """Rename the roots of the checkout at `repo` and rewrite its files. Returns changed paths."""
    files = tracked(repo)
    rewriter = Rewriter(Inventory.from_paths(files))
    moves = move_roots(repo, files)
    files = tracked(repo)
    changed = rewrite_files(repo, files, rewriter)
    changed += regenerate_aggregates(repo)
    if mk_all:
        # `mk_all` exits with the number of files it changed; after the regeneration above it
        # should change none.
        result = subprocess.run(["lake", "exe", "mk_all"], cwd=repo, capture_output=True,
                                text=True)
        if result.returncode != 0:
            raise ToolError(f"lake exe mk_all changed files or failed:\n{result.stdout}"
                            f"{result.stderr}")
    git(repo, "add", "-u")
    if not quiet:
        print(f"moved {len(moves)} files, rewrote {len(set(changed))} files")
    return sorted(set(changed) | {n for _, n in moves})


def report(repo: Path) -> int:
    rewriter = Rewriter(Inventory.from_paths(tracked(repo)))
    counts: dict[tuple[str, str], int] = {}
    for path in tracked(repo):
        full = repo / path
        if not full.is_file() or full.is_symlink():
            continue
        data = full.read_bytes()
        if b"\0" in data:
            continue
        try:
            text = data.decode("utf-8")
        except UnicodeDecodeError:
            continue
        for line, where, category, token in rewriter.residue(path, text):
            counts[(where, category)] = counts.get((where, category), 0) + 1
            print(f"{path}:{line}: {where}: {category}: {token}")
    for (where, category), n in sorted(counts.items()):
        print(f"# {n:6d}  {where}: {category}", file=sys.stderr)
    return 0


# --- Restack mode --------------------------------------------------------------------------------

def tool_digest() -> str:
    h = hashlib.sha256(TOOL.read_bytes())
    h.update((TOOL.parent / "proof_lengths.py").read_bytes())
    return h.hexdigest()[:16]


def state_dir(repo: Path) -> Path:
    common = Path(git(repo, "rev-parse", "--path-format=absolute", "--git-common-dir").stdout.strip())
    path = common / "rename-module-root"
    path.mkdir(exist_ok=True)
    return path


def converted_tree(repo: Path, commit: str) -> str:
    """The tree of `apply(commit)`, computed in a temporary worktree and cached."""
    state = state_dir(repo)
    cache_file = state / "trees.json"
    try:
        cache = json.loads(cache_file.read_text())
    except (OSError, ValueError):
        cache = {}
    key = f"{commit}:{tool_digest()}"
    tree = cache.get(key)
    if tree and git(repo, "cat-file", "-e", tree, check=False).returncode == 0:
        return tree
    work = state / f"work-{commit[:12]}-{os.getpid()}"
    git(repo, "worktree", "add", "-q", "--detach", str(work), commit)
    try:
        apply(work, mk_all=False, quiet=True)
        tree = git(work, "write-tree").stdout.strip()
    finally:
        git(repo, "worktree", "remove", "--force", str(work), check=False)
        shutil.rmtree(work, ignore_errors=True)
    cache[key] = tree
    cache_file.write_text(json.dumps(cache, indent=1, sort_keys=True))
    return tree


SCRATCH_IDENTITY = {"GIT_AUTHOR_NAME": "rename-module-root", "GIT_COMMITTER_NAME": "rename-module-root",
                    "GIT_AUTHOR_EMAIL": "rename-module-root@invalid",
                    "GIT_COMMITTER_EMAIL": "rename-module-root@invalid",
                    "GIT_AUTHOR_DATE": "2026-11-08T00:00:00Z",
                    "GIT_COMMITTER_DATE": "2026-11-08T00:00:00Z"}


def scratch_commit(repo: Path, tree: str) -> str:
    """A parentless commit of `tree`, unreferenced, for `git merge-tree`."""
    return git(repo, "commit-tree", tree, "-m", "rename-module-root scratch",
               env=SCRATCH_IDENTITY).stdout.strip()


def find_rename_commit(repo: Path, ref: str) -> str:
    out = git(repo, "log", "--first-parent", "--diff-filter=A", "--format=%H", ref, "--",
              MARKER).stdout.split()
    if not out:
        raise ToolError(f"{ref} has no commit that adds {MARKER}; pass --onto")
    return out[-1]


def pre_rename_counterpart(repo: Path, onto: str) -> str:
    commit = onto
    while has_path(repo, commit, MARKER):
        parents = git(repo, "rev-list", "--parents", "-n", "1", commit).stdout.split()[1:]
        if not parents:
            raise ToolError(f"no pre-rename first-parent ancestor of {onto}")
        commit = parents[0]
    if not has_path(repo, commit, PRE_MARKER):
        raise ToolError(f"{commit} has neither {MARKER} nor {PRE_MARKER}")
    return commit


def unmerged(repo: Path) -> list[str]:
    out = git(repo, "diff", "--name-only", "--diff-filter=U", "-z").stdout
    return sorted({p for p in out.split("\0") if p})


def merge_drivers() -> list[str]:
    scripts = TOOL.parent
    return ["-c", f"merge.leanagg.driver=python3 {scripts / 'resolve_aggregate_conflict.py'} %O %A %B",
            "-c", f"merge.bibkeys.driver=python3 {scripts / 'resolve_bib_conflict.py'} --driver %O %A %B"]


def residual_report(repo: Path, paths: list[str]) -> list[str]:
    rewriter = Rewriter(Inventory.from_paths(tracked(repo)))
    lines = []
    for path in paths:
        full = repo / path
        if not full.is_file():
            continue
        try:
            text = full.read_text()
        except (UnicodeDecodeError, OSError):
            continue
        for line, where, category, token in rewriter.residue(path, text):
            if category in ("dotted name, not a module",) or \
                    (category == "bare word" and where != "code" and token != OLD_LIB):
                lines.append(f"{path}:{line}: {where}: {category}: {token}")
    return lines


def restack(repo: Path, onto_ref: str | None, upstream: str, mk_all: bool) -> int:
    if git(repo, "status", "--porcelain", "--untracked-files=no").stdout.strip():
        raise ToolError("the working tree has uncommitted changes")
    gitdir = Path(git(repo, "rev-parse", "--path-format=absolute", "--git-dir").stdout.strip())
    if (gitdir / "MERGE_HEAD").exists():
        raise ToolError("a merge is in progress; commit or abort it first")
    head = rev(repo, "HEAD")
    onto = rev(repo, onto_ref) if onto_ref else find_rename_commit(repo, upstream)
    if not has_path(repo, onto, MARKER):
        raise ToolError(f"--onto {onto[:12]} is not a post-rename commit")
    branch = git(repo, "rev-parse", "--abbrev-ref", "HEAD").stdout.strip()
    if is_ancestor(repo, onto, head):
        print(f"{onto[:12]} is already merged; converting any remaining old names.")
        changed = apply(repo, mk_all=mk_all, quiet=True)
        if changed:
            git(repo, "commit", "-q", "-m", "chore: convert remaining module names to "
                f"{NEW_LIB}\n\nscripts/rename_module_root.py --restack")
            print(f"committed conversions of {len(changed)} files")
        return 0
    if has_path(repo, head, MARKER):
        raise ToolError("HEAD is already post-rename; merge the newer commit with plain git merge")
    pre = pre_rename_counterpart(repo, onto)
    print(f"branch {branch} at {head[:12]}; onto {onto[:12]}; pre-rename counterpart {pre[:12]}")

    # 1. The pre-rename counterpart.
    if not is_ancestor(repo, pre, head):
        result = git(repo, *merge_drivers(), "merge", "--no-ff", "--no-edit", "-m",
                     f"Merge {pre[:12]} (main before the module-root rename) into {branch}", pre,
                     check=False)
        if result.returncode != 0:
            conflicts = unmerged(repo)
            aggregates = aggregate_paths(repo)
            if not conflicts:
                raise ToolError(f"merging {pre[:12]} failed:\n{result.stderr.strip()}")
            if set(conflicts) <= aggregates:
                regenerate_aggregates_from_worktree(repo, conflicts)
                git(repo, "commit", "-q", "--no-edit")
            else:
                print("Merging the pre-rename main conflicts in:")
                for path in conflicts:
                    print(f"  {path}")
                print("Resolve, `git add` and `git commit` this merge, then run --restack again.")
                return 3
        head = rev(repo, "HEAD")
        print(f"merged the pre-rename main: {head[:12]}")

    # 2. The rename, as a three-way merge of converted trees.
    base_tree = converted_tree(repo, pre)
    ours_tree = converted_tree(repo, head)
    onto_tree = git(repo, "rev-parse", f"{onto}^{{tree}}").stdout.strip()
    # Git before 2.45 merges only commits, so the converted trees are wrapped in parentless ones.
    base_commit, ours_commit = (scratch_commit(repo, t) for t in (base_tree, ours_tree))
    merge = git(repo, *merge_drivers(), "-c", f"attr.tree={onto_tree}", "merge-tree",
                "--write-tree", "-z", f"--merge-base={base_commit}", ours_commit, onto,
                check=False)
    if merge.returncode not in (0, 1):
        raise ToolError(f"git merge-tree failed:\n{merge.stderr.strip()}")
    fields = merge.stdout.split("\0")
    result_tree = fields[0]
    stages = []
    for entry in fields[1:]:
        if not entry:
            break
        stages.append(entry)  # "<mode> <object> <stage>\t<path>"

    git(repo, "merge", "--no-ff", "--no-commit", "-s", "ours", onto, check=True,
        env={"GIT_MERGE_AUTOEDIT": "no"})
    git(repo, "read-tree", "-u", "--reset", result_tree)
    conflicted = sorted({s.split("\t", 1)[1] for s in stages})
    aggregates = aggregate_paths(repo)
    if stages:
        git(repo, "update-index", "--index-info",
            input="".join(f"0 {'0' * 40}\t{p}\n" for p in conflicted)
            + "".join(f"{s}\n" for s in stages))
    real_conflicts = [p for p in conflicted if p not in aggregates]
    agg_conflicts = [p for p in conflicted if p in aggregates]
    if agg_conflicts:
        regenerate_aggregates_from_worktree(repo, agg_conflicts)

    # 3. Safety net and aggregates.
    if not real_conflicts:
        extra = apply(repo, mk_all=mk_all, quiet=True)
        message = (f"Merge the module-root rename ({onto[:12]}) into {branch}\n\n"
                   f"Restacked with scripts/rename_module_root.py --restack: the branch's changes,\n"
                   f"with module names and paths converted, merged with the renamed tree.\n")
        git(repo, "commit", "-q", "--no-verify", "-F", "-", input=message)
        if extra:
            print("note: the safety-net conversion changed these files (review them):")
            for path in extra:
                print(f"  {path}")
    head2 = rev(repo, "HEAD") if not real_conflicts else None

    # 4. Summary.
    changed = git(repo, "diff", "--name-only", "-z", onto, "HEAD" if head2 else "--").stdout
    changed_paths = sorted({p for p in changed.split("\0") if p})
    print(f"\nThe branch changes {len(changed_paths)} files relative to {onto[:12]}.")
    attention = residual_report(repo, changed_paths)
    if real_conflicts:
        print("\nCONFLICTS (the merge is in progress; resolve, `git add`, `git commit`):")
        for path in real_conflicts:
            print(f"  {path}")
    if agg_conflicts:
        print("\nregenerated aggregates: " + ", ".join(agg_conflicts))
    if attention:
        print("\nOld-root tokens left in the branch's files (check whether they name modules):")
        for line in attention:
            print(f"  {line}")
    if head2:
        print(f"\nrestacked: {head2}")
    return 4 if real_conflicts else 0


def regenerate_aggregates_from_worktree(repo: Path, paths: list[str]) -> None:
    """Resolve conflicted aggregates by regenerating them from the merged tree."""
    for path in paths:
        entries = [e for e in git(repo, "ls-files", "-u", "-z", "--", path).stdout.split("\0") if e]
        text = git(repo, "cat-file", "-p", entries[-1].split()[1]).stdout if entries else ""
        # A placeholder in the side's style; the regeneration below writes the content.
        (repo / path).write_text(MODULE_PREAMBLE if text.startswith("module") else "")
        git(repo, "add", "--", path)
    regenerate_aggregates(repo)
    git(repo, "add", "--", *paths)


# --- Command line --------------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="checkout (default: .)")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--restack", action="store_true", help="merge the rename into this branch")
    mode.add_argument("--report", action="store_true", help="list the old-root tokens that remain")
    parser.add_argument("--onto", help="post-rename commit to merge (default: the rename commit)")
    parser.add_argument("--upstream", default="origin/main",
                        help="where to find the rename commit (default: origin/main)")
    mk = parser.add_mutually_exclusive_group()
    mk.add_argument("--no-mk-all", action="store_true", help="apply mode: skip `lake exe mk_all`")
    mk.add_argument("--mk-all", action="store_true", help="restack mode: run `lake exe mk_all`")
    args = parser.parse_args(argv)
    repo = Path(git(args.repo, "rev-parse", "--show-toplevel").stdout.strip())
    try:
        if args.report:
            return report(repo)
        if args.restack:
            return restack(repo, args.onto, args.upstream, args.mk_all)
        apply(repo, mk_all=not args.no_mk_all)
        return 0
    except ToolError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
