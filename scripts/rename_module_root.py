#!/usr/bin/env python3
"""Rename the Lean module root `Complexity` to `CslibFrontier`, and restack branches across it.

The roots other than `Complexity` (`ComplexityTests`, `ComplexityResults`, `ComplexityScripts`,
`ComplexityAbstracts`, `ComplexityComparator*`, `ComplexityGuide*`) are this project's own names,
so every occurrence becomes its `CslibFrontier…` counterpart: module names and paths, and also
namespaces, qualified declaration names, name literals, messages and prose. Only `Complexity`
itself keeps a distinction between modules and declarations, since `Cslib.Complexity.*` (also
written `Complexity.*` inside `namespace Cslib`) is a CSLib namespace: for it the rename changes
module names and source paths only, and no identifier in Lean code.

Apply mode (the default) transforms the checkout in the current directory in place:

    python3 scripts/rename_module_root.py [--no-mk-all]

1. `git mv` renames the roots: `Complexity/` and `Complexity.lean` become `CslibFrontier/` and
   `CslibFrontier.lean`; likewise `ComplexityTests`, `ComplexityResults`, `ComplexityAbstracts`,
   `ComplexityComparator*` and the guide's `ComplexityGuide*` (each where it exists).
2. Every tracked text file is rewritten, except `EXCLUDED` and lines carrying the pragma
   `rename-module-root: keep`. Sibling roots are renamed wherever they occur as whole tokens,
   except in a path inside a permalink to a fixed commit. For `Complexity`, the rules
   (`Rewriter`) touch only
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
   Python and shell sources are tooling, whose dotted `Complexity.X` tokens are module names even
   when the module does not exist (test fixtures), so they are rewritten too. Comment lines that
   the longer names push past 100 columns are re-wrapped, and `FIXUPS` makes the few edits that
   no rule can.
   `manual/history/` (formerly `manual/development-history/`) and `manual/data/` describe and
   analyse the pinned historical snapshot, so only their URLs change.
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
   with it. The tree is therefore a three-way merge of converted trees: base `apply(PRE)`, ours
   `apply(HEAD)` and theirs `--onto`. `apply(PRE)` is computed once in a temporary worktree and
   cached; `apply(HEAD)` is `apply(PRE)` with only the files that HEAD changes relative to `PRE`
   converted (paths mapped, contents rewritten), so it differs from the base exactly by the
   branch's own changes, and `--onto` differs from it by the rename commit's hand edits (and any
   later commits). Only those can conflict. The aggregates are regenerated.
3. The merge is committed with parents HEAD and `--onto`. When files conflict, the merge is left
   in progress with conflict markers instead: resolve, `git add` and `git commit`.
4. A summary lists remaining old-root tokens in the branch's changed files.
The result is computed without a checkout (`compute_restack`), which `flagday_restack.py` uses to
restack many pull requests.

Carry-forward check:

    python3 scripts/rename_module_root.py --verify-carry OLD_HEAD NEW_HEAD [--onto BASE]

compares the change OLD_HEAD made relative to its merge base with the pre-rename `main`,
converted as apply mode would, with the change NEW_HEAD makes relative to BASE (default: its merge
base with `origin/main`), as multisets of added and removed lines per renamed path, ignoring the
aggregates. It prints `CARRY OK` when they agree, otherwise the differing lines, and exits 1.

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
from collections import Counter
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
    ("ComplexityScripts", "CslibFrontierScripts", "scripts"),  # a namespace only
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
URL_ONLY = ("manual/history/", "manual/development-history/", "manual/data/")
# Tooling sources: their dotted root tokens are module names even for nonexistent (fixture) modules.
TOOLING_SUFFIXES = (".py", ".sh", ".cjs", ".js", ".yml", ".yaml")
PRAGMA = "rename-module-root: keep"
# Edits that complete the rename and that no rule makes, as (path after the rename, text after the
# rules, replacement). Each applies once, when its text is present and its replacement is not.
FIXUPS = (
    ("README.md", "The package is named `complexitylib`; imports begin",
     "The package is named `cslib-frontier`; imports begin"),
    ("README.md", "\ncd complexitylib\n", "\ncd cslib-frontier\n"),
    ("manual/workflows/getting-started.md", "\ncd complexitylib\n", "\ncd cslib-frontier\n"),
    ("manual/workflows/getting-started.md", "The package is `complexitylib`; imports start with",
     "The package is `cslib-frontier`; imports start with"),
    ("README.md",
     "Community. Downstream projects using that package name should change it to `complexitylib`; "
     "Lean\nimports remain unchanged.",
     "Community. The repository was later renamed from `complexitylib` to `cslib-frontier`, with "
     "the\nLake package renamed to match and the module root renamed from Complexity to "
     "CslibFrontier.\nDownstream projects should require `cslib-frontier` and import "
     "`CslibFrontier.*` modules;\ndeclaration names did not change."),
    ("guide/CslibFrontierGuide/FirstSteps.lean", "The package is named `complexitylib`, and",
     "The package is named `cslib-frontier`, and"),
    # The package-name fixup above lengthens the first line of this paragraph past 100 columns.
    ("guide/CslibFrontierGuide/FirstSteps.lean",
     "The package is named `cslib-frontier`, and its modules begin with `CslibFrontier.` and mirror CSLib's\nlayout. `import CslibFrontier` imports the whole library, which is convenient for exploring but slow\nto load; a development imports the modules it uses. Each module's documentation lists its main\ndefinitions and results, with references.",
     "The package is named `cslib-frontier`, and its modules begin with `CslibFrontier.` and mirror\nCSLib's layout. `import CslibFrontier` imports the whole library, which is convenient for exploring\nbut slow to load; a development imports the modules it uses. Each module's documentation lists its\nmain definitions and results, with references."),
    ("AGENTS.md",
     "`merge=union` result, which keeps deleted imports and can misorder added ones.\n",
     "`merge=union` result, which keeps deleted imports and can misorder added ones.\n\n"
     "A branch that forked before the module root was renamed from Complexity to CslibFrontier is\n"
     "restacked with `python3 scripts/rename_module_root.py --restack` (from a checkout of current\n"
     "`main`; `--onto` names the restacked head of a lower stacked branch). It merges the rename "
     "and\nconverts the branch's own module names and paths; `--verify-carry` compares the result "
     "with\nthe approved head. See the script's documentation.\n"),
    ("CslibFrontierTests/Smoke.lean",
     "/-- The free monad the program layer is built on. -/\nexample := @PFunctor.FreeM\n",
     "/-- The free monad the program layer is built on. -/\nexample := @PFunctor.FreeM\n\n"
     "/-- A two-step program in the upstream free monad evaluates to its value. -/\n"
     "example : ((PFunctor.FreeM.pure 2 : PFunctor.FreeM ⟨PUnit, fun _ => PUnit⟩ ℕ) >>= fun n =>\n"
     "    PFunctor.FreeM.pure (n + 1)) = PFunctor.FreeM.pure 3 := rfl\n"),
    ("abstracts/CslibFrontierAbstracts/Check.lean",
     "      let isLocalRepo := (`CslibFrontier).isPrefixOf owner || "
     "(`CslibFrontierTests).isPrefixOf owner ||\n        (`CslibFrontierAbstracts).isPrefixOf owner",
     "      let isLocalRepo := (`CslibFrontier).isPrefixOf owner ||\n"
     "        (`CslibFrontierTests).isPrefixOf owner || (`CslibFrontierAbstracts).isPrefixOf owner"),
    # Abstract code lines that the longer sibling-root names push past 100 columns.
    ("CslibFrontierTests/Abstracts/AndreevThresholdTests.lean",
     "    51 ≤ (C 0).size ∧ 4369067 ≤ CslibFrontierAbstracts.AndreevThresholdAbstract.wireCount "
     "(C 0) := by",
     "    51 ≤ (C 0).size ∧\n"
     "      4369067 ≤ CslibFrontierAbstracts.AndreevThresholdAbstract.wireCount (C 0) := by"),
    ("abstracts/CslibFrontierAbstracts/BQPAbstract.lean",
     "    (CslibFrontierTests.Abstracts.Encoding.encPair CslibFrontierTests.Abstracts.Encoding.encUnary\n"
     "      (CslibFrontierTests.Abstracts.Encoding.encList "
     "CslibFrontierTests.Abstracts.Encoding.encUnary))",
     "    (CslibFrontierTests.Abstracts.Encoding.encPair\n"
     "      CslibFrontierTests.Abstracts.Encoding.encUnary\n"
     "      (CslibFrontierTests.Abstracts.Encoding.encList\n"
     "        CslibFrontierTests.Abstracts.Encoding.encUnary))"),
    ("abstracts/CslibFrontierAbstracts/BQPAbstract.lean",
     "      CslibFrontierTests.Abstracts.Encoding.encUnary "
     "CslibFrontierTests.Abstracts.Encoding.encUnary ∧",
     "      CslibFrontierTests.Abstracts.Encoding.encUnary\n"
     "      CslibFrontierTests.Abstracts.Encoding.encUnary ∧"),
    ("abstracts/CslibFrontierAbstracts/CryptographyAbstract.lean",
     "  CslibFrontierAbstracts.Encoding, CslibFrontierAbstracts.Computation, "
     "CslibFrontierAbstracts.Randomized,\n",
     "  CslibFrontierAbstracts.Encoding, CslibFrontierAbstracts.Computation,\n"
     "  CslibFrontierAbstracts.Randomized,\n"),
    ("abstracts/CslibFrontierAbstracts/GSWSecurityAbstract.lean",
     "  CslibFrontierAbstracts.Encoding, CslibFrontierAbstracts.Computation, "
     "CslibFrontierAbstracts.Randomized,\n",
     "  CslibFrontierAbstracts.Encoding, CslibFrontierAbstracts.Computation,\n"
     "  CslibFrontierAbstracts.Randomized,\n"),
    # Test fixtures whose messages name the root, which no rule recognizes.
    ("scripts/test_check_docs.py", '"Missing modules in documentation database: Complexity")',
     '"Missing modules in documentation database: CslibFrontier")'),
    ("scripts/test_check_docs.py", '"Missing module in search index: Complexity")',
     '"Missing module in search index: CslibFrontier")'),
    ("scripts/test_check_docs.py", '"Missing module page: Complexity")',
     '"Missing module page: CslibFrontier")'),
    ("scripts/test_check_docs.py", "<summary>Complexity (<a href=",
     "<summary>CslibFrontier (<a href="),
    ("scripts/test_upstream.py", '"Complexity..Init", "Complexity./Init"',
     '"CslibFrontier..Init", "CslibFrontier./Init"'),
)
# Roots that tooling fixtures use for nonexistent modules. The others (`ComplexityTests.*`, ...)
# are also namespaces of test and abstract declarations, so only existing modules are renamed.
FIXTURE_ROOTS = ("Complexity",)

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
    # Lake reads manifest names as `Name`s and writes a hyphenated one with guillemets.
    (re.compile(r'(?<="name": ")complexitylib(?=")'), f"«{NEW_PACKAGE}»"),
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
# A path in a code span, written as its module name when its line cannot be wrapped otherwise.
PATH_SPAN = re.compile(r"`((?:" + "|".join(new for _, new, src in ROOTS if not src)
                       + r")(?:/[A-Za-z_][A-Za-z0-9_]*)+)\.lean`")
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
        pieces = wrap_line(line)
        if any(len(piece) > MAX_LINE for piece in pieces):
            pieces = wrap_line(PATH_SPAN.sub(lambda m: f"`{m[1].replace('/', '.')}`", line))
        out += pieces
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


HEX_SEGMENT = re.compile(r"[0-9a-f]{7,40}")


def sibling_rule(text: str, s: int, root: str) -> str | None:
    """The roots other than `Complexity` (`ComplexityTests`, `ComplexityScripts`, ...) are this
    project's own names, so every occurrence is renamed: module names and paths, and also
    namespaces, qualified declaration names, name literals and messages. Only a path inside a
    permalink to a fixed commit keeps the old name."""
    if s and text[s - 1] == "/":
        segment = SEGMENT.search(text[max(0, s - 400):s - 1]).group(0)
        if HEX_SEGMENT.fullmatch(segment):
            return None
    return NEW_ROOT[root]


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
        for fixup_path, old, replacement in FIXUPS:
            if fixup_path == path and replacement not in new and old in new:
                new = new.replace(old, replacement, 1)
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
            if root != OLD_LIB:
                new = sibling_rule(text, s, root)
            elif region == "h":
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
            if root != OLD_LIB:
                yield line, "any", "sibling root (a path at a fixed commit)", root + rest
                continue
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


def aggregate_specs(lakefile: str) -> list[tuple[str, str, str]]:
    """For each root of each `lean_lib`: its aggregate, the directory of its modules, and the
    library's source directory prefix."""
    specs = []
    for lib in tomllib.loads(lakefile).get("lean_lib", []):
        if not isinstance(lib, dict):
            continue
        src = lib.get("srcDir", ".").strip("/")
        prefix = "" if src in ("", ".") else src + "/"
        for root in lib.get("roots", [lib.get("name")]):
            if root:
                stem = prefix + root.replace(".", "/")
                specs.append((stem + ".lean", stem + "/", prefix))
    return specs


def render_aggregate(existing: str, files, below: str, prefix: str) -> str:
    """What `lake exe mk_all` writes: the sorted imports of every module below the root, in the
    style (module with `public import`, or plain `import`) of the existing file."""
    modules = sorted(p[len(prefix):-5].replace("/", ".") for p in files
                     if p.startswith(below) and p.endswith(".lean"))
    if existing.lstrip().startswith("module"):
        return MODULE_PREAMBLE + "".join(f"public import {m}\n" for m in modules)
    return "".join(f"import {m}\n" for m in modules)


def regenerate_aggregates(repo: Path) -> list[str]:
    """Regenerate the aggregates of the checkout. Returns the changed files."""
    files = [p for p in tracked(repo) if (repo / p).is_file()]
    changed = []
    for aggregate, below, prefix in aggregate_specs((repo / "lakefile.toml").read_text()):
        target = repo / aggregate
        if target.is_file():
            existing = target.read_text()
            content = render_aggregate(existing, files, below, prefix)
            if content != existing:
                target.write_text(content)
                changed.append(aggregate)
    return changed


def aggregate_paths(repo: Path) -> set[str]:
    return {spec[0] for spec in aggregate_specs((repo / "lakefile.toml").read_text())}


ENCODING_RATCHET = "scripts/check_encoding_readability.py"


def apply(repo: Path, mk_all: bool = False, quiet: bool = False,
          record_encodings: bool = False) -> list[str]:
    """Rename the roots of the checkout at `repo` and rewrite its files. Returns changed paths.

    With `record_encodings`, the encoding-readability baseline is then updated for every module
    (`--update-baseline --allow-increase`): the rename touches every module, so a pull request
    check would enforce the baseline in all of them, including any drift that `main` has
    accumulated since a module was last changed."""
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
    if record_encodings and (repo / ENCODING_RATCHET).is_file():
        before = (repo / "scripts/encoding_readability_baseline.json").read_bytes()
        result = subprocess.run([sys.executable, "-B", ENCODING_RATCHET, "--all",
                                 "--update-baseline", "--allow-increase"], cwd=repo,
                                capture_output=True, text=True)
        if result.returncode != 0:
            raise ToolError(f"{ENCODING_RATCHET} --update-baseline failed:\n"
                            f"{result.stdout}{result.stderr}")
        if (repo / "scripts/encoding_readability_baseline.json").read_bytes() != before:
            changed.append("scripts/encoding_readability_baseline.json")
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


def map_path(path: str) -> str:
    """The path of `path` after the rename."""
    for old, new, src in ROOTS:
        base = f"{src}/" if src else ""
        if path.startswith(f"{base}{old}/"):
            return f"{base}{new}/{path[len(base) + len(old) + 1:]}"
        if path == f"{base}{old}.lean":
            return f"{base}{new}.lean"
    return path


def tree_entries(repo: Path, rev: str) -> dict[str, tuple[str, str]]:
    """Path -> (mode, object) for every file of `rev`."""
    out = git(repo, "ls-tree", "-r", "-z", "--full-tree", rev).stdout
    entries = {}
    for record in out.split("\0"):
        if record:
            meta, path = record.split("\t", 1)
            mode, _, oid = meta.split()
            entries[path] = (mode, oid)
    return entries


def blob_text(repo: Path, oid: str) -> str | None:
    data = subprocess.run(["git", "-C", str(repo), "cat-file", "blob", oid], capture_output=True,
                          check=True).stdout
    if b"\0" in data:
        return None
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError:
        return None


def write_blob(repo: Path, text: str) -> str:
    return git(repo, "hash-object", "-w", "--stdin", input=text).stdout.strip()


class ScratchIndex:
    """A temporary index in the Git directory, for building trees without a checkout."""

    def __init__(self, repo: Path, tree: str):
        self.repo = repo
        self.path = state_dir(repo) / f"index-{os.getpid()}-{id(self)}"
        self.env = {"GIT_INDEX_FILE": str(self.path)}
        self.git("read-tree", tree)

    def git(self, *args: str, input: str | None = None) -> subprocess.CompletedProcess[str]:
        return git(self.repo, *args, env=self.env, input=input)

    def files(self) -> list[str]:
        return list(dict.fromkeys(p for p in self.git("ls-files", "-z").stdout.split("\0") if p))

    def update(self, entries: list[str]) -> None:
        if entries:
            self.git("update-index", "--index-info", input="".join(e + "\n" for e in entries))

    def regenerate_aggregates(self) -> None:
        files = self.files()
        if "lakefile.toml" not in files:
            return
        entries = []
        for aggregate, below, prefix in aggregate_specs(self.git("show", ":lakefile.toml").stdout):
            if aggregate in files:
                existing = self.git("show", f":{aggregate}").stdout
                content = render_aggregate(existing, files, below, prefix)
                if content != existing:
                    entries.append(f"100644 {write_blob(self.repo, content)}\t{aggregate}")
        self.update(entries)

    def write_tree(self) -> str:
        return self.git("write-tree").stdout.strip()

    def close(self) -> None:
        self.path.unlink(missing_ok=True)


def regenerate_tree_aggregates(repo: Path, tree: str) -> str:
    index = ScratchIndex(repo, tree)
    try:
        index.regenerate_aggregates()
        return index.write_tree()
    finally:
        index.close()


def convert_changes(repo: Path, pre: str, pre_converted: str, commit: str) -> str:
    """The tree of `apply(commit)`, built from the cached `apply(pre)` by converting only the
    files that differ between `pre` and `commit`. The files `commit` does not change keep their
    converted form in `apply(pre)`, so only the branch's own changes differ."""
    changes = git(repo, "diff", "--name-status", "--no-renames", "-z", pre, commit).stdout
    fields = [f for f in changes.split("\0") if f]
    pairs = list(zip(fields[0::2], fields[1::2]))
    entries_of = tree_entries(repo, commit)
    rewriter = Rewriter(Inventory.from_paths(entries_of))
    removals, additions = [], []
    for status, path in pairs:
        target = map_path(path)
        if status == "D":
            removals.append(f"0 {'0' * 40}\t{target}")
            continue
        mode, oid = entries_of[path]
        if mode in ("100644", "100755"):
            text = blob_text(repo, oid)
            if text is not None:
                converted = rewriter.rewrite(target, text)
                if converted != text:
                    oid = write_blob(repo, converted)
        additions.append(f"{mode} {oid}\t{target}")
    index = ScratchIndex(repo, pre_converted)
    try:
        index.update(removals)
        index.update(additions)
        index.regenerate_aggregates()
        return index.write_tree()
    finally:
        index.close()


def merge_trees(repo: Path, ours: str, theirs: str, base: str | None = None,
                attributes: str | None = None) -> tuple[str, list[str]]:
    """`git merge-tree` of two commits (and an explicit base commit). Returns the result tree,
    whose conflicted files carry conflict markers, and the conflicted-stage entries."""
    args = [*merge_drivers()]
    if attributes:
        args += ["-c", f"attr.tree={attributes}"]
    args += ["merge-tree", "--write-tree", "-z"]
    if base:
        args.append(f"--merge-base={base}")
    result = git(repo, *args, ours, theirs, check=False)
    if result.returncode not in (0, 1):
        raise ToolError(f"git merge-tree failed:\n{result.stderr.strip()}")
    fields = result.stdout.split("\0")
    stages = []
    for entry in fields[1:]:
        if not entry:
            break
        stages.append(entry)  # "<mode> <object> <stage>\t<path>"
    return fields[0], stages


def staged_paths(stages: list[str]) -> list[str]:
    return sorted({s.split("\t", 1)[1] for s in stages})


@dataclass
class Restack:
    status: str            # "clean", "up-to-date", "conflict"
    head: str              # the restacked head (HEAD when not clean)
    onto: str
    pre: str = ""
    stage: str = ""        # where a conflict arose: "pre" or "rename"
    merged_pre: str = ""   # the merge of `pre` into the branch, when it was clean
    tree: str = ""         # the merged tree, with conflict markers on a conflict
    stages: list[str] = field(default_factory=list)
    conflicts: list[str] = field(default_factory=list)


def compute_restack(repo: Path, head: str, onto: str, trailer: str = "",
                    reference: str | None = None) -> Restack:
    """Restack `head` onto the post-rename commit `onto` without touching any checkout or ref.
    On success the result is an unreferenced merge commit with parents (the branch, merged with
    the pre-rename counterpart if needed) and `onto`. `reference`, a pre-rename commit whose
    conversion is cached (main before the rename), lets a stacked branch's pre-rename counterpart
    be converted from it incrementally instead of in a full checkout."""
    if not has_path(repo, onto, MARKER):
        raise ToolError(f"{onto[:12]} is not a post-rename commit")
    if is_ancestor(repo, onto, head):
        return Restack("up-to-date", head, onto)
    if has_path(repo, head, MARKER):
        raise ToolError(f"{head[:12]} is already post-rename; merge newer commits with git merge")
    pre = pre_rename_counterpart(repo, onto)
    signature = f"\n\n{trailer}\n" if trailer else "\n"
    branch = head
    if not is_ancestor(repo, pre, head):
        tree, stages = merge_trees(repo, head, pre, attributes=pre)
        aggregates = {spec[0] for spec in aggregate_specs(
            git(repo, "show", f"{pre}:lakefile.toml").stdout)}
        conflicts = [p for p in staged_paths(stages) if p not in aggregates]
        if conflicts:
            return Restack("conflict", head, onto, pre, "pre", tree=tree, stages=stages,
                           conflicts=conflicts)
        tree = regenerate_tree_aggregates(repo, tree)
        message = f"Merge {pre[:12]} (main before the module-root rename){signature}"
        branch = git(repo, "commit-tree", tree, "-p", head, "-p", pre, "-F", "-",
                     input=message).stdout.strip()
    if reference and reference != pre:
        base = convert_changes(repo, reference, converted_tree(repo, reference), pre)
    else:
        base = converted_tree(repo, pre)
    ours = convert_changes(repo, pre, base, branch)
    tree, stages = merge_trees(repo, scratch_commit(repo, ours), onto,
                               base=scratch_commit(repo, base), attributes=onto)
    aggregates = {spec[0] for spec in aggregate_specs(
        git(repo, "show", f"{onto}:lakefile.toml").stdout)}
    conflicts = [p for p in staged_paths(stages) if p not in aggregates]
    if conflicts:
        return Restack("conflict", head, onto, pre, "rename", branch, tree, stages, conflicts)
    tree = regenerate_tree_aggregates(repo, tree)
    message = (f"Merge the module-root rename ({onto[:12]})\n\n"
               f"Restacked with scripts/rename_module_root.py --restack: the branch's changes,\n"
               f"with module names and paths converted, merged with the renamed tree.{signature}")
    new = git(repo, "commit-tree", tree, "-p", branch, "-p", onto, "-F", "-",
              input=message).stdout.strip()
    return Restack("clean", new, onto, pre, merged_pre=branch, tree=tree)


def resolve_onto(repo: Path, onto_ref: str | None, upstream: str) -> str:
    return rev(repo, onto_ref) if onto_ref else find_rename_commit(repo, upstream)


def residual_report(repo: Path, rev_: str, paths: list[str]) -> list[str]:
    entries = tree_entries(repo, rev_)
    rewriter = Rewriter(Inventory.from_paths(entries))
    lines = []
    for path in paths:
        if path not in entries or entries[path][0] not in ("100644", "100755"):
            continue
        text = blob_text(repo, entries[path][1])
        if text is None:
            continue
        for line, where, category, token in rewriter.residue(path, text):
            if category == "dotted name, not a module" or \
                    (category == "bare word" and where != "code" and token != OLD_LIB):
                lines.append(f"{path}:{line}: {where}: {category}: {token}")
    return lines


def restack(repo: Path, onto_ref: str | None, upstream: str, mk_all: bool,
            trailer: str = "") -> int:
    """Restack the checked-out branch; see the module documentation."""
    if git(repo, "status", "--porcelain", "--untracked-files=no").stdout.strip():
        raise ToolError("the working tree has uncommitted changes")
    gitdir = Path(git(repo, "rev-parse", "--path-format=absolute", "--git-dir").stdout.strip())
    if (gitdir / "MERGE_HEAD").exists():
        raise ToolError("a merge is in progress; commit or abort it first")
    head = rev(repo, "HEAD")
    onto = resolve_onto(repo, onto_ref, upstream)
    if is_ancestor(repo, onto, head):
        print(f"{onto[:12]} is already merged; converting any remaining old names.")
        changed = apply(repo, mk_all=mk_all, quiet=True)
        if changed:
            git(repo, "commit", "-q", "-F", "-", input=(
                f"chore: convert remaining module names to {NEW_LIB}\n\n"
                f"scripts/rename_module_root.py --restack\n" + (f"\n{trailer}\n" if trailer else "")))
            print(f"committed conversions of {len(changed)} files")
        return 0
    result = compute_restack(repo, head, onto, trailer)
    print(f"HEAD {head[:12]}; onto {onto[:12]}; pre-rename counterpart {result.pre[:12]}")
    if result.status == "clean":
        git(repo, "merge", "-q", "--ff-only", result.head)
        changed = git(repo, "diff", "--name-only", "-z", onto, "HEAD").stdout
        paths = sorted(p for p in changed.split("\0") if p)
        print(f"restacked: {result.head}\nThe branch changes {len(paths)} files relative to "
              f"{onto[:12]}.")
        attention = residual_report(repo, "HEAD", paths)
        if attention:
            print("Old-root tokens left in the branch's files (check whether they name modules):")
            for line in attention:
                print(f"  {line}")
        return 0
    if result.stage == "pre":
        # Repeat the merge in the checkout, so that a person resolves it there.
        git(repo, *merge_drivers(), "merge", "--no-ff", "--no-edit", result.pre, check=False)
        print("Merging the pre-rename main conflicts in:")
        for path in unmerged(repo) or result.conflicts:
            print(f"  {path}")
        print("Resolve, `git add` and `git commit` this merge, then run --restack again.")
        return 3
    if result.merged_pre != head:
        git(repo, "merge", "-q", "--ff-only", result.merged_pre)
    git(repo, "merge", "--no-ff", "--no-commit", "-s", "ours", onto)
    git(repo, "read-tree", "-u", "--reset", result.tree)
    git(repo, "update-index", "--index-info",
        input="".join(f"0 {'0' * 40}\t{p}\n" for p in staged_paths(result.stages))
        + "".join(f"{s}\n" for s in result.stages))
    aggregates = [p for p in staged_paths(result.stages) if p not in result.conflicts]
    if aggregates:
        regenerate_aggregates_from_worktree(repo, aggregates)
    print("CONFLICTS (the merge is in progress; resolve, `git add`, `git commit`):")
    for path in result.conflicts:
        print(f"  {path}")
    return 4


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


# --- Approval carry-forward ----------------------------------------------------------------------

def line_delta(before: str | None, after: str | None) -> tuple[Counter, Counter]:
    old = Counter((before or "").split("\n")) if before is not None else Counter()
    new = Counter((after or "").split("\n")) if after is not None else Counter()
    return new - old, old - new


def file_text(repo: Path, entries: dict[str, tuple[str, str]], path: str) -> str | None:
    if path not in entries:
        return None
    mode, oid = entries[path]
    if mode not in ("100644", "100755"):
        return f"<{mode} {oid}>"
    text = blob_text(repo, oid)
    return f"<binary {oid}>" if text is None else text


def deltas(repo: Path, base: str, head: str, convert: bool) -> dict[str, tuple[Counter, Counter]]:
    """Per (renamed) path, the lines that `head` adds and removes relative to `base`, as
    multisets. With `convert`, both sides are first converted as apply mode would."""
    changed = git(repo, "diff", "--name-only", "--no-renames", "-z", base, head).stdout
    paths = sorted({p for p in changed.split("\0") if p})
    base_entries, head_entries = tree_entries(repo, base), tree_entries(repo, head)
    rewriters = (Rewriter(Inventory.from_paths(base_entries)),
                 Rewriter(Inventory.from_paths(head_entries)))
    out: dict[str, tuple[Counter, Counter]] = {}
    for path in paths:
        target = map_path(path) if convert else path
        texts = [file_text(repo, base_entries, path), file_text(repo, head_entries, path)]
        if convert:
            texts = [t if t is None or t.startswith("<") else rw.rewrite(target, t)
                     for t, rw in zip(texts, rewriters)]
        added, removed = line_delta(*texts)
        previous = out.get(target, (Counter(), Counter()))
        out[target] = (previous[0] + added, previous[1] + removed)
    return out


def verify_carry(repo: Path, old_head: str, new_head: str, onto_ref: str | None,
                 upstream: str) -> tuple[bool, list[str]]:
    """Whether the restacked `new_head` makes exactly the converted change of `old_head`."""
    base_new = rev(repo, onto_ref) if onto_ref else \
        git(repo, "merge-base", new_head, upstream).stdout.strip()
    if not has_path(repo, base_new, MARKER):
        raise ToolError(f"{base_new[:12]}, the base of {new_head[:12]}, is not post-rename")
    pre = pre_rename_counterpart(repo, base_new)
    base_old = git(repo, "merge-base", old_head, pre).stdout.strip()
    aggregates = {spec[0] for spec in aggregate_specs(
        git(repo, "show", f"{new_head}:lakefile.toml").stdout)}
    old = deltas(repo, base_old, old_head, convert=True)
    new = deltas(repo, base_new, new_head, convert=False)
    moved = git(repo, "diff", "--name-only", "--no-renames", "-z", base_old, pre).stdout
    main_changed = {map_path(p) for p in moved.split("\0") if p}
    report = []
    for path in sorted(set(old) | set(new)):
        if path in aggregates:
            continue
        o_add, o_rem = old.get(path, (Counter(), Counter()))
        n_add, n_rem = new.get(path, (Counter(), Counter()))
        if (o_add, o_rem) == (n_add, n_rem):
            continue
        report.append(f"--- {path}" + ("  (main also changed this file after the old head's base)"
                                         if path in main_changed else ""))
        for sign, only, label in (("+", o_add - n_add, "added only at the old head"),
                                  ("+", n_add - o_add, "added only at the new head"),
                                  ("-", o_rem - n_rem, "removed only at the old head"),
                                  ("-", n_rem - o_rem, "removed only at the new head")):
            if only:
                report.append(f"  {label}:")
                report += [f"    {sign}{line}" for line in sorted(only.elements())]
    return not report, report


# --- Command line --------------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--repo", type=Path, default=Path.cwd(), help="checkout (default: .)")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--restack", action="store_true", help="merge the rename into this branch")
    mode.add_argument("--report", action="store_true", help="list the old-root tokens that remain")
    mode.add_argument("--verify-carry", nargs=2, metavar=("OLD_HEAD", "NEW_HEAD"),
                      help="check that NEW_HEAD, the restacked OLD_HEAD, makes the same change")
    parser.add_argument("--onto", help="restack: the post-rename commit to merge (default: the "
                        "rename commit); verify-carry: the base of NEW_HEAD (default: its merge "
                        "base with --upstream)")
    parser.add_argument("--trailer", default="", help="restack: a trailer for the merge commits")
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
            return restack(repo, args.onto, args.upstream, args.mk_all, args.trailer)
        if args.verify_carry:
            old, new = (rev(repo, r) for r in args.verify_carry)
            ok, lines = verify_carry(repo, old, new, args.onto, args.upstream)
            print("\n".join(lines + [f"CARRY {'OK' if ok else 'DIFF'} {old} {new}"]))
            return 0 if ok else 1
        apply(repo, mk_all=not args.no_mk_all, record_encodings=True)
        return 0
    except ToolError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
