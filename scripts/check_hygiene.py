#!/usr/bin/env python3
"""Static proof-hygiene and module-template checks for Complexitylib Lean files.

Checks enforced by default (see AGENTS.md):
1. Every module under Complexity/ has a valid standalone `-- upstream:` line comment.
2. No `sorry`, custom `axiom`, or `native_decide` in Complexity/, ComplexityTests/ or the
   dedicated abstract library.
3. Every `set_option maxHeartbeats` or `set_option maxRecDepth` has an explanatory comment
   on the same line, within the preceding 3 lines, or (for `set_option ... in`) on the next
   line, where Mathlib's `linter.style.maxHeartbeats` expects it.
4. Docstrings in `Complexity/` contain only root-qualified or external Markdown links
   (`[text](target)`, where external means `http://` or `https://` and anchors start with `#`,
   matching `doc-gen4`'s `extendLink`) and root-qualified slash-containing `.lean` code tokens
   (`Complexity/.../*.lean`, `Cslib/...`, `Mathlib/...`) in inline code spans and fenced Lean code
   blocks. `Complexity/...` targets are checked for file existence on disk; dependency roots
   (`Cslib/`, `Mathlib/`, `Batteries/`) are checked on disk when `.lake/packages` is present locally
   and by root prefix in CI (where `check_hygiene.py` runs before `.lake` is restored) or for
   toolchain roots (`Std/`, `Init/`, `Lean/`). Reference-link definitions (`[label]: target`, with
   an optional single-line title and the destination on the same or next line) use the same
   target check.
   Citation-shaped labels followed by a bare prose word remain citation prose.
   Nested block-container definitions and indented (4-space) code blocks are not scanned;
   `scripts/check_docs.py` in `docs.yml` remains the full HTML backstop.
5. (Default selection only.) `references.bib` keys are unique and its entries are sorted by key,
   both compared case-insensitively as BibTeX does, so that PRs adding entries rarely conflict.
6. Every citation key in a docstring is a `references.bib` key. A citation is a bracketed segment
   (`[Key]`, `[Key, Theorem 2]`, `[Key; Other]`, or the reference in `[text][Key]`) that has the
   shape of the repository's keys: letters, a two- to four-digit year or number, and an optional
   letter suffix (`AroraBarak09`, `NISTFIPS203`, `Ilango2020FOCS`), opened at the start of a
   line or after whitespace or punctuation, not after a word character (`xs[i10]`). Code spans,
   fenced code, math, escaped brackets, inline links `[text](target)` and block quotes (`> ...`,
   which quote a source's own citations) are not scanned. Keys without digits are not recognized.

7. (Default selection and explicit paths.) No `set_option maxHeartbeats N` exceeds the 200000
   default unless its file is listed in `scripts/heartbeat_allowlist.txt` with a cap of at least
   `N` (one `<path> <cap>` entry per line, `#` comments allowed). Zero means unlimited in Lean
   and requires an explicit zero cap; finite caps never permit it. Unparsed values fail closed.
   Inline and multiline settings and decimal/hexadecimal numerals are checked. With the default
   selection, an entry whose file no longer needs it (no budget above the default, or a cap above the largest
   budget) is reported as stale, so the allowlist only shrinks as budgets are reduced (#1528).

Opt-in heuristic checks:
8. (`--check-simp`) Flag non-terminal bare `simp` tactics in `-- upstream: candidate` modules
   under Complexity/.
9. (`--max-lines N`) Flag Lean files exceeding N lines.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from proof_lengths import (  # noqa: E402
    CHAR_LITERAL,
    COMMAND,
    COMMENT_SPECIAL,
    NORMAL_SPECIAL,
    STRING_SPECIAL,
    masks,
)
from upstream import upstream_markers  # noqa: E402

UPSTREAM_STATUS_RE = re.compile(
    r"(?:"
    r"candidate(?:\s+.*)?|"
    r"submitted\s+#\d+(?:\s+@[0-9a-f]{7,40})?(?:\s+.*)?|"
    r"(?:vendored|subset of)\s+\S+(?:\s+@[0-9a-f]{7,40})?(?:\s+.*)?|"
    r"merged\s+@[0-9a-f]{7,40}(?:\s+.*)?|"
    r"local-only\s+\([^)]+\)"
    r")",
)

FORBIDDEN_TOKEN_RE = re.compile(r"\b(sorry|native_decide)\b")
CUSTOM_AXIOM_RE = re.compile(
    r"^\s*(?:@\[(?:[^\[\]\n]|\[[^\[\]\n]*\])*\]\s*)*(?:(?:public|private|protected|noncomputable|scoped|local)\s+)*axiom\b",
    re.M,
)
SET_OPTION_RE = re.compile(r"\bset_option\s+(maxHeartbeats|maxRecDepth)\b(?:\s+\S+)?")
HEARTBEAT_VALUE_RE = re.compile(r"\bset_option\s+maxHeartbeats\b\s*([^\s;,)]+)?")
DEFAULT_MAX_HEARTBEATS = 200000
HEARTBEAT_ALLOWLIST = ROOT / "scripts" / "heartbeat_allowlist.txt"
# cslib pads some keys with spaces.
BIB_KEY_RE = re.compile(r"^@\w+\s*\{\s*([^,\s]+)\s*,", re.M)

DOC_DEP_ROOTS = ("Cslib", "Mathlib", "Batteries", "Std", "Init", "Lean")
DOC_FENCE_RE = re.compile(
    r"^[ \t]*(?P<fence>`{3,}|~{3,})(?P<info>[^\n]*)\n(?P<body>.*?)(?:\n[ \t]*(?P=fence)[ \t]*(?=\n|$)|\Z)",
    re.M | re.S,
)
DOC_INLINE_RE = re.compile(
    r"(?P<escape>\\.)"
    r"|(?P<math>\$\$[\s\S]+?\$\$|\$[^$\n]+?\$)"
    r"|(?P<link>(?<!!)\[(?:`+[^`\n]*`+|\\.|[^\[\]`\\])*\]\(\s*"
    r"(?:<(?P<angle_target>[^>\s]+)>|(?P<target>[^)\s\"']+))"
    r"(?:\s+(?:\"[^\"]*\"|'[^']*'|\([^)\n]*\)))?\s*\))"
    r"|(?P<code_fence>`+)(?P<code>(?:(?!\n[ \t]*\n)[\s\S])+?)(?<!`)(?P=code_fence)(?!`)"
)
DOC_REFERENCE_RE = re.compile(
    r"^[ ]{0,3}\[(?P<label>(?:\\.|[^\[\]\\\n])+)\]:[ \t]*(?:\n[ ]{0,3})?"
    r"(?:<(?P<angle_target>[^<>\n]*)>|(?P<target>[^\s<>]+))"
    r"(?:[ \t]+(?:\"[^\"\n]*\"|'[^'\n]*'|\([^)\n]*\)))?[ \t]*$",
    re.M,
)
WHITESPACE_RUN_RE = re.compile(r"\S+")
# The shape of every `references.bib` key except the year-less `MilewskiDao`.
CITATION_KEY_RE = re.compile(r"[A-Za-z]+[0-9]{2,4}[A-Za-z]*")
# A bracketed span that starts a line or follows whitespace or punctuation other than `\` and
# `!`, so that indexing such as `xs[i10]` is not a citation, and is not followed by `(` (a link
# the masks missed).
DOC_BRACKET_RE = re.compile(r"(?<![\w\\!])\[([^\[\]]*)\](?!\()")
DOC_BLOCKQUOTE_RE = re.compile(r"^[ \t]*>.*$", re.M)
CITATION_SEGMENT_RE = re.compile(r"[^;,]+")


def extract_docstrings(text: str) -> list[tuple[int, str]]:
    """Return `(start_offset, body)` for every top-level `/-! ... -/` or `/-- ... -/` docstring."""
    docstrings: list[tuple[int, str]] = []
    size = len(text)
    depth, quoted, i = 0, False, 0
    doc_start: int | None = None
    while i < size:
        if depth:
            match = COMMENT_SPECIAL.search(text, i)
            if not match:
                break
            if match[0] == "/-":
                depth += 1
            else:
                depth -= 1
                if depth == 0 and doc_start is not None:
                    docstrings.append((doc_start, text[doc_start:match.start()]))
                    doc_start = None
            i = match.end()
        elif quoted:
            match = STRING_SPECIAL.search(text, i)
            if not match:
                break
            j = match.start()
            if text[j] == "\\" and j + 1 < size:
                i = j + 2
            else:
                quoted = text[j] != '"'
                i = j + 1
        else:
            match = NORMAL_SPECIAL.search(text, i)
            if not match:
                break
            j = match.start()
            if match[0] == "--":
                end = text.find("\n", j)
                i = size if end < 0 else end
            elif match[0] == "/-":
                if text.startswith(("/--", "/-!"), j) and not text.startswith("/---", j):
                    doc_start = j + 3
                depth, i = 1, j + 2
            elif match[0] == "'":
                literal = CHAR_LITERAL.match(text, j)
                i = literal.end() if literal else j + 1
            elif match[0] != '"':
                close = '"' + match[0][1:-1]
                end = text.find(close, match.end())
                i = size if end < 0 else end + len(close)
            else:
                quoted, i = True, j + 1
    return docstrings


def validate_doc_module_path(part: str, root: pathlib.Path) -> str | None:
    """Validate a slash-containing `.lean` code token that `doc-gen4` auto-links from doc root."""
    if any(ch in part for ch in "{}\\") or part.startswith("/") or "//" in part:
        return "use a clean repository-root `Complexity/.../*.lean` path or a full URL link"
    segments = part.split("/")
    if any(seg in ("", ".", "..") for seg in segments):
        return "path must not contain `.` or `..` segments"
    top = segments[0]
    if top == "Complexity":
        if not (root / part).is_file():
            return f"local module `{part}` does not exist"
        return None
    if top in DOC_DEP_ROOTS:
        if top in ("Cslib", "Mathlib", "Batteries"):
            pkg_dir = root / ".lake" / "packages" / top.lower()
            if pkg_dir.is_dir() and not (pkg_dir / part).is_file() and not (root / part).is_file():
                return f"dependency module `{part}` does not exist"
        return None
    return (
        "slash-qualified `.lean` code token is auto-linked by doc-gen4; "
        "prefix with `Complexity/` or link to a full URL"
    )


def validate_doc_markdown_target(target: str, root: pathlib.Path) -> str | None:
    """Validate an inline or reference Markdown link target in a `Complexity/` docstring."""
    if target.startswith(("https://", "http://", "#")):
        return None
    path_part, _, _ = target.partition("#")
    if (
        path_part.endswith(".html")
        and "/" in path_part
        and not path_part.startswith("/")
        and "//" not in path_part
        and not any(ch in path_part for ch in "{}\\")
    ):
        segments = path_part.split("/")
        if not any(seg in ("", ".", "..") for seg in segments):
            lean_rel = path_part[:-5] + ".lean"
            top = segments[0]
            if top == "Complexity":
                if (root / lean_rel).is_file():
                    return None
                return f"target module `{lean_rel}` does not exist"
            if top in DOC_DEP_ROOTS:
                if top in ("Cslib", "Mathlib", "Batteries"):
                    pkg_dir = root / ".lake" / "packages" / top.lower()
                    if (
                        pkg_dir.is_dir()
                        and not (pkg_dir / lean_rel).is_file()
                        and not (root / lean_rel).is_file()
                    ):
                        return f"target dependency module `{lean_rel}` does not exist"
                return None
    return (
        "use a root-qualified `Complexity/.../*.html` path, `#anchor`, or `https://` URL "
        "(or escape `\\[...\\]` if not a link)"
    )


def check_docstring_links(raw: str, rel: pathlib.Path, root: pathlib.Path) -> list[str]:
    """Check Markdown links and auto-linked `.lean` code tokens in `Complexity/` docstrings."""
    errors: list[str] = []
    for doc_start, doc in extract_docstrings(raw):
        chars = list(doc)
        for m in DOC_FENCE_RE.finditer(doc):
            info = m.group("info").strip()
            lang = info.split()[0] if info else ""
            if lang in ("", "lean"):
                body = m.group("body")
                body_offset = doc_start + m.start("body")
                for tm in WHITESPACE_RUN_RE.finditer(body):
                    tok = tm.group(0)
                    if "/" in tok and tok.endswith(".lean"):
                        reason = validate_doc_module_path(tok, root)
                        if reason:
                            line_no = raw.count("\n", 0, body_offset + tm.start()) + 1
                            errors.append(
                                f"{rel}:{line_no}: invalid docstring module path `{tok}` ({reason})"
                            )
            for j in range(m.start(), m.end()):
                if chars[j] != "\n":
                    chars[j] = " "
        masked_doc = "".join(chars)
        for m in DOC_INLINE_RE.finditer(masked_doc):
            target = m.group("angle_target") or m.group("target")
            if target is not None:
                reason = validate_doc_markdown_target(target, root)
                if reason:
                    line_no = raw.count("\n", 0, doc_start + m.start()) + 1
                    errors.append(
                        f"{rel}:{line_no}: invalid docstring Markdown link target `{target}` ({reason})"
                    )
            elif m.group("code") is not None:
                code_body = m.group("code")
                code_offset = doc_start + m.start("code")
                for tm in WHITESPACE_RUN_RE.finditer(code_body):
                    tok = tm.group(0)
                    if "/" in tok and tok.endswith(".lean"):
                        reason = validate_doc_module_path(tok, root)
                        if reason:
                            line_no = raw.count("\n", 0, code_offset + tm.start()) + 1
                            errors.append(
                                f"{rel}:{line_no}: invalid docstring module path `{tok}` ({reason})"
                            )
            # Reference definitions inside inline code, math or escaped brackets are examples,
            # not links. Preserve offsets while hiding them from the line-based scan below.
            mask_span(chars, m.start(), m.end())
        for m in DOC_REFERENCE_RE.finditer(masked_doc):
            label_start = m.start() + len(m[0]) - len(m[0].lstrip(" "))
            if chars[label_start] != "[":
                continue
            target = m.group("angle_target")
            if target is None:
                target = m.group("target")
                # A citation sentence may wrap just after "[Key, locator]: if". Preserve
                # citation prose, but still validate explicit angle/path/URL destinations.
                if target.isalpha() and docstring_citations("[" + m.group("label") + "]"):
                    continue
            reason = validate_doc_markdown_target(target, root)
            if reason:
                line_no = raw.count("\n", 0, doc_start + m.start()) + 1
                errors.append(
                    f"{rel}:{line_no}: invalid docstring Markdown link target `{target}` ({reason})"
                )
    return errors


def mask_span(chars: list[str], start: int, end: int) -> None:
    for j in range(start, end):
        if chars[j] != "\n":
            chars[j] = " "


def docstring_citations(doc: str) -> list[tuple[int, str]]:
    """Return `(offset, key)` for every citation-shaped key in a docstring body (check 6)."""
    chars = list(doc)
    for m in DOC_FENCE_RE.finditer(doc):
        mask_span(chars, m.start(), m.end())
    for m in DOC_BLOCKQUOTE_RE.finditer(doc):
        mask_span(chars, m.start(), m.end())
    masked = "".join(chars)
    for m in DOC_INLINE_RE.finditer(masked):
        mask_span(chars, m.start(), m.end())
    masked = "".join(chars)
    citations: list[tuple[int, str]] = []
    for bracket in DOC_BRACKET_RE.finditer(masked):
        for segment in CITATION_SEGMENT_RE.finditer(bracket.group(1)):
            key = segment.group(0).strip()
            if CITATION_KEY_RE.fullmatch(key):
                offset = bracket.start(1) + segment.start() + segment.group(0).index(key)
                citations.append((offset, key))
    return citations


def check_docstring_citations(raw: str, rel: pathlib.Path, bib_keys: frozenset[str]) -> list[str]:
    """Report docstring citation keys that `references.bib` does not define."""
    errors: list[str] = []
    for doc_start, doc in extract_docstrings(raw):
        for offset, key in docstring_citations(doc):
            if key not in bib_keys:
                line_no = raw.count("\n", 0, doc_start + offset) + 1
                errors.append(
                    f"{rel}:{line_no}: docstring cites `{key}`, which is not a key in "
                    "references.bib (add the entry, or escape the brackets `\\[...\\]` if it is "
                    "not a citation)"
                )
    return errors


def bibliography_keys(text: str) -> frozenset[str]:
    return frozenset(m.group(1) for m in BIB_KEY_RE.finditer(text))


def has_nearby_comment(raw_lines: list[str], code_lines: list[str], idx_0based: int) -> bool:
    start = max(0, idx_0based - 3)
    end = idx_0based + 1
    # Mathlib's `linter.style.maxHeartbeats` wants the reason right after `set_option ... in`.
    if code_lines[idx_0based].rstrip().endswith(" in") and idx_0based + 1 < len(code_lines):
        end = idx_0based + 2
    for j in range(start, end):
        # If masking comments changed the line, a comment is present on line j.
        if raw_lines[j] != code_lines[j]:
            return True
    return False


BARE_SIMP_RE = re.compile(
    r"^simp(?!\s*(?:\?\s*)?(?:(?:\+\w+|\([^)]*\))\s*)*only\b|_all\b|_arith\b|_rw\b|a\b|\w)"
)


def find_nonterminal_bare_simps(code: str) -> list[int]:
    """Return 1-based line numbers of non-terminal bare `simp` tactics in masked code."""
    lines = code.split("\n")
    violations: list[int] = []
    for i, line in enumerate(lines):
        stripped = line.strip()
        if not stripped:
            continue
        # Only inspect lines that start with a bare `simp` (or `· simp`).
        bullet_stripped = re.sub(r"^[·•*-]\s*", "", stripped)
        if not BARE_SIMP_RE.match(bullet_stripped):
            continue
        if "<;>" in bullet_stripped or ";" in bullet_stripped or bullet_stripped.endswith(","):
            continue
        indent = len(line) - len(line.lstrip(" "))
        has_bullet = stripped.startswith(("·", "•"))
        # Scan subsequent non-empty lines to see if another tactic follows in the same block.
        j = i + 1
        while j < len(lines) and not lines[j].strip():
            j += 1
        if j >= len(lines):
            continue
        next_line = lines[j]
        next_stripped = next_line.strip()
        if COMMAND.match(next_line):
            continue
        if re.match(r"^\|(\s|$)", next_stripped) or re.match(r"^case\s+", next_stripped):
            continue
        next_indent = len(next_line) - len(next_line.lstrip(" "))
        next_has_bullet = next_stripped.startswith(("·", "•"))
        if has_bullet:
            # Inside a `· simp` line, a following tactic at indent > bullet indent is non-terminal.
            if next_indent > indent and not next_has_bullet:
                violations.append(i + 1)
        else:
            if next_indent == indent and not next_has_bullet:
                violations.append(i + 1)
    return violations


def load_heartbeat_allowlist(path: pathlib.Path = HEARTBEAT_ALLOWLIST) -> dict[str, int]:
    """Parse `<path> <cap>` lines (blank lines and `#` comments ignored) into a cap per file."""
    caps: dict[str, int] = {}
    if not path.exists():
        return caps
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        entry = line.split("#", 1)[0].split()
        if not entry:
            continue
        if len(entry) != 2 or not entry[1].isdigit():
            raise ValueError(f"{path}:{line_no}: expected `<path> <cap>`, got {line!r}")
        caps[entry[0]] = int(entry[1])
    return caps


def heartbeat_budgets(code_lines: list[str]) -> list[tuple[int, int | None]]:
    """Find inline/multiline budgets in masked code; None denotes an unparsed value."""
    code = "\n".join(code_lines)
    budgets: list[tuple[int, int | None]] = []
    for match in HEARTBEAT_VALUE_RE.finditer(code):
        token = (match.group(1) or "").replace("_", "")
        try:
            value = int(token, 16 if token.lower().startswith("0x") else 10)
            if value < 0:
                value = None
        except ValueError:
            value = None
        budgets.append((code.count("\n", 0, match.start()) + 1, value))
    return budgets


def check_heartbeat_allowlist_stale(caps: dict[str, int], root: pathlib.Path = ROOT) -> list[str]:
    """Report allowlist entries whose file no longer needs them, so the list only shrinks."""
    errors: list[str] = []
    for rel, cap in sorted(caps.items()):
        path = root / rel
        if not path.exists():
            errors.append(f"scripts/heartbeat_allowlist.txt: `{rel}` does not exist; remove it")
            continue
        code, _ = masks(path.read_text(encoding="utf-8"))
        values = [v for _, v in heartbeat_budgets(code.split("\n")) if v is not None]
        # Lean's zero means unlimited, above every finite cap.
        if 0 in values:
            continue
        largest = max(values, default=0)
        if largest <= DEFAULT_MAX_HEARTBEATS:
            errors.append(f"scripts/heartbeat_allowlist.txt: `{rel}` has no budget above "
                          f"{DEFAULT_MAX_HEARTBEATS}; remove its entry")
        elif cap == 0 or cap > largest:
            errors.append(f"scripts/heartbeat_allowlist.txt: `{rel}` cap {cap} exceeds its "
                          f"largest budget {largest}; lower the cap to {largest}")
    return errors


def check_file(
    path: pathlib.Path,
    root: pathlib.Path = ROOT,
    check_simp: bool = False,
    max_lines: int | None = None,
    bib_keys: frozenset[str] | None = None,
    heartbeat_caps: dict[str, int] | None = None,
) -> list[str]:
    rel = path.relative_to(root) if path.is_relative_to(root) else path
    raw = path.read_text(encoding="utf-8")
    code, syntax = masks(raw)
    raw_lines = raw.split("\n")
    code_lines = code.split("\n")
    errors: list[str] = []

    in_complexity = rel.parts and rel.parts[0] == "Complexity"
    markers = upstream_markers(raw) if in_complexity else []
    if in_complexity and not any(UPSTREAM_STATUS_RE.fullmatch(status) for status in markers):
        errors.append(f"{rel}: missing or invalid `-- upstream:` marker")
    if in_complexity:
        errors.extend(check_docstring_links(raw, rel, root))
    if bib_keys is not None:
        errors.extend(check_docstring_citations(raw, rel, bib_keys))

    for idx, s_line in enumerate(syntax.split("\n"), 1):
        for m in FORBIDDEN_TOKEN_RE.finditer(s_line):
            errors.append(f"{rel}:{idx}: forbidden `{m.group(1)}`")

    for m in CUSTOM_AXIOM_RE.finditer(syntax):
        line_no = syntax.count("\n", 0, m.start()) + 1
        errors.append(f"{rel}:{line_no}: forbidden custom `axiom` declaration")

    for match in SET_OPTION_RE.finditer(code):
        idx = code.count("\n", 0, match.start())
        value_idx = code.count("\n", 0, match.end())
        if not any(has_nearby_comment(raw_lines, code_lines, line)
                   for line in range(idx, value_idx + 1)):
            errors.append(
                f"{rel}:{idx + 1}: `set_option {match.group(1)}` requires a justifying comment"
            )

    if heartbeat_caps is not None:
        cap = heartbeat_caps.get(rel.as_posix(), DEFAULT_MAX_HEARTBEATS)
        for line_no, value in heartbeat_budgets(code_lines):
            if value is None:
                errors.append(f"{rel}:{line_no}: cannot parse `set_option maxHeartbeats` budget")
            elif cap != 0 and (value == 0 or value > cap):
                errors.append(
                    f"{rel}:{line_no}: `set_option maxHeartbeats {value}` exceeds "
                    + (f"its allowlisted cap {cap}" if cap > DEFAULT_MAX_HEARTBEATS else
                       f"the {DEFAULT_MAX_HEARTBEATS} default; reduce the proof's cost, or add "
                       "the file to scripts/heartbeat_allowlist.txt with review")
                )

    if check_simp and any(re.match(r"candidate\b", status) for status in markers):
        for line_no in find_nonterminal_bare_simps(syntax):
            errors.append(f"{rel}:{line_no}: non-terminal bare `simp` (use `simp only`)")

    line_count = len(raw.splitlines())
    if max_lines is not None and line_count > max_lines:
        errors.append(f"{rel}: file has {line_count} lines (exceeds limit of {max_lines})")

    return errors


def check_bibliography(text: str, rel: str = "references.bib") -> list[str]:
    """Keys are unique and entries sorted by key, compared case-insensitively."""
    errors: list[str] = []
    entries = [(m.group(1), m.group(1).casefold(), text.count("\n", 0, m.start()) + 1)
               for m in BIB_KEY_RE.finditer(text)]
    seen: dict[str, int] = {}
    for key, folded, line in entries:
        if folded in seen:
            errors.append(f"{rel}:{line}: duplicate key `{key}` (first at line {seen[folded]})")
        seen.setdefault(folded, line)
    for (before, folded_before, _), (key, folded, line) in zip(entries, entries[1:]):
        if folded < folded_before:
            errors.append(f"{rel}:{line}: entry `{key}` comes after `{before}`; keep entries "
                          "sorted by key")
    return errors


def check_paths(
    paths: list[pathlib.Path],
    root: pathlib.Path = ROOT,
    check_simp: bool = False,
    max_lines: int | None = None,
    bib_keys: frozenset[str] | None = None,
    heartbeat_caps: dict[str, int] | None = None,
) -> list[str]:
    errors: list[str] = []
    checked = 0
    for p in paths:
        if not p.exists():
            errors.append(f"{p}: input path does not exist")
            continue
        if p.is_dir():
            files = sorted(p.rglob("*.lean"))
        else:
            files = [p]
        for f in files:
            checked += 1
            errors.extend(check_file(f, root=root, check_simp=check_simp, max_lines=max_lines,
                                     bib_keys=bib_keys, heartbeat_caps=heartbeat_caps))
    if not checked and not errors:
        errors.append("no source files found in selected paths")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "paths",
        nargs="*",
        help="Files or directories to check (defaults to library, test and abstract sources); "
             "the selection must contain at least one source file",
    )
    parser.add_argument(
        "--check-simp",
        action="store_true",
        help="Also flag non-terminal bare `simp` calls in candidate modules",
    )
    parser.add_argument(
        "--max-lines",
        type=int,
        default=None,
        help="Optional maximum line count per Lean file",
    )
    args = parser.parse_args()

    if args.paths:
        targets = [pathlib.Path(p).resolve() for p in args.paths]
    else:
        targets = [ROOT / "Complexity", ROOT / "ComplexityTests", ROOT / "abstracts/ComplexityAbstracts"]

    bibliography = (ROOT / "references.bib").read_text(encoding="utf-8")
    heartbeat_caps = load_heartbeat_allowlist()
    errors = check_paths(
        targets,
        root=ROOT,
        check_simp=args.check_simp,
        max_lines=args.max_lines,
        bib_keys=bibliography_keys(bibliography),
        heartbeat_caps=heartbeat_caps,
    )
    if not args.paths:
        errors += check_bibliography(bibliography)
        errors += check_heartbeat_allowlist_stale(heartbeat_caps)
    if errors:
        for err in errors:
            print(f"ERROR: {err}", file=sys.stderr)
        return 1
    print("All hygiene checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
