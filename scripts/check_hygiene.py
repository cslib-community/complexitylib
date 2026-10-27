#!/usr/bin/env python3
"""Static proof-hygiene and module-template checks for Complexitylib Lean files.

Checks enforced by default (see AGENTS.md):
1. Every module under Complexity/ has a valid `-- upstream:` marker.
2. No `sorry`, custom `axiom`, or `native_decide` in Complexity/, ComplexityTests/ or the
   dedicated abstract library.
3. Every `set_option maxHeartbeats` or `set_option maxRecDepth` has an explanatory comment
   on the same line, within the preceding 3 lines, or (for `set_option ... in`) on the next
   line, where Mathlib's `linter.style.maxHeartbeats` expects it.
4. Docstrings in `Complexity/` contain only root-qualified or external inline Markdown links
   (`[text](target)`, where external means `http://` or `https://` and anchors start with `#`,
   matching `doc-gen4`'s `extendLink`) and root-qualified slash-containing `.lean` code tokens
   (`Complexity/.../*.lean`, `Cslib/...`, `Mathlib/...`) in inline code spans and fenced Lean code
   blocks. `Complexity/...` targets are checked for file existence on disk; dependency roots
   (`Cslib/`, `Mathlib/`, `Batteries/`) are checked on disk when `.lake/packages` is present locally
   and by root prefix in CI (where `check_hygiene.py` runs before `.lake` is restored) or for
   toolchain roots (`Std/`, `Init/`, `Lean/`). Reference-link definitions (`[label]: target`) and
   indented (4-space) code blocks are not scanned; `scripts/check_docs.py` in `docs.yml` remains the
   full HTML backstop.
5. (Default selection only.) `references.bib` keys are unique and its entries are sorted by key,
   both compared case-insensitively as BibTeX does, so that PRs adding entries rarely conflict.

Opt-in heuristic checks:
6. (`--check-simp`) Flag non-terminal bare `simp` tactics in `-- upstream: candidate` modules
   under Complexity/.
7. (`--max-lines N`) Flag Lean files exceeding N lines.
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

UPSTREAM_MARKER_RE = re.compile(
    r"^--\s*upstream:\s*(?:"
    r"candidate(?:\s+.*)?|"
    r"submitted\s+#\d+(?:\s+@[0-9a-f]{7,40})?(?:\s+.*)?|"
    r"(?:vendored|subset of)\s+\S+(?:\s+@[0-9a-f]{7,40})?(?:\s+.*)?|"
    r"merged\s+@[0-9a-f]{7,40}(?:\s+.*)?|"
    r"local-only\s+\([^)]+\)"
    r")\s*$",
    re.M,
)

FORBIDDEN_TOKEN_RE = re.compile(r"\b(sorry|native_decide)\b")
CUSTOM_AXIOM_RE = re.compile(
    r"^\s*(?:@\[(?:[^\[\]\n]|\[[^\[\]\n]*\])*\]\s*)*(?:(?:public|private|protected|noncomputable|scoped|local)\s+)*axiom\b",
    re.M,
)
SET_OPTION_RE = re.compile(r"^\s*set_option\s+(maxHeartbeats|maxRecDepth)\b")
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
    r"|(?P<code_fence>`+)(?P<code>.+?)(?<!`)(?P=code_fence)(?!`)"
)
WHITESPACE_RUN_RE = re.compile(r"\S+")


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
    """Validate a Markdown link target `[text](target)` in a `Complexity/` docstring."""
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
    return errors


def is_candidate_module(text: str) -> bool:
    return bool(re.search(r"^--\s*upstream:\s*candidate\b", text, re.M))


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


def check_file(
    path: pathlib.Path,
    root: pathlib.Path = ROOT,
    check_simp: bool = False,
    max_lines: int | None = None,
) -> list[str]:
    rel = path.relative_to(root) if path.is_relative_to(root) else path
    raw = path.read_text(encoding="utf-8")
    code, syntax = masks(raw)
    raw_lines = raw.split("\n")
    code_lines = code.split("\n")
    errors: list[str] = []

    in_complexity = rel.parts and rel.parts[0] == "Complexity"
    if in_complexity and not UPSTREAM_MARKER_RE.search(raw):
        errors.append(f"{rel}: missing or invalid `-- upstream:` marker")
    if in_complexity:
        errors.extend(check_docstring_links(raw, rel, root))

    for idx, s_line in enumerate(syntax.split("\n"), 1):
        for m in FORBIDDEN_TOKEN_RE.finditer(s_line):
            errors.append(f"{rel}:{idx}: forbidden `{m.group(1)}`")

    for m in CUSTOM_AXIOM_RE.finditer(syntax):
        line_no = syntax.count("\n", 0, m.start()) + 1
        errors.append(f"{rel}:{line_no}: forbidden custom `axiom` declaration")

    for idx, c_line in enumerate(code_lines):
        m_opt = SET_OPTION_RE.match(c_line)
        if m_opt and not has_nearby_comment(raw_lines, code_lines, idx):
            errors.append(
                f"{rel}:{idx + 1}: `set_option {m_opt.group(1)}` requires a justifying comment"
            )

    if check_simp and in_complexity and is_candidate_module(raw):
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
            errors.extend(check_file(f, root=root, check_simp=check_simp, max_lines=max_lines))
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

    errors = check_paths(
        targets,
        root=ROOT,
        check_simp=args.check_simp,
        max_lines=args.max_lines,
    )
    if not args.paths:
        errors += check_bibliography((ROOT / "references.bib").read_text(encoding="utf-8"))
    if errors:
        for err in errors:
            print(f"ERROR: {err}", file=sys.stderr)
        return 1
    print("All hygiene checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
