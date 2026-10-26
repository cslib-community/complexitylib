#!/usr/bin/env python3
"""Prepare a module of this library for a cslib pull request.

Usage:
    scripts/upstream.py Complexity.Foundations.Data.Encoding [more modules] \
        [--cslib ../cslib] [--no-mk-all] [--dry-run]

For each module the script
  * locates `Complexity/<Path>.lean` and the mirrored destination `<cslib>/Cslib/<Path>.lean`,
  * rewrites local imports, including `public`, `meta` and `all` modifiers, to `Cslib.`,
    mapping `Complexity.Init` to `Cslib.Init`, and likewise backticked module names
    (`` `Complexity.Foo.Bar` `` naming an existing module) in comments and docstrings,
  * drops standalone `-- upstream:` marker comments,
  * refuses to continue if the module imports a local module whose marker is not
    `merged`/`submitted` (those must be upstreamed first, in the same stack),
  * refuses to overwrite an existing destination file or symlink in the cslib checkout
    (additions to existing upstream files must be integrated manually),
  * writes the file, runs `lake exe mk_all` in the cslib checkout (unless --no-mk-all), and
  * prints a suggested PR title from the module docstring.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys

from proof_lengths import masks

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIB = "Complexity"
UPSTREAM_LIB = "Cslib"

HEADER_RE = re.compile(r"\s*(?:module\s+)?(?:prelude\s+)?")
IMPORT_RE = re.compile(r"(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(?P<module>\S+)\s*")
COMMENT_RE = re.compile(r"/-|--")
BLOCK_DELIMITER_RE = re.compile(r"/-|-/")
MARKER_RE = re.compile(r"^--\s*upstream:\s*(?P<status>.*?)\s*$")
TITLE_RE = re.compile(r"^#\s+(?P<title>.+?)\s*$", re.M)
MODULE_REF_RE = re.compile(r"`Complexity(?P<rest>(?:\.[A-Z][A-Za-z0-9_']*)+)`")


def module_to_path(module: str, root: pathlib.Path = ROOT) -> pathlib.Path:
    parts = module.split(".")
    if len(parts) < 2 or parts[0] != LIB or any(not p or "/" in p or "\\" in p for p in parts):
        sys.exit(f"error: invalid module {module!r}; expected {LIB}.<Name> with dot-separated components")
    return root.joinpath(*parts).with_suffix(".lean")


def comment_spans(text: str, code: str | None = None) -> list[tuple[int, int]]:
    """Locate whole comments using the shared lexer to exclude comment-like literals."""
    code = masks(text)[0] if code is None else code
    spans = []
    end = 0
    for match in COMMENT_RE.finditer(text):
        start = match.start()
        if start < end or code[start] != " ":
            continue
        if match[0] == "--":
            end = text.find("\n", start)
            end = len(text) if end < 0 else end
        else:
            depth = 1
            for delimiter in BLOCK_DELIMITER_RE.finditer(text, match.end()):
                depth += 1 if delimiter[0] == "/-" else -1
                if depth == 0:
                    end = delimiter.end()
                    break
        spans.append((start, end))
    return spans


def marker_match(text: str, start: int, end: int) -> re.Match[str] | None:
    """Only a standalone line comment is an upstream marker."""
    line_start = text.rfind("\n", 0, start) + 1
    if text[line_start:start].strip():
        return None
    return MARKER_RE.fullmatch(text[start:end])


def upstream_markers(text: str) -> list[str]:
    return [match.group("status") for start, end in comment_spans(text)
            if (match := marker_match(text, start, end))]


def marker_of(path: pathlib.Path) -> str | None:
    return next(iter(upstream_markers(path.read_text(encoding="utf-8"))), None)


def rewrite_module_ref(m: re.Match[str], root: pathlib.Path = ROOT) -> str:
    """Rewrite a backticked reference to an existing local module to its upstream name."""
    rest = m.group("rest")
    if root.joinpath(LIB, *rest[1:].split(".")).with_suffix(".lean").exists():
        return f"`{UPSTREAM_LIB}{rest}`"
    return m.group(0)


def rewrite(module: str, text: str, root: pathlib.Path = ROOT) -> tuple[str, list[str], str | None]:
    code, syntax = masks(text)
    edits: list[tuple[int, int, str]] = []
    local_imports: list[str] = []
    title: str | None = None
    # Lean's header permits comments/newlines between tokens and one module per import.
    # Stop at the first command so syntax quotations in the body are never rewritten.
    pos = HEADER_RE.match(syntax).end()
    while match := IMPORT_RE.match(syntax, pos):
        imported = match.group("module")
        if imported == LIB or imported.startswith(LIB + "."):
            local_imports.append(imported)
            start = match.start("module")
            edits.append((start, start + len(LIB), UPSTREAM_LIB))
        pos = match.end()

    for start, end in comment_spans(text, code):
        comment = text[start:end]
        if marker_match(text, start, end):
            line_start = text.rfind("\n", 0, start) + 1
            edits.append((line_start, end + (end < len(text)), ""))
            continue
        if comment.startswith("/-!") and title is None:
            if heading := TITLE_RE.search(comment):
                title = heading.group("title")
        rewritten = MODULE_REF_RE.sub(lambda match: rewrite_module_ref(match, root=root), comment)
        if rewritten != comment:
            edits.append((start, end, rewritten))

    for start, end, replacement in sorted(edits, reverse=True):
        text = text[:start] + replacement + text[end:]
    return text if text.endswith("\n") else text + "\n", local_imports, title


def suggest_title(module: str, title: str | None) -> str:
    parts = module.split(".")[1:]
    scope = parts[-2] if len(parts) >= 2 else parts[-1]
    desc = (title or parts[-1]).rstrip(".")
    if len(desc) > 1 and desc[1].islower():
        desc = desc[0].lower() + desc[1:]
    return f"feat({scope}): {desc}"


def destination_exists(dest: pathlib.Path) -> bool:
    """Return True if dest already exists on disk, including broken symlinks."""
    return dest.exists() or dest.is_symlink()


def main(argv: list[str] | None = None, root: pathlib.Path = ROOT) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("modules", nargs="+")
    ap.add_argument("--cslib", default=str(root.parent / "cslib"), help="path to a cslib checkout")
    ap.add_argument("--no-mk-all", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args(argv)

    cslib = pathlib.Path(args.cslib).resolve()
    if not (cslib / "lakefile.toml").exists():
        sys.exit(f"error: {cslib} is not a cslib checkout")

    requested = set(args.modules)
    planned: list[tuple[str, pathlib.Path, str | None, str, bool]] = []
    collisions: list[tuple[str, pathlib.Path]] = []

    for module in args.modules:
        src = module_to_path(module, root=root)
        if not src.exists():
            sys.exit(f"error: {src} does not exist")
        text = src.read_text(encoding="utf-8")
        new_text, local_imports, title = rewrite(module, text, root=root)

        for dep in local_imports:
            if dep == f"{LIB}.Init" or dep in requested:
                continue
            dep_path = module_to_path(dep, root=root)
            status = marker_of(dep_path) if dep_path.exists() else None
            if status is None or not (status.startswith("merged") or status.startswith("submitted")):
                sys.exit(
                    f"error: {module} imports {dep} whose upstream status is {status!r}; "
                    "upstream it first or include it in this invocation."
                )

        dest = cslib / UPSTREAM_LIB / src.relative_to(root / LIB)
        collides = destination_exists(dest)
        if collides:
            collisions.append((module, dest))
        planned.append((module, dest, title, new_text, collides))

    for module, dest, title, _, collides in planned:
        print(f"{module}\n  -> {dest}")
        print(f"  suggested PR title: {suggest_title(module, title)}")
        if collides:
            print(f"  existing destination: {dest} already exists; integrate additions manually")

    if collisions:
        details = ", ".join(f"{module} -> {dest}" for module, dest in collisions)
        sys.exit(
            f"error: refusing to overwrite existing upstream destination(s) ({details}); "
            "integrate additions to existing upstream files manually."
        )

    if not args.dry_run:
        for _, dest, _, new_text, _ in planned:
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_text(new_text, encoding="utf-8")

    if not args.dry_run and not args.no_mk_all:
        subprocess.run(["lake", "exe", "mk_all"], cwd=cslib, check=True)
        print("ran `lake exe mk_all` in", cslib)
    print("next: run cslib's gates there (build --wfail --iofail, mk_all --check, test, lint, lint-style)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
