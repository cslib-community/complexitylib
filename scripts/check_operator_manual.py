#!/usr/bin/env python3
"""Check current manual links, book chapter lists and Lean excerpt identity (stdlib only).

Relative `File.lean#L<n>` links must also start on a declaration, attribute, docstring or (for
ranges) section header. This does not fetch URLs, elaborate Lean, audit mathematical meaning,
check that a source line link names the declaration it starts on, or assert that historical
evidence describes the current checkout. Run from any working directory.
"""
from __future__ import annotations

import argparse
import html
import importlib.util
import json
import re
import sys
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'manual/data'))
from visuals import check_markup

EXCLUDED = {"_build", "_generated", "__pycache__"}
FENCE = re.compile(r"^\s*(`{3,}|~{3,})(.*)$")

# A relative `File.lean#L<a>[-L<b>]` link must start where the cited Lean text starts (#3991):
# an unindented declaration (after optional modifiers), attribute or docstring outside any
# comment, so not a structure field's docstring. Ranges may also start at a section header;
# `#L1` links the whole file.
DECLARATION_START = re.compile(
    r"(?:@\[|/--|(?:(?:private|protected|public|noncomputable|partial|unsafe|nonrec|meta|scoped"
    r"|local)\s+)*(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|example)\b)")
SECTION_START = re.compile(r"(?:/-!|(?:(?:public|noncomputable)\s+)*(?:section|namespace)\b)")
STALE_SOURCE_ANCHOR = "source line anchor does not start a declaration"
# Anchors, as (Lean file, start line), that are stale or that queued pull requests will make
# stale; the check tolerates them until they can be repointed without conflicting with or
# ejecting those pull requests. Repoint the manual link and delete the entry (#3991). An entry
# that no longer matches is listed in the result, not reported as an error, so a pull request
# that repoints a link does not have to edit this list.
STALE_SOURCE_ANCHORS: set[tuple[str, int]] = {
    # Stale on main. #3728 edits the manual paragraph that links it.
    ("CslibFrontier/Crypto/Computational/TreeSignature/Security.lean", 4779),
    # Stale on main. #3981 moves this file's declarations.
    ("CslibFrontier/Computability/StreamArithmetic/Interface.lean", 243),
    ("CslibFrontier/Computability/StreamArithmetic/Interface.lean", 528),
    # Stale on main. #3875 moves this file's declarations.
    *(("CslibFrontier/Crypto/Protocols/SigmaProtocol/Interactive.lean", line)
      for line in (197, 213, 226, 285, 342, 352, 395, 444, 600)),
    # Correct on main, but queued #3875 and #3977 move these declarations without repointing.
    *(("CslibFrontier/Crypto/Protocols/SigmaProtocol/Computational.lean", line)
      for line in (107, 217, 228, 243)),
    ("CslibFrontier/Crypto/Protocols/VOLE/Basic.lean", 175),
    ("CslibFrontier/Foundations/NumberTheory/Primality/EulerLiars.lean", 152),
    ("CslibFrontier/Foundations/NumberTheory/Primality/RabinMonier.lean", 343),
    ("CslibFrontier/Foundations/NumberTheory/Primality/StrongLiars.lean", 222),
}


def prose(text: str) -> str:
    """Ignore fenced and inline code when scanning Markdown links/headings."""
    result = []
    fence = None
    for line in text.splitlines():
        match = FENCE.match(line)
        if fence is not None:
            if match and match[1][0] == fence[0] and len(match[1]) >= len(fence):
                fence = None
            continue
        if match:
            fence = match[1]
            continue
        result.append(re.sub(r"(`+).*?\1", "", line))
    return "\n".join(result)


def anchors(text: str) -> set[str]:
    # GitHub-style heading IDs, including repeated headings and explicit HTML IDs.
    active = prose(text)
    found = set(re.findall(r'<a\s+(?:[^>]*?\s)?id=["\']([^"\']+)', active))
    counts: dict[str, int] = {}
    for heading in re.findall(r"^\s{0,3}#{1,6}\s+(.+?)\s*#*\s*$", active, re.M):
        heading = re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", heading)
        heading = re.sub(r"<[^>]+>", "", html.unescape(heading)).lower()
        slug = re.sub(r"[^\w\-\s]", "", heading).replace(" ", "-")
        number = counts.get(slug, 0)
        counts[slug] = number + 1
        found.add(slug if number == 0 else f"{slug}-{number}")
    return found


def links(text: str) -> tuple[list[str], list[str]]:
    active = prose(text)
    definitions = {k.casefold(): v for k, v in re.findall(
        r"^\s{0,3}\[([^\]]+)\]:\s*<?([^\s>]+)>?", active, re.M)}
    targets = re.findall(r"\]\(\s*(?:<([^>]+)>|([^\s)]+))", active)
    urls = [a or b for a, b in targets] + list(definitions.values())
    missing = []
    for display, key in re.findall(r"\[([^\]\n]+)\]\[([^\]\n]*)\]", active):
        key = (key or display).casefold()
        if key not in definitions:
            missing.append(key)
        else:
            urls.append(definitions[key])
    return urls, missing


def within(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
        return True
    except ValueError:
        return False


def comment_depths(lines: list[str]) -> list[int]:
    """Nesting depth of Lean block comments (`/- … -/`, docstrings included) at each line start.

    Line comments and string literals are skipped so that `--`, `"/-"` or `"-/"` do not count.
    """
    depths, depth = [], 0
    for line in lines:
        depths.append(depth)
        i, in_string = 0, False
        while i < len(line):
            pair = line[i:i + 2]
            if depth:
                depth += (pair == "/-") - (pair == "-/")
                i += 2 if pair in ("/-", "-/") else 1
            elif in_string:
                in_string = line[i] != '"'
                i += 2 if line[i] == "\\" else 1
            elif pair == "--":
                break
            elif pair == "/-":
                depth, i = 1, i + 2
            elif line[i:i + 3] == "'\"'":
                i += 3
            else:
                in_string = line[i] == '"'
                i += 1
    return depths


def source_anchor_error(fragment: str, lines: list[str]) -> str | None:
    """Problem with a `L<a>[-L<b>]` fragment into a Lean file with these lines, or `None`."""
    bounds = [int(n) for n in re.findall(r"\d+", fragment)]
    if min(bounds) < 1 or max(bounds) > len(lines):
        return "source line anchor out of bounds"
    start = bounds[0]
    if start == 1:
        return None
    line = lines[start - 1]
    if comment_depths(lines[:start])[-1] == 0 and (
            DECLARATION_START.match(line) or len(bounds) > 1 and SECTION_START.match(line)):
        return None
    return STALE_SOURCE_ANCHOR


def load_book_builder(data: Path):
    """Import `data/build_manual.py` with its own sibling modules, leaving `sys.modules` as found."""
    siblings = {path.stem for path in data.glob("*.py")}
    saved = {name: sys.modules.pop(name) for name in siblings if name in sys.modules}
    sys.path.insert(0, str(data))
    try:
        spec = importlib.util.spec_from_file_location("checked_build_manual", data / "build_manual.py")
        book = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(book)
        return book
    finally:
        sys.path.remove(str(data))
        for name in siblings:
            sys.modules.pop(name, None)
        sys.modules.update(saved)


def book_input_errors(repo: Path, manual: Path) -> list[str]:
    """Run the PDF builder's chapter-list check, which otherwise fails only in the Pandoc build."""
    data = manual / "data"
    book = load_book_builder(data)
    try:
        book.validate_inputs(manual, book.FILES)
    except ValueError as error:
        place = data.relative_to(repo).as_posix() if within(data, repo) else str(data)
        return [f"{error}. The book's chapter lists are ORDER in {place}/build_latex.py (reference "
                f"and history chapters) and WORKFLOWS or APPENDICES in {place}/build_manual.py: "
                "add each 'missing' page there and remove 'extra' or duplicate entries."]
    return []


def check(repo: Path, manual: Path | None = None) -> dict:
    repo = repo.resolve()
    manual = (manual or repo / "manual").resolve()
    errors: list[str] = []
    documents = sorted(p for p in manual.rglob("*.md")
                       if not EXCLUDED.intersection(p.relative_to(manual).parts))
    document_set = set(documents)
    edges = {p: set() for p in documents}
    link_count = 0
    allowed_stale: set[tuple[str, int]] = set()
    visual_counts = {'diagrams': 0, 'worked_examples': 0}
    for doc in documents:
        try:
            for key, value in check_markup(doc.read_text()).items():
                visual_counts[key] += value
        except ValueError as error:
            errors.append(f'{doc.relative_to(manual)}: {error}')
        urls, undefined = links(doc.read_text())
        errors.extend(f"{doc.relative_to(manual)}: undefined reference [{key}]" for key in undefined)
        for url in urls:
            parsed = urlsplit(html.unescape(url))
            if parsed.scheme or parsed.netloc:
                continue
            link_count += 1
            target = (doc.parent / unquote(parsed.path)).resolve() if parsed.path else doc
            if not within(target, repo):
                errors.append(f"{doc.relative_to(manual)}: local link escapes repository: {url}")
                continue
            if not target.exists():
                errors.append(f"{doc.relative_to(manual)}: missing local link: {url}")
                continue
            if target in document_set:
                edges[doc].add(target)
            fragment = unquote(parsed.fragment)
            if fragment and target.suffix == ".md" and fragment not in anchors(target.read_text()):
                errors.append(f"{doc.relative_to(manual)}: missing Markdown anchor: {url}")
            elif fragment and target.suffix == ".lean" and re.fullmatch(r"L\d+(?:-L\d+)?", fragment):
                problem = source_anchor_error(fragment, target.read_text().splitlines())
                known = (target.relative_to(repo).as_posix(), int(re.match(r"L(\d+)", fragment)[1]))
                if problem == STALE_SOURCE_ANCHOR and known in STALE_SOURCE_ANCHORS:
                    allowed_stale.add(known)
                elif problem:
                    errors.append(f"{doc.relative_to(manual)}: {problem}: {url}")
    start = manual / "README.md"
    if start not in document_set:
        errors.append("Missing manual/README.md entry page")
    if manual / "AGENT_OPERATORS.md" not in document_set:
        errors.append("Missing manual/AGENT_OPERATORS.md human driver manual")
    # Manuals without the builder (test fixtures) skip the chapter-list check; the builder's
    # check also requires AGENT_OPERATORS.md, which is reported above when absent.
    book_checked = ((manual / "data/build_manual.py").is_file()
                    and manual / "AGENT_OPERATORS.md" in document_set)
    if book_checked:
        errors.extend(book_input_errors(repo, manual))
    pending, reachable = [start], set()
    while pending:
        path = pending.pop()
        if path in reachable:
            continue
        reachable.add(path)
        pending.extend(edges.get(path, set()) - reachable)
    errors.extend(f"Unreachable manual page: {p.relative_to(manual)}"
                  for p in sorted(document_set - reachable))

    rows = []
    for manifest in sorted((manual / "workflows/data").glob("*-excerpts.json")):
        try:
            data = json.loads(manifest.read_text())
            if not isinstance(data, list):
                raise ValueError("expected a list")
            rows.extend(data)
        except (ValueError, OSError) as exc:
            errors.append(f"{manifest.relative_to(manual)}: {exc}")
    ids, observed, excerpt_results = set(), {}, []
    for doc in (manual / "workflows").glob("*.md"):
        text = doc.read_text()
        blocks = re.findall(r"<!-- excerpt: ([\w-]+) -->\s*```lean\n(.*?)\n```", text, re.S)
        lean_blocks = re.findall(r"^```lean\s*\n", text, re.M)
        if len(blocks) != len(lean_blocks):
            errors.append(f"{doc.relative_to(manual)}: unregistered Lean block")
        for key, body in blocks:
            if key in observed:
                errors.append(f"Duplicate excerpt marker: {key}")
            observed[key] = (doc, body)
    for row in rows:
        if not isinstance(row, dict) or not all(isinstance(row.get(k), str)
                                               for k in ("id", "document", "source_path")):
            errors.append("Invalid excerpt manifest row: expected id, document and source_path")
            continue
        key = row["id"]
        if key in ids:
            errors.append(f"Duplicate excerpt manifest ID: {key}")
        ids.add(key)
        doc = (manual / row["document"]).resolve()
        source = (repo / row["source_path"]).resolve()
        if not within(doc, manual) or not within(source, repo):
            errors.append(f"{key}: excerpt path escapes its root")
            continue
        if key not in observed or observed[key][0] != doc:
            errors.append(f"{key}: missing marker in {row['document']}")
            continue
        if not source.is_file():
            errors.append(f"{key}: missing source file {row['source_path']}")
            continue
        body = observed[key][1]
        excerpt_lines, source_lines = body.splitlines(), source.read_text().splitlines()
        positions = [i for i in range(len(source_lines) - len(excerpt_lines) + 1)
                     if source_lines[i:i + len(excerpt_lines)] == excerpt_lines]
        if len(positions) != 1:
            errors.append(f"{key}: expected one exact source match, found {len(positions)} in {row['source_path']}")
            continue
        doc_urls, _ = links(doc.read_text())
        linked = any(not urlsplit(url).scheme and
                     (doc.parent / unquote(urlsplit(url).path)).resolve() == source
                     for url in doc_urls)
        if not linked:
            errors.append(f"{key}: document must link the complete source client")
        excerpt_results.append({"id": key, "source_path": row["source_path"],
                                "start_line": positions[0] + 1,
                                "end_line": positions[0] + len(excerpt_lines)})
    errors.extend(f"Excerpt marker absent from manifests: {key}" for key in sorted(set(observed) - ids))
    if not rows:
        errors.append("No contextual Lean excerpts registered")
    return {"status": "fail" if errors else "pass", "manual_documents": len(documents),
            "local_links_checked": link_count, "excerpts_checked": len(excerpt_results),
            "book_inputs_checked": book_checked, **visual_counts,
            "allowed_stale_source_anchors": sorted(f"{path}#L{line}" for path, line in allowed_stale),
            "unused_stale_source_anchor_entries": sorted(
                f"{path}#L{line}" for path, line in STALE_SOURCE_ANCHORS - allowed_stale),
            "excerpts": excerpt_results, "errors": errors, "lean_compilation": False,
            "external_links_fetched": False, "historical_revision_checked": False}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=ROOT)
    parser.add_argument("--manual", type=Path, help="Manual root (default: REPO/manual)")
    parser.add_argument("--output", type=Path, help="Optional JSON result path")
    args = parser.parse_args()
    result = check(args.repo, args.manual)
    encoded = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")
    return bool(result["errors"])


if __name__ == "__main__":
    raise SystemExit(main())
