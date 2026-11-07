#!/usr/bin/env python3
"""Check current manual links, book chapter lists and Lean excerpt identity (stdlib only).

This does not fetch URLs, elaborate Lean, audit mathematical meaning, or assert that
historical evidence describes the current checkout. Run from any working directory.
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


def load_book_builder(data: Path):
    """Import `data/build_manual.py` with its own sibling modules, leaving `sys.modules` as found."""
    siblings = ("build_latex", "visuals")
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
                bounds = [int(n) for n in re.findall(r"\d+", fragment)]
                if min(bounds) < 1 or max(bounds) > len(target.read_text().splitlines()):
                    errors.append(f"{doc.relative_to(manual)}: source line anchor out of bounds: {url}")
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
