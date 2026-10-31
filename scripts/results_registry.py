#!/usr/bin/env python3
# Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Christian Reitwiessner
"""Collect named results alongside the selected abstracts; validate their declaration links.

This checks references, not mathematical correspondence or completeness of coverage.
`--compiled` uses the same Lean output reader as the tidy/declaration audits.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess
from urllib.parse import quote

import build_abstracts
import check_hygiene
import lean_outputs

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "https://github.com/cslib-community/complexitylib/blob/main/"
API = "https://www.cslib.io/complexitylib/"


def module_path(module: str, root: Path) -> Path:
    if not re.fullmatch(r"(?:Complexity|ComplexityAbstracts)(?:\.[A-Za-z_][A-Za-z0-9_]*)+", module):
        raise ValueError(f"Unsupported module: {module}")
    relative = Path(module.replace(".", "/") + ".lean")
    return root / (Path("abstracts") / relative if module.startswith("ComplexityAbstracts.")
                   else relative)


def module_citations(path: Path) -> list[str]:
    """Module citations are discovery context, never inferred theorem/source equivalences."""
    return sorted({key for _, doc in check_hygiene.extract_docstrings(path.read_text())
                   for _, key in check_hygiene.docstring_citations(doc)})


def collect(root: Path = ROOT) -> list[dict]:
    manifest = json.loads((root / "results/registry.json").read_text())
    if not isinstance(manifest, dict) or manifest.get("schema_version") != 1:
        raise ValueError("Unsupported registry schema")
    if manifest.get("abstract_catalogue") != "abstracts/catalogue.json":
        raise ValueError("The registry must reuse abstracts/catalogue.json")
    entries = []
    for abstract in build_abstracts.load_catalogue(root / manifest["abstract_catalogue"], root):
        module = abstract["module"]
        entries.append({"id": abstract["id"], "title": abstract["title"],
                        "topic": "selected abstracts", "module": module,
                        "theorems": abstract["headline_theorems"], "scope": abstract["scope"],
                        "abstract_id": abstract["id"], "source_review": "module-citations",
                        "sources": [{"bib_key": key, "locator": None}
                                    for key in module_citations(module_path(module, root))]})
    if not isinstance(manifest.get("results"), list):
        raise ValueError("Registry results must be a list")
    for entry in manifest["results"]:
        if not isinstance(entry, dict) or entry.get("source_review") != "recorded":
            raise ValueError("New inventory entries must identify source_review as recorded")
        entries.append(entry)
    validate(entries, root)
    return entries


def validate(entries: list[dict], root: Path) -> None:
    bib_keys = set(check_hygiene.BIB_KEY_RE.findall((root / "references.bib").read_text()))
    ids, declarations = set(), set()
    for entry in entries:
        for key in ("id", "title", "topic", "module", "scope"):
            if not isinstance(entry.get(key), str) or not entry[key].strip():
                raise ValueError(f"Result needs a nonempty {key}")
        if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", entry["id"]) or entry["id"] in ids:
            raise ValueError(f"Invalid or duplicate result id: {entry['id']}")
        ids.add(entry["id"])
        source = module_path(entry["module"], root)
        if not source.is_file():
            raise ValueError(f"Missing result module: {entry['module']}")
        if not isinstance(entry.get("theorems"), list) or not entry["theorems"]:
            raise ValueError(f"No theorems for {entry['id']}")
        for name in entry["theorems"]:
            if not isinstance(name, str) or not name or any(c.isspace() for c in name):
                raise ValueError(f"Invalid theorem name: {name!r}")
            if name in declarations:
                raise ValueError(f"Duplicate theorem: {name}")
            declarations.add(name)
        if not isinstance(entry.get("sources"), list):
            raise ValueError(f"Sources must be a list: {entry['id']}")
        if entry["source_review"] == "recorded" and not entry["sources"]:
            raise ValueError(f"Recorded sources required: {entry['id']}")
        seen = set()
        for reference in entry["sources"]:
            if not isinstance(reference, dict) or reference.get("bib_key") not in bib_keys:
                raise ValueError(f"Unknown bibliography reference: {reference!r}")
            key = reference["bib_key"]
            if key in seen:
                raise ValueError(f"Duplicate reference: {key}")
            seen.add(key)
            locator = reference.get("locator")
            if locator is not None and (not isinstance(locator, str) or not locator.strip()):
                raise ValueError(f"Invalid source locator: {key}")


def validate_constants(entries: list[dict], constants: dict[str, dict]) -> None:
    for entry in entries:
        for name in entry["theorems"]:
            row = constants.get(name)
            if not row or row["m"] != entry["module"] or row["k"] != "thm" or not row["e"]:
                raise ValueError(f"Not a public theorem defined in {entry['module']}: {name}")



def compiled_constants(entries: list[dict]) -> dict[str, dict]:
    modules = sorted({e["module"] for e in entries})
    # Do not certify a renamed/removed declaration from stale local output. CI has already
    # built these modules, so this is a cheap freshness assertion rather than another build.
    lean_outputs.run(["lake", "build", "--no-build", *modules], capture_output=True)
    constants, _ = lean_outputs.load_constants(lean_outputs.DEFAULT_BUILD_DIR, modules)
    return constants

def bibliography_links(root: Path) -> dict[str, str]:
    text = (root / "references.bib").read_text()
    return {m.group(1): REPOSITORY + "references.bib#L" + str(text.count("\n", 0, m.start()) + 1)
            for m in check_hygiene.BIB_KEY_RE.finditer(text)}


def markdown(entries: list[dict], root: Path = ROOT, papers: bool = False) -> str:
    links = bibliography_links(root)
    title = "Referenced works: initial inventory" if papers else "Formalized results: initial inventory"
    lines = ["# " + title, "",
             "Incomplete coverage. Source locators are recorded from repository documentation,",
             "not newly source-verified. Abstract module citations are context, not result mappings.", ""]
    groups: dict[str, list[dict]] = {}
    for entry in entries:
        keys = [r["bib_key"] for r in entry["sources"]] if papers else [entry["topic"]]
        for key in keys:
            groups.setdefault(key, []).append(entry)
    for group, results in sorted(groups.items()):
        label = f"[{group}]({links[group]})" if papers else group
        lines.extend([f"## {label}", ""])
        for entry in results:
            lines.extend([f"### {entry['title']}", "", entry["scope"], ""])
            for name in entry["theorems"]:
                if entry["module"].startswith("ComplexityAbstracts."):
                    source = module_path(entry["module"], root)
                    line = build_abstracts.declaration_line(source.read_text(), name)
                    target = REPOSITORY + source.relative_to(root).as_posix() + f"#L{line}"
                else:
                    target = API + entry["module"].replace(".", "/") + ".html#" + quote(name)
                lines.append(f"- [`{name}`]({target})")
            if entry.get("abstract_id"):
                lines.append(f"- [Formal abstract]({API}abstracts/{entry['abstract_id']}.pdf)")
            sources = [f"[{r['bib_key']}]({links[r['bib_key']]})" +
                       (f" ({r['locator']})" if r.get("locator") else " (locator not collected)")
                       for r in entry["sources"]]
            lines.extend(["", f"References ({entry['source_review']}): " + (", ".join(sources) or
                          "none collected; inspect the abstract and bridge documentation"), ""])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiled", action="store_true", help="require built public theorem metadata")
    parser.add_argument("--markdown", action="store_true", help="print the result/topic index")
    parser.add_argument("--papers", action="store_true", help="print the index grouped by bibliography key")
    args = parser.parse_args()
    try:
        entries = collect()
        if args.compiled:
            validate_constants(entries, compiled_constants(entries))
        if args.markdown or args.papers:
            print(markdown(entries, papers=args.papers))
        else:
            keys = {r["bib_key"] for e in entries for r in e["sources"]}
            print(f"{len(entries)} result groups; {sum(len(e['theorems']) for e in entries)} "
                  f"theorems; {len(keys)} bibliography keys. Coverage/source review remain incomplete.")
    except subprocess.CalledProcessError as error:
        parser.exit(1, "Registry metadata check failed; build the registered modules first.\n" +
                    (error.stderr or str(error)))
    except (ValueError, OSError, KeyError, TypeError) as error:
        parser.exit(1, f"Registry error: {error}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
