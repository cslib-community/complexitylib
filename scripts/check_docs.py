#!/usr/bin/env python3
"""Check documentation pins, module/search coverage and the guide's links (Python 3.11+)."""

import argparse
from contextlib import closing
import gzip
import html
import json
from pathlib import Path
import posixpath
import re
import shutil
import sqlite3
import tempfile
import tomllib
from urllib.parse import unquote, urlsplit
import urllib.request


ROOT = Path(__file__).resolve().parents[1]
LOCAL_DOC_ROOTS = ("Complexity", "Cslib")
NON_EXTERNAL_ROOTS = frozenset({
    *LOCAL_DOC_ROOTS,
    "abstracts",
    "declarations",
    "find",
    "guide",
    "src",
})
SHELL_DOC_PAGES = frozenset({
    "404.html",
    "foundational_types.html",
    "index.html",
    "navbar.html",
    "references.html",
    "search.html",
    "tactics.html",
})
LOCAL_DECLARATION_PREFIXES = (
    "./Complexity/",
    "./Complexity.html",
    "./Cslib/",
    "./Cslib.html",
)
# Where the guide and trimmed API docs link declarations.
API_DOCS_URL = "https://www.cslib.io/complexitylib/"
MATHLIB_DOCS_URL = "https://leanprover-community.github.io/mathlib4_docs/"
PUBLISHED_INDEX_URL = f"{MATHLIB_DOCS_URL}declarations/declaration-data.bmp"
EXTERNAL_TARGETS_FILE = "external-doc-targets.json"
KERNEL_RECURSOR_ANCHORS = frozenset({
    ("Init/Prelude.html", "Eq.rec"),
    ("Init/Prelude.html", "Eq.ndrec"),
})
HREF_RE = re.compile(r'href="([^"]*)"')
ID_ATTR_RE = re.compile(r'id="([^"]*)"')
DEP_BROKEN_LINK_RE = re.compile(
    r'<code><a href="([^"]+)">([^<]*\.lean)</a></code>'
    r'|<a href="([^"]+)">(<code>[^<]+</code>)</a>'
    r'|<a href="([^"]*(?:lean-manual://|\.lean|/fderiv\.html)[^"]*)">([^<]*)</a>'
)
NAV_LINK_RE = re.compile(
    r'<div class="nav_link"><a href="\./([^"]+)">[^<]*</a></div>'
    r'|\s*\(<a href="\./([^"]+)">file</a>\)'
)
EMPTY_NAV_SECT_RE = re.compile(
    r'<details class="nav_sect"[^>]*><summary>[^<]*</summary></details>'
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


LOCKED_KEYS = ("type", "url", "rev", "subDir")


def check_project(project, label, generator_name, root_packages, toolchain):
    """Check a documentation project that shares the library's toolchain and package checkouts."""
    lockfile = f"{project}/lake-manifest.json"
    manifest = json.loads((ROOT / lockfile).read_text())
    packages = {p["name"].strip("«»"): p for p in manifest["packages"]}
    for package in root_packages:
        locked = packages.get(package["name"])
        require(locked is not None,
                f"{label} lockfile omits {package['name']}; copy its entry from "
                f"lake-manifest.json into {lockfile}")
        for key in LOCKED_KEYS:
            require(package.get(key) == locked.get(key),
                    f"{label} lockfile differs for {package['name']}: {key} is "
                    f"{json.dumps(locked.get(key))} in {lockfile} but "
                    f"{json.dumps(package.get(key))} in lake-manifest.json; update {lockfile} "
                    f"to match the root pin")
    require((ROOT / project / "lean-toolchain").read_text().strip() == toolchain,
            f"{label} toolchain differs from the library")
    config = tomllib.loads((ROOT / project / "lakefile.toml").read_text())
    generator = next(p for p in config["require"] if p["name"] == generator_name)
    require(generator["rev"] == toolchain.rsplit(":", 1)[-1],
            f"{generator_name} tag must match the Lean version")
    require(packages[generator_name]["inputRev"] == generator["rev"],
            f"{label} lockfile has a stale {generator_name} tag")
    return packages


def check_config():
    root_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    docs_packages = check_project("docbuild", "Documentation", "doc-gen4",
                                  root_manifest["packages"], toolchain)
    guide_packages = check_project("guide", "Guide", "verso", root_manifest["packages"], toolchain)
    # Both projects check out their packages into the library's .lake/packages.
    for name in sorted(docs_packages.keys() & guide_packages.keys()):
        for key in LOCKED_KEYS:
            require(docs_packages[name].get(key) == guide_packages[name].get(key),
                    f"Guide and documentation lockfiles differ for {name}: {key}")
    require((ROOT / "docbuild/docs/references.bib").read_bytes()
            == (ROOT / "references.bib").read_bytes(),
            "Documentation bibliography differs from references.bib")
    # scripts/check_hygiene.py checks the bibliography's keys.


def local_modules(names):
    return {name for name in names if name == "Complexity" or name.startswith("Complexity.")}


def resolve_relative_href(rel_page, href):
    if not href:
        return None
    split = urlsplit(html.unescape(href))
    if split.scheme or split.netloc or not split.path:
        return None
    page_dir = posixpath.dirname(rel_page)
    raw_path = unquote(split.path)
    joined = posixpath.join(page_dir, raw_path) if page_dir else raw_path
    return posixpath.normpath(joined)


def resolve_doc_target(docs, norm_path):
    if not norm_path or norm_path == ".." or norm_path.startswith(("/", "../")):
        return None
    docs_root = docs.resolve()
    target = docs_root / ("index.html" if norm_path == "." else norm_path)
    if target.is_dir():
        target = target / "index.html"
    resolved = target.resolve()
    if not resolved.is_relative_to(docs_root):
        return None
    return resolved


def is_published_doc_file(docs, norm_path):
    target = resolve_doc_target(docs, norm_path)
    return target is not None and target.is_file()


def split_href_target(raw_target):
    before_hash, has_hash, fragment = raw_target.partition("#")
    path_part, has_query, query = before_hash.partition("?")
    return (
        path_part,
        (query if has_query else None),
        (fragment if has_hash and fragment else None),
    )


def normalize_doc_relpath(rel_path):
    if not rel_path:
        return None
    norm = posixpath.normpath(rel_path)
    if not norm or norm in (".", "..") or norm.startswith(("/", "../")):
        return None
    return norm


def is_external_doc_relpath(norm):
    if not norm or norm in SHELL_DOC_PAGES or not norm.endswith(".html"):
        return False
    top = norm.split("/", 1)[0]
    if "/" not in norm:
        top = top[:-len(".html")]
    return top not in NON_EXTERNAL_ROOTS


def page_anchors(page_path, cache=None):
    if cache is not None and page_path in cache:
        return cache[page_path]
    anchors = {html.unescape(i) for i in ID_ATTR_RE.findall(page_path.read_text())}
    if cache is not None:
        cache[page_path] = anchors
    return anchors


def collect_guide_external_pages():
    guide_dir = ROOT / "guide/.lake/build/site/html-multi"
    if not guide_dir.is_dir():
        return set()
    pages = set()
    for base_url in (MATHLIB_DOCS_URL, API_DOCS_URL):
        pattern = re.compile(r'href="' + re.escape(base_url) + r'([^"]*)"')
        for html_page in sorted(guide_dir.rglob("*.html")):
            for target in pattern.findall(html_page.read_text()):
                path_part, _, _ = split_href_target(html.unescape(target))
                norm = normalize_doc_relpath(unquote(path_part))
                if is_external_doc_relpath(norm):
                    pages.add(norm)
    return pages


def fetch_published_external_index():
    request = urllib.request.Request(
        PUBLISHED_INDEX_URL,
        headers={"Accept-Encoding": "gzip"},
    )
    with urllib.request.urlopen(request, timeout=30) as response:
        raw = response.read()
        if response.headers.get("Content-Encoding") == "gzip":
            raw = gzip.decompress(raw)
    return json.loads(raw)


def parse_published_external_index(index_data):
    pages = {
        module.replace(".", "/") + ".html"
        for module in index_data.get("modules", {})
        if module.split(".", 1)[0] not in LOCAL_DOC_ROOTS
    }
    anchors = {page: set() for page in pages}
    declarations = {}
    for name, info in index_data.get("declarations", {}).items():
        doc_link = info.get("docLink", "")
        if not doc_link or doc_link.startswith(LOCAL_DECLARATION_PREFIXES):
            continue
        split = urlsplit(doc_link)
        norm = normalize_doc_relpath(unquote(split.path))
        if norm not in pages:
            continue
        frag = unquote(split.fragment) if split.fragment else ""
        if frag:
            anchors[norm].add(frag)
            declarations.setdefault(name, (norm, frag))
            declarations.setdefault(frag, (norm, frag))
    return {
        "pages": pages,
        "anchors": anchors,
        "declarations": declarations,
    }


def load_external_targets(docs):
    manifest_path = docs.parent / EXTERNAL_TARGETS_FILE
    if manifest_path.is_file():
        raw = json.loads(manifest_path.read_text())
        if raw.get("source") == "published":
            pages = set(raw.get("pages", ()))
            anchors = {rel: set(items) for rel, items in raw.get("anchors", {}).items()}
            declarations = {
                name: tuple(target)
                for name, target in raw.get("declarations", {}).items()
                if isinstance(target, list) and len(target) == 2
            }
            for rel, items in sorted(anchors.items()):
                for item in sorted(items):
                    declarations.setdefault(item, (rel, item))
            return {
                "pages": pages,
                "anchors": anchors,
                "declarations": declarations,
            }
    published_index = fetch_published_external_index()
    if published_index is None:
        return {"pages": set(), "anchors": {}, "declarations": {}}
    return parse_published_external_index(published_index)


def rewrite_external_dependency_links(docs, index, external_pages):
    manifest_path = docs.parent / EXTERNAL_TARGETS_FILE
    has_published_manifest = False
    legacy_local_pages = set()
    legacy_local_anchors = {}
    if manifest_path.is_file():
        raw_manifest = json.loads(manifest_path.read_text())
        if raw_manifest.get("source") == "published":
            has_published_manifest = True
        else:
            legacy_local_pages = set(raw_manifest.get("pages", ()))
            legacy_local_anchors = {
                rel: set(items) for rel, items in raw_manifest.get("anchors", {}).items()
            }

    published_targets = load_external_targets(docs)
    valid_local_pages = set(legacy_local_pages)
    for module in index.get("modules", {}):
        if module.split(".", 1)[0] in LOCAL_DOC_ROOTS:
            continue
        rel = module.replace(".", "/") + ".html"
        if (docs / rel).is_file() or (docs.parent / "doc-data" / f"declaration-data-{module}.bmp").is_file():
            valid_local_pages.add(rel)

    anchor_cache = {}
    local_anchors_by_page = {
        rel: set(legacy_local_anchors.get(rel, ())) for rel in valid_local_pages
    }
    for info in index.get("declarations", {}).values():
        doc_link = info.get("docLink", "")
        if not doc_link or doc_link.startswith(LOCAL_DECLARATION_PREFIXES):
            continue
        split = urlsplit(doc_link)
        norm = normalize_doc_relpath(unquote(split.path))
        if norm in local_anchors_by_page and split.fragment:
            local_anchors_by_page[norm].add(unquote(split.fragment))

    preload_pages = set(valid_local_pages) if len(valid_local_pages) <= 200 else set()
    preload_pages |= (collect_guide_external_pages() & valid_local_pages)
    for rel in sorted(preload_pages):
        if (docs / rel).is_file():
            local_anchors_by_page[rel].update(page_anchors(docs / rel, anchor_cache))

    def recursor_parent_fragment(norm, fragment):
        """Link omitted generated recursors to their indexed inductive/structure parent."""
        if not fragment:
            return fragment
        anchor = unquote(fragment)
        if anchor in local_anchors_by_page.get(norm, ()):
            return fragment
        parent, _, suffix = anchor.rpartition(".")
        info = index.get("declarations", {}).get(parent, {})
        if suffix != "rec" or info.get("kind") not in ("inductive", "structure"):
            return fragment
        parent_link = urlsplit(info.get("docLink", ""))
        if (
            normalize_doc_relpath(unquote(parent_link.path)) == norm
            and unquote(parent_link.fragment) == parent
            and parent in local_anchors_by_page.get(norm, ())
        ):
            return parent_link.fragment
        return fragment

    for page in sorted(docs.rglob("*.html")):
        if not page.is_file():
            continue
        rel_page = page.relative_to(docs).as_posix()
        if rel_page == "navbar.html" or rel_page in external_pages:
            continue
        text = page.read_text()

        def resolve_published_target(norm, query, fragment, display_path):
            anchor = unquote(fragment) if fragment else None
            if fragment:
                if (norm, anchor) in KERNEL_RECURSOR_ANCHORS:
                    require(norm in published_targets["pages"],
                            f"Broken dependency link in {rel_page}: {display_path}")
                    target_norm, target_fragment = norm, fragment
                elif (
                    norm in published_targets["pages"]
                    and anchor in published_targets["anchors"].get(norm, ())
                ):
                    target_norm, target_fragment = norm, fragment
                elif anchor in published_targets["declarations"]:
                    target_norm, target_fragment = published_targets["declarations"][anchor]
                elif norm in published_targets["pages"]:
                    target_norm, target_fragment = norm, None
                else:
                    raise ValueError(f"Broken dependency link in {rel_page}: {display_path}")
            else:
                require(norm in published_targets["pages"],
                        f"Broken dependency link in {rel_page}: {display_path}")
                target_norm, target_fragment = norm, None
            query_suffix = f"?{query}" if query is not None else ""
            frag_suffix = f"#{target_fragment}" if target_fragment else ""
            rewritten = f"{MATHLIB_DOCS_URL}{target_norm}{query_suffix}{frag_suffix}"
            return f'href="{html.escape(rewritten, quote=True)}"'

        def replace_href(match):
            raw_href = match.group(1)
            unescaped = html.unescape(raw_href)
            if unescaped.startswith(MATHLIB_DOCS_URL):
                target = unescaped[len(MATHLIB_DOCS_URL):]
                path_part, query, fragment = split_href_target(target)
                rel_target = unquote(path_part)
                norm = normalize_doc_relpath(rel_target)
                require(norm is not None and is_external_doc_relpath(norm),
                        f"Broken dependency link in {rel_page}: {rel_target}")
                anchor = unquote(fragment) if fragment else None
                already_published = (
                    norm in published_targets["pages"]
                    and (
                        not fragment
                        or anchor in published_targets["anchors"].get(norm, ())
                        or (norm, anchor) in KERNEL_RECURSOR_ANCHORS
                    )
                )
                if not already_published:
                    require(norm in valid_local_pages,
                            f"Broken dependency link in {rel_page}: {rel_target}")
                    if (docs / norm).is_file():
                        local_anchors_by_page[norm].update(page_anchors(docs / norm, anchor_cache))
                    fragment = recursor_parent_fragment(norm, fragment)
                    anchor = unquote(fragment) if fragment else None
                    if fragment and (norm, anchor) not in KERNEL_RECURSOR_ANCHORS:
                        require(anchor in local_anchors_by_page[norm],
                                f"Broken dependency anchor in {rel_page}: {norm}#{anchor}")
                return resolve_published_target(norm, query, fragment, rel_target)

            if unescaped.startswith(API_DOCS_URL):
                target = unescaped[len(API_DOCS_URL):]
                path_part, query, fragment = split_href_target(target)
                rel_target = unquote(path_part)
                norm = normalize_doc_relpath(rel_target)
                if norm is None or not (
                    norm in external_pages
                    or (not is_published_doc_file(docs, norm) and is_external_doc_relpath(norm))
                ):
                    return match.group(0)
            else:
                path_part, query, fragment = split_href_target(unescaped)
                norm = resolve_relative_href(rel_page, path_part)
                if norm is None or not (
                    norm in external_pages
                    or (not is_published_doc_file(docs, norm) and is_external_doc_relpath(norm))
                ):
                    return match.group(0)

            require(norm in valid_local_pages,
                    f"Broken dependency link in {rel_page}: {norm}")
            if (docs / norm).is_file():
                local_anchors_by_page[norm].update(page_anchors(docs / norm, anchor_cache))
            fragment = recursor_parent_fragment(norm, fragment)
            if fragment:
                anchor = unquote(fragment)
                if (norm, anchor) not in KERNEL_RECURSOR_ANCHORS:
                    require(anchor in local_anchors_by_page[norm],
                            f"Broken dependency anchor in {rel_page}: {norm}#{anchor}")
            return resolve_published_target(norm, query, fragment, norm)

        updated = HREF_RE.sub(replace_href, text)
        if updated != text:
            page.write_text(updated)

    if not has_published_manifest:
        manifest_path.write_text(json.dumps({
            "source": "published",
            "pages": sorted(published_targets["pages"]),
            "anchors": {
                rel: sorted(anchors)
                for rel, anchors in sorted(published_targets["anchors"].items())
                if anchors
            },
            "declarations": {
                name: list(target)
                for name, target in sorted(published_targets["declarations"].items())
            },
        }, ensure_ascii=False, separators=(",", ":")))


def remove_empty_parents(path, stop):
    parent = path.parent
    while parent != stop and parent.exists():
        try:
            parent.rmdir()
        except OSError:
            break
        parent = parent.parent


def trim_navbar(navbar_path, pruned_pages):
    if not navbar_path.is_file() or not pruned_pages:
        return
    text = navbar_path.read_text()
    text = NAV_LINK_RE.sub(
        lambda m: "" if (m.group(1) or m.group(2)) in pruned_pages else m.group(0),
        text,
    )
    while EMPTY_NAV_SECT_RE.search(text):
        text = EMPTY_NAV_SECT_RE.sub("", text)
    navbar_path.write_text(text)


def sanitize_dependency_code_links(docs, modules=(), pruned_pages=()):
    if not docs.is_dir():
        return
    page_to_module = {module.replace(".", "/") + ".html": module for module in modules}
    for page in sorted(docs.rglob("*.html")):
        if not page.is_file():
            continue
        rel_page = page.relative_to(docs).as_posix()
        if (
            rel_page in ("Complexity.html", "navbar.html")
            or rel_page.startswith("Complexity/")
            or rel_page in pruned_pages
        ):
            continue
        text = page.read_text()
        if (
            ".lean" not in text
            and "><code>" not in text
            and "lean-manual://" not in text
            and "/fderiv.html" not in text
        ):
            continue

        def replace_link(match):
            href = match.group(1) or match.group(3) or match.group(5)
            label = (
                f"<code>{match.group(2)}</code>"
                if match.group(2) is not None
                else (match.group(4) or match.group(6))
            )
            norm = resolve_relative_href(rel_page, href)
            if norm and norm not in page_to_module and not is_published_doc_file(docs, norm):
                return label
            return match.group(0)

        updated = DEP_BROKEN_LINK_RE.sub(replace_link, text)
        if updated != text:
            page.write_text(updated)


def trim_output():
    docs = ROOT / "docbuild/.lake/build/doc"
    index_path = docs / "declarations/declaration-data.bmp"
    require(index_path.is_file(), "Missing documentation output: declarations/declaration-data.bmp")
    index = json.loads(index_path.read_text())
    modules = index["modules"]
    kept_modules = {
        module for module in modules
        if module.split(".", 1)[0] in LOCAL_DOC_ROOTS
    }
    pruned_modules = set(modules) - kept_modules
    pruned_pages = {module.replace(".", "/") + ".html" for module in pruned_modules}

    sanitize_dependency_code_links(docs, modules, pruned_pages)
    rewrite_external_dependency_links(docs, index, pruned_pages)

    for rel_page in sorted(pruned_pages):
        page = docs / rel_page
        if page.is_file():
            page.unlink()
            remove_empty_parents(page, docs)

    trim_navbar(docs / "navbar.html", pruned_pages)

    kept_declarations = {
        name: info for name, info in index.get("declarations", {}).items()
        if info.get("docLink", "").startswith(LOCAL_DECLARATION_PREFIXES)
    }
    kept_instances = {
        name: [inst for inst in items if inst in kept_declarations]
        for name, items in index.get("instances", {}).items()
    }
    kept_instances = {name: items for name, items in kept_instances.items() if items}
    kept_instances_for = {
        name: [inst for inst in items if inst in kept_declarations]
        for name, items in index.get("instancesFor", {}).items()
    }
    kept_instances_for = {name: items for name, items in kept_instances_for.items() if items}
    kept_modules_dict = {
        module: {
            **info,
            **({"importedBy": [imp for imp in info["importedBy"] if imp in kept_modules]}
               if "importedBy" in info else {}),
        }
        for module, info in modules.items()
        if module in kept_modules
    }
    trimmed_index = {
        **index,
        "declarations": kept_declarations,
        "modules": kept_modules_dict,
    }
    if "instances" in index:
        trimmed_index["instances"] = kept_instances
    if "instancesFor" in index:
        trimmed_index["instancesFor"] = kept_instances_for
    index_path.write_text(json.dumps(trimmed_index, ensure_ascii=False, separators=(",", ":")))


def verify_external_doc_target(raw_target, external_targets, *,
                               context_page=None, is_guide=False):
    path_part, _, fragment = split_href_target(raw_target)
    rel_path = unquote(path_part)
    norm = normalize_doc_relpath(rel_path)
    if not norm or not is_external_doc_relpath(norm) or norm not in external_targets["pages"]:
        if is_guide:
            raise ValueError(f"Guide links to a missing documentation page: {path_part}")
        raise ValueError(f"Broken external dependency link in {context_page}: {rel_path}")
    if fragment:
        anchor = unquote(fragment)
        if (norm, anchor) in KERNEL_RECURSOR_ANCHORS:
            return
        if anchor not in external_targets["anchors"].get(norm, ()):
            if is_guide:
                raise ValueError(f"Guide links to a missing documentation anchor: {raw_target}")
            raise ValueError(
                f"Broken external dependency anchor in {context_page}: {norm}#{anchor}"
            )


def check_internal_links(docs):
    pages = sorted(page for page in docs.rglob("*.html") if page.is_file())
    checked_targets = {}
    external_targets = load_external_targets(docs)
    for page in pages:
        rel_page = page.relative_to(docs).as_posix()
        text = page.read_text()
        for raw in HREF_RE.findall(text):
            unescaped = html.unescape(raw)
            if unescaped.startswith(MATHLIB_DOCS_URL):
                verify_external_doc_target(
                    unescaped[len(MATHLIB_DOCS_URL):],
                    external_targets, context_page=rel_page,
                )
                continue
            if unescaped.startswith(API_DOCS_URL):
                path_part, _, _ = split_href_target(unescaped[len(API_DOCS_URL):])
                rel_target = unquote(path_part) or "index.html"
                norm = normalize_doc_relpath(rel_target)
            else:
                norm = resolve_relative_href(rel_page, unescaped)
                if norm is None:
                    continue
                rel_target = norm
            if norm is None:
                raise ValueError(f"Broken internal link in {rel_page}: {rel_target}")
            exists = checked_targets.get(norm)
            if exists is None:
                exists = is_published_doc_file(docs, norm)
                checked_targets[norm] = exists
            require(exists, f"Broken internal link in {rel_page}: {norm}")


def check_module_inventory(names, expected, label):
    actual = local_modules(names)
    obsolete = sorted(actual - expected)
    missing = sorted(expected - actual)
    require(not obsolete, f"Obsolete modules in {label}: {', '.join(obsolete)}")
    require(not missing, f"Missing modules in {label}: {', '.join(missing)}")


def check_intermediate_modules(build, expected):
    # Pinned doc-gen4's htmlOutputIndex/headerDataOutput merge these files on
    # incremental builds, even when the assembled index currently looks clean.
    prefix = "declaration-data-"
    names = (path.name[len(prefix):-len(".bmp")]
             for path in (build / "doc-data").glob(f"{prefix}*.bmp") if path.is_file())
    check_module_inventory(names, expected, "per-module declaration data")
    # DocGen4/DB/Schema.lean defines modules(name PRIMARY KEY, source_url).
    # Even mode=ro can create WAL/SHM files. Inspect a private snapshot of completed
    # output, including committed WAL rows; immutable=1 on the main file loses those.
    database = build / "api-docs.db"
    require(database.is_file(), "Missing documentation database: api-docs.db")
    with tempfile.TemporaryDirectory(prefix="check-docs-") as temporary:
        snapshot = Path(temporary) / database.name
        shutil.copyfile(database, snapshot)
        wal = database.with_name(database.name + "-wal")
        if wal.is_file():
            shutil.copyfile(wal, snapshot.with_name(snapshot.name + "-wal"))
        with closing(sqlite3.connect(snapshot.as_uri() + "?mode=ro", uri=True)) as db:
            names = (row[0] for row in db.execute("SELECT name FROM modules"))
            check_module_inventory(names, expected, "documentation database")


def check_output():
    docs = ROOT / "docbuild/.lake/build/doc"
    for name in ("index.html", "search.html", "search.js", "declaration-data.js",
                 "references.html", "references.bib", "find/index.html"):
        require((docs / name).is_file(), f"Missing documentation output: {name}")
    # doc-gen4 uses a .bmp extension for its JSON search index.
    index = json.loads((docs / "declarations/declaration-data.bmp").read_text())
    sources = [ROOT / "Complexity.lean", *sorted((ROOT / "Complexity").rglob("*.lean"))]
    expected_modules = {
        ".".join(source.relative_to(ROOT).with_suffix("").parts) for source in sources
    }
    # Reused doc-gen4 caches can retain removed modules. Dependency docs are allowed.
    stale_modules = sorted(local_modules(index["modules"]) - expected_modules)
    require(not stale_modules,
            f"Obsolete modules in search index: {', '.join(stale_modules)}")
    local_pages = {
        ".".join(page.relative_to(docs).with_suffix("").parts)
        for page in (docs / "Complexity").rglob("*.html") if page.is_file()
    }
    stale_pages = sorted(local_pages - expected_modules)
    require(not stale_pages, f"Obsolete module pages: {', '.join(stale_pages)}")
    for source in sources:
        module = ".".join(source.relative_to(ROOT).with_suffix("").parts)
        require(module in index["modules"], f"Missing module in search index: {module}")
        page = docs / source.relative_to(ROOT).with_suffix(".html")
        require(page.is_file(), f"Missing module page: {module}")
    check_intermediate_modules(docs.parent, expected_modules)
    for name in ("Cslib.Complexity.CookLevin.SAT_npComplete",
                 "Cslib.Complexity.NP_eq_PCP_log",
                 "Cslib.Crypto.OneWay.exists_pseudorandomFunction"):
        require(name in index["declarations"], f"Missing theorem in search index: {name}")
        link = urlsplit(index["declarations"][name]["docLink"])
        page = docs / unquote(link.path)
        anchor = html.escape(unquote(link.fragment), quote=True)
        require(f'id="{anchor}"' in page.read_text(), f"Missing theorem anchor: {name}")
    check_internal_links(docs)
    print(f"Documentation covers {len(sources)} modules and representative theorem search entries.")


def expected_abstract_paths():
    catalogue_path = ROOT / "abstracts/catalogue.json"
    if not catalogue_path.is_file():
        return {"abstracts/catalogue.pdf"}
    catalogue = json.loads(catalogue_path.read_text())
    return {"abstracts/catalogue.pdf"} | {
        f"abstracts/{entry['id']}.pdf" for entry in catalogue.get("entries", [])
    }


def check_guide_links():
    docs = ROOT / "docbuild/.lake/build/doc"
    pages = sorted((ROOT / "guide/.lake/build/site/html-multi").rglob("*.html"))
    require(pages, "Missing guide output")
    local_link_re = re.compile(r'href="' + re.escape(API_DOCS_URL) + r'([^"]*)"')
    external_link_re = re.compile(r'href="' + re.escape(MATHLIB_DOCS_URL) + r'([^"]*)"')
    anchors = {}
    local_links = set()
    external_links = set()
    for page in pages:
        text = page.read_text()
        local_links.update(html.unescape(target) for target in local_link_re.findall(text))
        external_links.update(html.unescape(target) for target in external_link_re.findall(text))
    abstract_paths = expected_abstract_paths()
    abstracts_staged = (docs / "abstracts").is_dir()
    for target in sorted(local_links):
        path, _, fragment = split_href_target(target)
        rel_path = unquote(path) or "index.html"
        if rel_path.startswith("abstracts/"):
            require(rel_path in abstract_paths,
                    f"Guide links to an unknown formal abstract: {path}")
            require(not fragment,
                    f"Guide links to a formal abstract with an unexpected anchor: {target}")
            if abstracts_staged:
                require((docs / rel_path).is_file(),
                        f"Guide links to a missing documentation page: {path}")
            continue
        file = docs / rel_path
        require(file.is_file(), f"Guide links to a missing documentation page: {path}")
        if fragment:
            if file not in anchors:
                ids = re.findall(r'id="([^"]*)"', file.read_text())
                anchors[file] = {html.unescape(i) for i in ids}
            require(unquote(fragment) in anchors[file],
                    f"Guide links to a missing documentation anchor: {target}")
    external_targets = load_external_targets(docs)
    for target in sorted(external_links):
        verify_external_doc_target(
            target, external_targets, is_guide=True,
        )
    total_links = len(local_links) + len(external_links)
    print(f"The guide's {total_links} links into the documentation resolve.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config-only", action="store_true",
                        help="check pins before invoking Lake; do not require built documentation")
    parser.add_argument("--trim", action="store_true",
                        help="externalize dependency pages and trim declaration data before checking")
    parser.add_argument("--guide", action="store_true",
                        help="also check the built guide's links into the built documentation")
    args = parser.parse_args()
    try:
        check_config()
        if args.config_only:
            print("Documentation configuration is consistent.")
        else:
            if args.trim:
                trim_output()
            check_output()
            if args.guide:
                check_guide_links()
    except (OSError, ValueError, KeyError, StopIteration, sqlite3.Error) as error:
        parser.exit(1, f"Documentation check failed: {error}\n")


if __name__ == "__main__":
    main()
