#!/usr/bin/env python3
"""Build individual Lean formal-abstract PDFs and their curated catalogue (Python 3.11+)."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from urllib.parse import quote
import xml.etree.ElementTree as ET
import zlib

import abstract_to_tex as render
from proof_lengths import command_starts, signature_end


ROOT = Path(__file__).resolve().parents[1]
STYLE_SOURCE = (
    "https://github.com/edemaine/translation-tiling-paper/blob/"
    "5309313e662377d2efb353acba454859469606bd/paper.texlish"
)
EXTRACTION_SOURCE = (
    "https://github.com/edemaine/translation-tiling-paper/blob/"
    "5309313e662377d2efb353acba454859469606bd/figures/extract_lean_snippets.py"
)
KEYWORDS = {"abbrev", "def", "theorem", "lemma", "inductive", "structure", "where", "fun",
            "noncomputable", "private", "if", "then", "else", "match", "with"}
TYPES = {"Prop", "Type", "Set", "List", "Fin", "Nat", "Bool", "Polynomial", "Finset", "Option"}
TOKEN_RE = re.compile(r"\b(?:" + "|".join(sorted(KEYWORDS | TYPES)) + r")\b")

# Typography, code-box treatment and syntax colors adapted from Erik Demaine and Stefan Langerman's
# translation-tiling-paper, paper.texlish:25-78 at the exact revision linked above.
# This uses no logo or copied mathematical exposition.
PREAMBLE = r"""\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage{amsmath,amssymb}
\usepackage{libertine}
\usepackage[libertine]{newtxmath}
\usepackage[scaled=0.96]{zi4}
\usepackage[margin=0.9in,bottom=1.1in,footskip=44pt]{geometry}
\usepackage{microtype,enumitem,xcolor,tcolorbox,xurl,hyperref,fancyhdr}
\tcbuselibrary{breakable,skins}
\definecolor{leanblue}{RGB}{41,110,166}
\definecolor{leangreen}{RGB}{38,128,89}
\hypersetup{colorlinks=true,urlcolor=leanblue,linkcolor=leanblue}
\tcbset{leandeclarationmeasure/.style={}}
\newtcolorbox{leanbox}{breakable,enhanced,colback=black!3,colframe=black!45,
  boxrule=0.5pt,arc=2pt,left=7pt,right=7pt,top=5pt,bottom=5pt,
  before skip=7pt,after skip=9pt,leandeclarationmeasure}
% Measure a declaration's prose and code at their actual display width. Bottom-align the
% minipage so TeX's page builder counts its full height against \pagegoal instead of letting
% half the box hang into the footer as depth. Keep the pair together below 35% of the text
% height; larger declarations retain breakable boxes.
% environ is already required by tcolorbox. These bodies contain display text, not counters.
\newsavebox{\leandeclarationbox}
\NewEnviron{leandeclaration}{%
  \par
  \sbox{\leandeclarationbox}{%
    \begin{minipage}[b]{\linewidth}
    \setlength{\parskip}{0.45em}
    \tcbset{leandeclarationmeasure/.style={unbreakable}}%
    \BODY
    \end{minipage}}%
  \ifdim\dimexpr\ht\leandeclarationbox+\dp\leandeclarationbox\relax<0.35\textheight
    \par\addvspace{5pt}\noindent\usebox{\leandeclarationbox}\par\addvspace{6pt}
  \else
    \ifdim\pagetotal>0.80\textheight
      \newpage
    \fi
    {\interlinepenalty=10000\BODY\par}%
  \fi}
\setlength{\parindent}{0pt}
\setlength{\parskip}{0.45em}
\setlength{\emergencystretch}{2em}
\widowpenalty=10000
\clubpenalty=10000
\setlist[itemize]{leftmargin=1.4em,itemsep=2pt,topsep=3pt}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small\textsc{Complexitylib / Formal abstracts}}
\renewcommand{\headrulewidth}{0.3pt}
\setlength{\headheight}{14pt}
\begin{document}
"""


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def git(root, *args):
    return subprocess.check_output(["git", *args], cwd=root, text=True).strip()


def module_source_path(module, root=ROOT):
    return render.module_source_path(module, root)


def _lean_code(text):
    return render.lean_code(text)


def _namespace_contexts(text):
    """Track namespace commands (and section scopes) in the abstract's source code."""
    declared, contexts, stack, namespace = set(), {}, [], ""
    for number, line in enumerate(_lean_code(text).splitlines(), 1):
        contexts[number] = namespace
        opening = re.fullmatch(r"\s*namespace\s+([A-Za-z_][A-Za-z0-9_.]*)\s*", line)
        if opening:
            stack.append(namespace)
            namespace = ".".join(filter(None, (namespace, opening.group(1))))
            declared.add(namespace)
        elif re.fullmatch(r"\s*(?:noncomputable\s+)?section(?:\s+\w+)?\s*", line):
            stack.append(namespace)
        elif re.fullmatch(r"\s*end(?:\s+[A-Za-z_][A-Za-z0-9_.]*)?\s*", line):
            if stack:
                namespace = stack.pop()
    return declared, contexts


def declaration_line(text, name):
    """Locate the named source declaration; headline names may be qualified."""
    short = name.rsplit(".", 1)[-1]
    pattern = re.compile(r"^\s*(?:(?:private|noncomputable)\s+)?"
                         r"(?:theorem|lemma|def|abbrev|inductive|structure)\s+"
                         + re.escape(short) + r"(?=[\s:{(])")
    matches = [i for i, line in enumerate(_lean_code(text).splitlines(), 1) if pattern.search(line)]
    if len(matches) != 1:
        raise ValueError(f"Expected exactly one declaration named {name}, found {len(matches)}")
    return matches[0]


def selected_statement(text, name):
    """The named theorem's source statement through its type: everything before its proof.

    It is read from the whole source file by declaration line and command boundary, separately
    from the docstring sections that the display is rendered from.
    """
    start = 0
    for _ in range(declaration_line(text, name) - 1):
        start = text.index("\n", start) + 1
    start += len(text[start:]) - len(text[start:].lstrip(" \t"))
    syntax = _lean_code(text)
    end = next((command for command in command_starts(syntax) if command > start), len(text))
    try:
        return text[start:start + signature_end(syntax[start:end])[0]].rstrip()
    except ValueError as error:
        raise ValueError(f"{name}: {error}") from error


def check_selected_statements(text, sections, names):
    """Require every selected statement to be displayed in full in the main presentation.

    The comparison ignores whitespace, so it is independent of layout but not of content.
    """
    selected, displayed = {name.rsplit(".", 1)[-1] for name in names}, {}
    for item in render.split_sections(sections)[0]:
        displayed.update(displayed_code(item, selected)[1])
    if missing := sorted(selected - displayed.keys()):
        raise ValueError(f"Selected statements must be in the main presentation: {missing}")
    for name in names:
        shown = render.declaration_body(displayed[name.rsplit(".", 1)[-1]])
        if shown.split() != selected_statement(text, name).split():
            raise ValueError(f"Selected statement is not displayed in full: {name}")


def entry_foundations(entry, root=ROOT):
    """Require the manifest to name exactly the source's imported foundation closure."""
    listed = entry.get("foundations", [])
    if not isinstance(listed, list) or any(not isinstance(module, str) for module in listed):
        raise ValueError(f"Foundations must be a list of module names in {entry['id']}")
    if len(listed) != len(set(listed)):
        raise ValueError(f"Duplicate foundation in {entry['id']}")
    for module in listed:
        path = module_source_path(module, root)
        if module == "CslibFrontierAbstracts.Check" or module.endswith(("Abstract", "Bridge")):
            raise ValueError(f"Not a shared foundation: {module}")
        if not path.is_file():
            raise ValueError(f"Missing shared foundation source: {module}")
        render.split_sections(render.parse_abstract(path.read_text())[2])
    expected = render.foundation_modules(module_source_path(entry["module"], root), root)
    missing, unused = set(expected) - set(listed), set(listed) - set(expected)
    if missing or unused:
        raise ValueError(f"Foundation manifest mismatch in {entry['id']}: "
                         f"missing {sorted(missing)}, unused {sorted(unused)}")
    return expected


def load_catalogue(manifest, root=ROOT):
    data = json.loads(Path(manifest).read_text())
    if not isinstance(data, dict) or not isinstance(data.get("title"), str) or not data["title"].strip():
        raise ValueError("Catalogue needs a title and an entries list")
    entries = data.get("entries")
    if not isinstance(entries, list) or not entries:
        raise ValueError("Catalogue must contain a nonempty entries list")
    seen_ids, seen_headlines = set(), set()
    for entry in entries:
        if not isinstance(entry, dict):
            raise ValueError("Each catalogue entry must be an object")
        for field in ("id", "title", "module", "summary", "scope"):
            if not isinstance(entry.get(field), str) or not entry[field].strip():
                raise ValueError(f"Catalogue entry needs nonempty {field}")
        entry_id = entry["id"]
        if (not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", entry_id)
                or entry_id in seen_ids or entry_id == "catalogue"):
            raise ValueError(f"Invalid or duplicate catalogue id: {entry_id}")
        seen_ids.add(entry_id)
        module = entry["module"]
        source = module_source_path(module, root)
        if not module.endswith("Abstract"):
            raise ValueError(f"Not a formal-abstract module: {module}")
        namespace = entry.get("namespace", module)
        if not isinstance(namespace, str) or not re.fullmatch(
                r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", namespace):
            raise ValueError(f"Invalid abstract namespace: {namespace}")
        text = source.read_text()
        declared, contexts = _namespace_contexts(text)
        if namespace not in declared:
            raise ValueError(f"Abstract namespace {namespace} is not declared in {source}")
        headlines = entry.get("headline_theorems")
        if not isinstance(headlines, list) or not headlines:
            raise ValueError(f"No selected headline theorems in {entry_id}")
        supporting = entry.get("supporting_theorems", [])
        if not isinstance(supporting, list):
            raise ValueError(f"Supporting theorems must be a list in {entry_id}")
        for name in [*headlines, *supporting]:
            if not isinstance(name, str) or not re.fullmatch(
                    re.escape(namespace) + r"\.[A-Za-z_][A-Za-z0-9_']*", name):
                raise ValueError(f"Headline must be qualified within {namespace}: {name}")
            if name in seen_headlines:
                raise ValueError(f"Duplicate selected headline: {name}")
            seen_headlines.add(name)
            line = declaration_line(text, name)
            if contexts[line] != namespace:
                raise ValueError(f"Headline is outside namespace {namespace}: {name}")
            if not re.match(r"\s*(?:theorem|lemma)\s", text.splitlines()[line - 1]):
                raise ValueError(f"Selected headline is not a theorem: {name}")
        check_selected_statements(text, render.parse_abstract(text)[2], [*headlines, *supporting])
        entry_foundations(entry, root)
    return entries


def source_url(repository, sha, relative_path, line=None):
    url = f"https://github.com/{repository}/blob/{sha}/{quote(str(relative_path))}"
    return url + (f"#L{line}" if line else "")


def link(url, label):
    # detokenize preserves source paths/anchors without treating underscores as TeX commands.
    return r"\href{\detokenize{" + url + "}}{" + label + "}"


def highlighted_line(line):
    pieces, start = [], 0
    for token in TOKEN_RE.finditer(line):
        pieces.append(render.escape_tex_code_line(line[start:token.start()]))
        word = token.group()
        color = "leanblue" if word in KEYWORDS else "leangreen"
        escaped = render.escape_tex_code_line(word)
        if word in KEYWORDS:
            escaped = r"\textbf{" + escaped + "}"
        pieces.append(r"\textcolor{" + color + "}{" + escaped + "}")
        start = token.end()
    pieces.append(render.escape_tex_code_line(line[start:]))
    return "".join(pieces)


def displayed_code(item, selected=None):
    """An item's displayed code, and its displayed theorem signatures by name."""
    kept, displayed = [], {}
    for block in render.display_blocks(item["code"], is_undocumented_tail=item["kind"] == "section"):
        theorem = render.theorem_name(block)
        if not theorem or selected is None or theorem in selected:
            kept.append(block)
            if theorem:
                displayed[theorem] = block
    return "\n\n".join(kept), displayed


def render_sections(sections, selected=None):
    """Display all definitions, and either all theorem signatures or an explicit selection."""
    lines, displayed = [], {}
    for item in sections:
        code, shown = displayed_code(item, selected)
        displayed.update(shown)
        if item["kind"] == "decl" and item["code"].strip() and not code:
            continue
        heading = render.section_heading(item)
        prose_source = heading.group(2) if heading else item["doc"]
        paragraphs = render.render_tex_paragraphs(prose_source)
        if heading:
            lines.append(r"\subsection*{" + render.escape_tex_prose(heading.group(1).strip()) + "}")
        if code:
            code_lines = [highlighted_line(line) or "~" for line in code.splitlines()]
            box = [r"\begin{leanbox}\small\ttfamily\raggedright\noindent",
                   " \\\\\n".join(code_lines), r"\par\end{leanbox}"]
            if paragraphs:
                lines.extend(paragraphs[:-1])
                lines.extend([r"\begin{leandeclaration}", paragraphs[-1], *box,
                              r"\end{leandeclaration}"])
            else:
                lines.extend(box)
        else:
            lines.extend(paragraphs)
    return "\n\n".join(lines), displayed


def foundation_record(module, repository, sha, root=ROOT):
    source = module_source_path(module, root)
    text = source.read_text()
    declared, contexts = _namespace_contexts(text)
    relative = source.relative_to(root)
    declarations = []
    for number, line in enumerate(_lean_code(text).splitlines(), 1):
        match = re.match(r"\s*(?:(?:private|noncomputable)\s+)?"
                         r"(?:def|abbrev|theorem|lemma|inductive|structure)\s+([\w'.]+)", line)
        if match:
            name = ".".join(filter(None, (contexts[number], match.group(1))))
            declarations.append({"declaration": name, "line": number,
                                 "url": source_url(repository, sha, relative, number)})
    return {"module": module, "source": str(relative), "source_sha256": digest(source),
            "url": source_url(repository, sha, relative), "namespaces": sorted(declared),
            "declarations": declarations}


def render_foundations(modules, repository, sha, root=ROOT):
    if not modules:
        return ""
    lines = [r"\section*{Appendix: shared foundations}",
             "These checked definitions specify the representations and machine bounds used "
             "above. They are displayed once here; their Lean sources remain part of the "
             "document's provenance."]
    for module in dict.fromkeys(modules):
        source = module_source_path(module, root)
        title, intro, sections = render.parse_abstract(source.read_text())
        record = foundation_record(module, repository, sha, root)
        lines.extend([r"\subsection*{" + render.escape_tex_prose(title) + "}",
                      r"{\small " + link(record["url"], "Lean source") + ". Namespaces: " +
                      ", ".join(render.escape_tex_prose("`" + ns + "`")
                                for ns in record["namespaces"]) + ".}"])
        if record["declarations"]:
            lines.append(r"{\small Declarations: " + ", ".join(
                link(item["url"], render.escape_tex_prose(
                    "`" + item["declaration"].rsplit(".", 1)[-1] + "`"))
                for item in record["declarations"]) + ".}")
        lines.extend([*render.render_tex_intro(intro),
                      render_sections(render.presentation_sections(sections))[0]])
    return "\n\n".join(lines) + "\n"


def render_entry(entry, repository, sha, dirty, root=ROOT, *, include_foundations=True):
    source = module_source_path(entry["module"], root)
    text = source.read_text()
    _, intro, sections = render.parse_abstract(text)
    relative = source.relative_to(root)
    title = render.escape_tex_prose(entry["title"])
    url = source_url(repository, sha, relative)
    state = "Working tree based on" if dirty else "Source revision"
    lines = [r"\hypertarget{" + entry["id"] + "}{}", r"\section*{" + title + "}",
             r"{\small\color{black!65} " + state + " " +
             link(f"https://github.com/{repository}/commit/{sha}", r"\texttt{" + sha[:12] + "}") +
             " / " + link(url, "Lean source") + "}"]
    displayed_names = [*entry["headline_theorems"], *entry.get("supporting_theorems", [])]
    lines.append(r"{\small Statements: " + ", ".join(
        link(source_url(repository, sha, relative, declaration_line(text, name)),
             render.escape_tex_prose("`" + name.rsplit(".", 1)[-1] + "`"))
        for name in displayed_names) + "}")
    if dirty:
        lines.append(r"{\small\emph{Local source edits are identified by digests in provenance.json; "
                     "the links show the base revision.}}")
    lines.extend([r"\begin{quote}\small " + render.escape_tex_prose(entry["summary"]) +
                  r"\par\emph{Scope.} " + render.escape_tex_prose(entry["scope"]) +
                  r"\end{quote}", "", *render.render_tex_intro(intro), ""])
    check_selected_statements(text, sections, displayed_names)
    selected = {name.rsplit(".", 1)[-1] for name in displayed_names}
    lines.append(render_sections(render.presentation_sections(sections), selected)[0])
    modules = entry_foundations(entry, root)
    if modules:
        lines.insert(-1, r"{\small Shared foundation definitions appear in the appendix: " +
                     ", ".join(link(source_url(repository, sha,
                                                module_source_path(module, root).relative_to(root)),
                                    render.escape_tex_prose("`" + module + "`"))
                               for module in modules) + ".}")
    if include_foundations:
        lines.append(render_foundations(modules, repository, sha, root))
    return "\n\n".join(lines) + "\n"


def style_credit():
    return (r"\fancyfoot[C]{\parbox[b]{\textwidth}{\centering\fontsize{8}{9.5}\selectfont"
            r"\color{black!60} Theorem and helper proofs are omitted. "
            "Proof-field underscores mark omitted checked terms. Linked sources contain complete "
            "definitions and proofs. Layout adapted from Erik Demaine and Stefan Langerman's " +
            link(STYLE_SOURCE, "paper style") + "; extraction follows their " +
            link(EXTRACTION_SOURCE, "Lean snippet workflow") + r".\par\thepage}}" + "\n")


def document(body):
    return PREAMBLE + style_credit() + body + "\n\\end{document}\n"


def page_drawn_bounds(pdf_path, page_heights):
    """Extract bounding boxes of drawn vector paths (such as code-box borders) per page."""
    pdf_bytes = Path(pdf_path).read_bytes()
    streams = []
    for match in re.finditer(rb"<<([^>]*?)>>\s*stream(?:\r\n|\n)", pdf_bytes):
        header = match.group(1)
        if b"/Length1" in header or b"/Subtype" in header or b"/Type" in header:
            continue
        length = re.search(rb"/Length\s+(\d+)", header)
        if not length:
            continue
        raw = pdf_bytes[match.end():match.end() + int(length.group(1))]
        data = zlib.decompress(raw).decode("latin1")
        if "BT" in data and "ET" in data:
            streams.append(data)
    if len(streams) != len(page_heights):
        raise ValueError(f"Expected {len(page_heights)} page streams in {Path(pdf_path).name}, "
                         f"found {len(streams)}")
    pages = []
    for data, page_height in zip(streams, page_heights):
        stack, tx, ty, pts, boxes = [(0.0, 0.0)], 0.0, 0.0, [], []
        for line in data.splitlines():
            s = line.strip()
            if s == "q":
                stack.append((tx, ty))
            elif s == "Q":
                tx, ty = stack.pop()
            elif s.endswith(" cm"):
                parts = [float(x) for x in s[:-3].split()]
                if len(parts) == 6:
                    tx += parts[4]
                    ty += parts[5]
            elif s.endswith((" m", " l")):
                vals = [float(v) for v in s[:-2].split()]
                if len(vals) == 2:
                    pts.append((tx + vals[0], page_height - (ty + vals[1])))
            elif s.endswith(" c"):
                vals = [float(v) for v in s[:-2].split()]
                if len(vals) == 6:
                    for i in range(0, 6, 2):
                        pts.append((tx + vals[i], page_height - (ty + vals[i + 1])))
            elif s in ("f", "S", "B", "f*", "B*"):
                if pts:
                    xs, ys = [p[0] for p in pts], [p[1] for p in pts]
                    boxes.append((min(xs), min(ys), max(xs), max(ys)))
                    pts = []
            elif s == "n":
                pts = []
        pages.append(boxes)
    return pages


def build_pdf(tex_path):
    command = ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
               "-no-shell-escape", tex_path.name]
    result = subprocess.run(command, cwd=tex_path.parent, capture_output=True, text=True,
                            errors="replace")
    if result.returncode:
        raise ValueError(f"PDF build failed for {tex_path.name}:\n{result.stdout[-5000:]}\n"
                         f"{result.stderr[-1000:]}")
    pdf = tex_path.with_suffix(".pdf")
    if not shutil.which("pdftotext"):
        raise ValueError("Poppler's pdftotext is required to check PDF text margins")
    bounds = tex_path.with_suffix(".bbox.html")
    subprocess.run(["pdftotext", "-bbox", str(pdf), str(bounds)], check=True,
                   capture_output=True, text=True)
    pages = ET.parse(bounds).getroot().findall(".//{*}page")
    if not pages:
        raise ValueError(f"No rendered pages in {pdf.name}")
    heights = [float(page.attrib["height"]) for page in pages]
    drawn_pages = page_drawn_bounds(pdf, heights)
    for number, (page, boxes) in enumerate(zip(pages, drawn_pages), 1):
        width, height = float(page.attrib["width"]), float(page.attrib["height"])
        words = page.findall(".//{*}word")
        footer_indices = [
            index for index, word in enumerate(words)
            if word.text == "Theorem" and index + 1 < len(words)
            and words[index + 1].text == "and" and float(word.attrib["yMin"]) > height - 80
        ]
        footer_top = float(words[footer_indices[0]].attrib["yMin"]) if footer_indices else None
        footer_words = set(words[footer_indices[0]:footer_indices[0] + 36]) if footer_indices else set()
        for word in words:
            x_min, x_max = float(word.attrib["xMin"]), float(word.attrib["xMax"])
            y_min, y_max = float(word.attrib["yMin"]), float(word.attrib["yMax"])
            if x_min < 24 or x_max > width - 24 or y_min < 18 or y_max > height - 18:
                raise ValueError(f"Text clips page margins in {pdf.name}, page {number}: {word.text!r}")
            if footer_top is not None and word not in footer_words and footer_top - y_max < 12:
                raise ValueError(
                    f"Body text encroaches on provenance footer in {pdf.name}, page {number}: "
                    f"{word.text!r} (yMax={y_max:.2f}, footer={footer_top:.2f})")
        for x_min, y_min, x_max, y_max in boxes:
            if x_min < 24 or x_max > width - 24 or y_min < 18 or y_max > height - 18:
                raise ValueError(f"Code box clips page margins in {pdf.name}, page {number}")
            if footer_top is not None and footer_top - y_max < 12:
                raise ValueError(
                    f"Code box encroaches on provenance footer in {pdf.name}, page {number} "
                    f"(yMax={y_max:.2f}, footer={footer_top:.2f})")
    return pdf


def build(manifest, output, *, root=ROOT, require_clean=False):
    root = Path(root).resolve()
    manifest, output = Path(manifest).resolve(), Path(output).resolve()
    entries = load_catalogue(manifest, root)
    sha = git(root, "rev-parse", "HEAD")
    dirty = bool(git(root, "status", "--porcelain"))
    if require_clean and dirty:
        raise ValueError("A clean source checkout is required for publication")
    if not shutil.which("latexmk"):
        raise ValueError("latexmk is required (see abstracts/README.md for TeX dependencies)")
    inputs = {Path(manifest), *(root / "scripts" / name for name in
                                ("build_abstracts.py", "abstract_to_tex.py", "proof_lengths.py"))}
    all_foundations = []
    for entry in entries:
        source = module_source_path(entry["module"], root)
        inputs.add(source)
        modules = entry_foundations(entry, root)
        all_foundations.extend(modules)
        inputs.update(module_source_path(module, root) for module in modules)
        bridge = source.with_name(source.name.replace("Abstract.lean", "Bridge.lean"))
        if bridge.is_file():
            inputs.add(bridge)
    input_records = [{"path": str(path.relative_to(root)), "sha256": digest(path)}
                     for path in sorted(inputs)]
    repository = os.environ.get("GITHUB_REPOSITORY", "cslib-community/complexitylib")
    output.mkdir(parents=True, exist_ok=True)
    (output / "provenance.json").unlink(missing_ok=True)
    # Rebuild the explicit selection without retaining retired release PDFs in a reused directory.
    for stale in output.glob("*.pdf"):
        if stale.stem not in {entry["id"] for entry in entries} | {"catalogue"}:
            stale.unlink()
    bodies, documents = [], []
    for entry in entries:
        body = render_entry(entry, repository, sha, dirty, root, include_foundations=False)
        bodies.append(body)
        tex = output / (entry["id"] + ".tex")
        modules = entry_foundations(entry, root)
        tex.write_text(document(body + render_foundations(modules, repository, sha, root)))
        pdf = build_pdf(tex)
        source = module_source_path(entry["module"], root)
        text = source.read_text()
        documents.append({
            "id": entry["id"], "title": entry["title"], "pdf": pdf.name,
            "pdf_sha256": digest(pdf), "source": str(source.relative_to(root)),
            "source_sha256": digest(source),
            "foundations": [foundation_record(module, repository, sha, root) for module in modules],
            "headlines": [
                {"declaration": name, "line": declaration_line(text, name),
                 "url": source_url(repository, sha, source.relative_to(root),
                                   declaration_line(text, name))}
                for name in entry["headline_theorems"]],
            "supporting_statements": [
                {"declaration": name, "line": declaration_line(text, name),
                 "url": source_url(repository, sha, source.relative_to(root),
                                   declaration_line(text, name))}
                for name in entry.get("supporting_theorems", [])],
        })
    manifest_data = json.loads(Path(manifest).read_text())
    catalogue_title = manifest_data.get("title", "Complexitylib / Formal abstracts")
    index = [r"\section*{" + render.escape_tex_prose(catalogue_title) + "}",
             "Selected proved results, with their definitions and formal statements. "
             "Proof bodies are omitted from the display and remain in the linked Lean sources.",
             r"\begin{itemize}\raggedright"]
    for entry in entries:
        index.append(r"\item{} \hyperlink{" + entry["id"] + "}{" +
                     render.escape_tex_prose(entry["title"]) + "}. " +
                     render.escape_tex_prose(entry["summary"]))
    index.extend([r"\end{itemize}", r"\clearpage"])
    catalogue = output / "catalogue.tex"
    foundations = render_foundations(all_foundations, repository, sha, root)
    catalogue.write_text(document("\n\n".join(index) + "\n\\clearpage\n".join(bodies) +
                                  ("\n\\clearpage\n" + foundations if foundations else "")))
    catalogue_pdf = build_pdf(catalogue)
    event_path = os.environ.get("GITHUB_EVENT_PATH")
    event = json.loads(Path(event_path).read_text()) if event_path else {}
    pr = event.get("pull_request", {})
    for record in input_records:
        if digest(root / record["path"]) != record["sha256"]:
            raise ValueError(f"Source changed during PDF generation: {record['path']}")
    provenance = {
        "source_sha": sha, "source_dirty": dirty, "repository": repository,
        "event": os.environ.get("GITHUB_EVENT_NAME", "local"), "ref": os.environ.get("GITHUB_REF"),
        "pull_request_number": pr.get("number"),
        "pull_request_head_sha": pr.get("head", {}).get("sha"),
        "pull_request_base_sha": pr.get("base", {}).get("sha"),
        "run_url": (f"https://github.com/{repository}/actions/runs/{os.environ['GITHUB_RUN_ID']}"
                    if os.environ.get("GITHUB_RUN_ID") else None),
        "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
        "catalogue": {"pdf": "catalogue.pdf", "pdf_sha256": digest(catalogue_pdf),
                      "foundations": list(dict.fromkeys(all_foundations))},
        "documents": documents,
        "inputs": input_records,
        "style_sources": [STYLE_SOURCE, EXTRACTION_SOURCE],
    }
    (output / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    print(f"Built {len(documents)} individual PDFs and {catalogue_pdf} from {sha}")
    return provenance


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=ROOT / "abstracts/catalogue.json")
    parser.add_argument("--output", type=Path, default=ROOT / "abstracts/build")
    parser.add_argument("--check", action="store_true", help="validate selection without building PDFs")
    parser.add_argument("--require-clean", action="store_true")
    args = parser.parse_args()
    try:
        if args.check:
            entries = load_catalogue(args.manifest)
            print(f"Catalogue selects {len(entries)} abstracts and "
                  f"{sum(len(e['headline_theorems']) for e in entries)} headline theorems.")
        else:
            build(args.manifest, args.output, require_clean=args.require_clean)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Abstract build failed: {error}\n")


if __name__ == "__main__":
    main()
