#!/usr/bin/env python3
"""Render a Complexitylib *Abstract.lean file into Markdown or pdflatex-ready LaTeX."""

import argparse
import hashlib
from pathlib import Path
import re
import sys

from proof_lengths import (COMMAND, COMMAND_PREFIX, MODIFIERS, command_starts, masks,
                           signature_end)


UNICODE_TO_TEX_MATH = {
    "ℕ": r"\mathbb{N}",
    "ℤ": r"\mathbb{Z}",
    "ℚ": r"\mathbb{Q}",
    "ℝ": r"\mathbb{R}",
    "↪": r"\hookrightarrow",
    "→": r"\to",
    "↦": r"\mapsto",
    "←": r"\leftarrow",
    "↔": r"\leftrightarrow",
    "∃": r"\exists",
    "∀": r"\forall",
    "∈": r"\in",
    "∉": r"\notin",
    "⊆": r"\subseteq",
    "∅": r"\emptyset",
    "∪": r"\cup",
    "∩": r"\cap",
    "∏": r"\prod",
    "∑": r"\sum",
    "⋃": r"\bigcup",
    "⊂": r"\subset",
    "⊥": r"\bot",
    "⊤": r"\top",
    "∞": r"\infty",
    "⨅": r"\inf",
    "⨆": r"\sup",
    "¬": r"\neg",
    "∧": r"\land",
    "∨": r"\lor",
    "≤": r"\le",
    "≥": r"\ge",
    "≠": r"\ne",
    "×": r"\times",
    "∘": r"\circ",
    "ᶜ": r"^{\mathsf{c}}",
    "⟨": r"\langle",
    "⟩": r"\rangle",
    "⦃": r"\{\!\{",
    "⦄": r"\}\!\}",
    "≃": r"\simeq",
    "⌈": r"\lceil",
    "⌉": r"\rceil",
    "⌊": r"\lfloor",
    "⌋": r"\rfloor",
    "·": r"\cdot",
    "ℓ": r"\ell",
    "Σ": r"\Sigma",
    "Δ": r"\Delta",
    "Π": r"\Pi",
    "α": r"\alpha",
    "β": r"\beta",
    "γ": r"\gamma",
    "δ": r"\delta",
    "ε": r"\varepsilon",
    "σ": r"\sigma",
    "τ": r"\tau",
    "φ": r"\varphi",
    "ψ": r"\psi",
    "χ": r"\chi",
    "π": r"\pi",
    "ρ": r"\rho",
    "μ": r"\mu",
    "ν": r"\nu",
    "ι": r"\iota",
    "ω": r"\omega",
    "⁻": r"^{-}",
    "⁰": r"^{0}",
    "¹": r"^{1}",
    "²": r"^{2}",
    "³": r"^{3}",
    "⁵": r"^{5}",
    "⁹": r"^{9}",
    "ˢ": r"^{\mathsf{s}}",
    "ᶠ": r"^{\mathsf{f}}",
    "₀": r"_{0}",
    "₁": r"_{1}",
    "₂": r"_{2}",
    "₊": r"_{+}",
    "ₖ": r"_{k}",
    "…": r"\dots",
    "⋯": r"\cdots",
}

UNICODE_TO_TEX_TEXT = {
    "–": "--",
    "—": "---",
    "’": "'",
    "“": "``",
    "”": "''",
    "á": r"\'{a}",
    "é": r"\'{e}",
    "É": r"\'{E}",
    "ő": r"\H{o}",
    "å": r"\r{a}",
    **{k: f"${v}$" for k, v in UNICODE_TO_TEX_MATH.items()},
}

TEX_SPECIAL_CODE = {
    "\\": r"\textbackslash{}",
    "{": r"\{",
    "}": r"\}",
    "_": r"\_",
    "^": r"\textasciicircum{}",
    "&": r"\&",
    "#": r"\#",
    "%": r"\%",
    "$": r"\$",
    "~": r"\textasciitilde{}",
}


def lean_code(text: str) -> str:
    """Mask comments and literals, preserving source positions and line numbers."""
    return masks(text)[1]


def module_source_path(module: str, root: Path) -> Path:
    """Resolve a module in the dedicated abstract library, never an arbitrary path."""
    if not isinstance(module, str) or not re.fullmatch(
            r"ComplexityAbstracts\.[A-Za-z_][A-Za-z0-9_]*", module):
        raise ValueError(f"Not a formal-abstract module: {module}")
    return Path(root).joinpath("abstracts", *module.split(".")).with_suffix(".lean")


def foundation_modules(source: Path, root: Path) -> list[str]:
    """Find directly imported shared foundations and their dependency closure in source order.

    Bridges and the audit helper supply proofs, not displayed definitions. Imports from outside
    the abstract library are handled by Lean's dependency audit rather than this display check.
    """
    ordered, visiting, visited = [], set(), set()

    def visit(path):
        for match in re.finditer(r"^\s*(?:(?:public|meta)\s+)*import\s+([^\n]+)",
                                 lean_code(path.read_text()), re.MULTILINE):
            for module in match.group(1).split():
                if not module.startswith("ComplexityAbstracts."):
                    continue
                dependency = module_source_path(module, root)
                if module == "ComplexityAbstracts.Check" or module.endswith("Bridge"):
                    continue
                if module.endswith("Abstract"):
                    raise ValueError(f"A shared foundation cannot be another abstract: {module}")
                if module in visiting:
                    raise ValueError(f"Cyclic shared foundations: {module}")
                if module not in visited:
                    visiting.add(module)
                    visit(dependency)
                    visiting.remove(module)
                    visited.add(module)
                    ordered.append(module)

    visit(Path(source))
    return ordered


def parse_abstract(text: str):
    """Extract the title, module introduction, and alternating docstring/code sections."""
    mod_match = re.search(r"/-\!\s*#\s*([^\n]+)\n(.*?)-/", text, re.DOTALL)
    title = mod_match.group(1).strip() if mod_match else "Formal Abstract"
    intro = mod_match.group(2).strip() if mod_match else ""
    body_start = mod_match.end() if mod_match else 0
    body = text[body_start:]
    body = re.sub(r"^\s*namespace\s+[^\n]+\n", "", body, flags=re.MULTILINE)
    # Drop audit commands together with the `#guard_msgs` docstrings pinning their reports.
    body = re.sub(
        r"/--(?:(?!-/).)*-/\s*#guard_msgs[^\n]*\n"
        r"(?=\s*#(?:check_abstract\b|print\s+axioms\b))",
        "",
        body,
        flags=re.DOTALL,
    )
    body = re.sub(
        r"^\s*#check_abstract\b[^\[\n]*(?:\[[^\]]*\])?[^\n]*\n?",
        "",
        body,
        flags=re.MULTILINE,
    )
    body = re.sub(r"^\s*#print\s+axioms\b[^\n]*\n?", "", body, flags=re.MULTILINE)
    body = re.sub(r"^\s*end\s+[^\n]+\n?", "", body, flags=re.MULTILINE)

    sections = []
    pos = 0
    for m in re.finditer(r"(/-\!(.*?)-/|/--(.*?)-/)", body, re.DOTALL):
        code_before = body[pos:m.start()].strip()
        if code_before:
            if not sections:
                sections.append({"kind": "section", "doc": "", "code": code_before})
            else:
                sections[-1]["code"] += ("\n\n" if sections[-1]["code"] else "") + code_before
        is_section = m.group(1).startswith("/-!")
        doc = (m.group(2) if is_section else m.group(3)).strip()
        sections.append({"kind": "section" if is_section else "decl", "doc": doc, "code": ""})
        pos = m.end()
    trailing = body[pos:].strip()
    if trailing:
        if not sections:
            sections.append({"kind": "section", "doc": "", "code": trailing})
        else:
            sections[-1]["code"] += ("\n\n" if sections[-1]["code"] else "") + trailing
    return title, intro, sections


def section_heading(item: dict):
    return (re.match(r"^##\s+([^\n]+)\n?(.*)", item["doc"], re.DOTALL)
            if item["kind"] == "section" else None)


def split_sections(sections: list[dict]) -> tuple[list[dict], list[dict]]:
    """Keep the mathematical presentation first and move marked representation details last."""
    main, details, destination = [], [], "main"
    for item in sections:
        heading = section_heading(item)
        if heading:
            destination = "details" if heading.group(1).strip() == "Representation details" else "main"
        (details if destination == "details" else main).append(item)
    return main, details


def presentation_sections(sections: list[dict]) -> list[dict]:
    main, details = split_sections(sections)
    if not details:
        return main
    appendix = [{"kind": "section", "doc": "## Appendix: representation details", "code": ""}]
    for item in details:
        heading = section_heading(item)
        appendix.append({**item, "doc": heading.group(2).strip()} if heading else item)
    return main + appendix


# Text at column 0 that can continue a declaration after its body begins.
DECLARATION_CONTINUATION = re.compile(
    r"\||where\b|termination_by\b|decreasing_by\b|deriving\b|[)\]}⟩⦄]")


def split_commands(code: str) -> list[str]:
    """Split Lean source into its top-level commands at keyword boundaries, not blank lines.

    Text before the first command stays with it. Comments that begin at column 0 between two
    commands move with the command that follows them.
    """
    comments_masked, syntax = masks(code)
    cuts = [0]
    for start in command_starts(syntax)[1:]:
        cut = start
        line = code.find("\n", len(comments_masked[:start].rstrip())) + 1
        while 0 < line < start:
            if not code[line].isspace():
                cut = line
                break
            line = code.find("\n", line) + 1
        cuts.append(cut)
    blocks = (code[start:end].strip() for start, end in zip(cuts, [*cuts[1:], len(code)]))
    return [block for block in blocks if block]


def strip_theorem_proof(block: str) -> str:
    """Keep a theorem's attributes and complete statement, omitting its proof.

    The statement ends at the shared scanner's proof `:=` (or `where`/equation clauses), so
    assignments in `let`/`have` bindings, brackets, comments and strings are kept. Fails rather
    than omit top-level text after the theorem that the command scanner does not recognize.
    """
    masked = lean_code(block)
    try:
        end, body = signature_end(masked)
    except ValueError as error:
        raise ValueError(f"{theorem_name(block)}: {error}") from error
    for line in masked[body:].splitlines()[1:]:
        if line[:1].strip() and not DECLARATION_CONTINUATION.match(line):
            raise ValueError(f"Unrecognized top-level command after theorem "
                             f"{theorem_name(block)}: {line.strip()[:60]}")
    return block[:end].rstrip()


INJECTIVITY_HELPER_RE = re.compile(
    r"^(?:private\s+)?theorem\s+\S*_injective\s*(?:(?:\{[^}]*\}|\([^)]*\))\s*)*:\s*"
    r"Function\.Injective\b"
)


def declaration_body(block: str) -> str:
    """Skip leading comments, `… in` prefix commands and attributes, without interpreting
    comments or quoted strings as syntax."""
    masked = lean_code(block)
    pos = len(masked) - len(masked.lstrip())
    for command in COMMAND.finditer(masked):
        if command.start() > pos and COMMAND_PREFIX.search(masked[:command.start()].rstrip()):
            pos = command.start()
    while masked.startswith("@[", pos):
        depth, end = 1, pos + 2
        while end < len(masked) and depth:
            depth += (masked[end] == "[") - (masked[end] == "]")
            end += 1
        if depth:
            return block[pos:]
        pos = end
        while pos < len(masked) and masked[pos].isspace():
            pos += 1
    return block[pos:]


THEOREM_RE = re.compile(MODIFIERS + r"(?:theorem|lemma)\s+([^\s:{(\[⦃]+)")


def theorem_name(block: str):
    match = THEOREM_RE.match(declaration_body(block))
    return match.group(1) if match else None


def display_blocks(code: str, is_undocumented_tail: bool = False) -> list[str]:
    """Return a code section's displayed commands: definitions, and theorem signatures
    without their proofs.

    The only declarations omitted are undocumented `*_injective` helper theorems that follow a
    definition block or a section docstring: they are the injectivity glue for packaging an
    encoding as an embedding (see the lean-abstract skill). Every other theorem keeps its
    signature.
    """
    kept = []
    for index, block in enumerate(split_commands(code)):
        if INJECTIVITY_HELPER_RE.match(declaration_body(block)) and (index or is_undocumented_tail):
            continue
        if theorem_name(block):
            kept.append(strip_theorem_proof(block))
        else:
            # Replace inline proof terms `, by ...⟩` inside structure constructors with `, _⟩`
            kept.append(re.sub(r",\s*by\s+[^⟩]+⟩", ", _⟩", block))
    return kept


def clean_code_for_display(code: str, is_undocumented_tail: bool = False) -> str:
    """Join a code section's displayed commands (see `display_blocks`)."""
    return "\n\n".join(display_blocks(code, is_undocumented_tail))


def escape_tex_code_line(line: str) -> str:
    """Convert a single line of Lean code into pdflatex-safe monospaced LaTeX."""
    leading = len(line) - len(line.lstrip(" "))
    rest = line[leading:]
    out = [r"\hspace*{" + f"{leading * 0.5:.1f}em" + "}"] if leading else []
    for index, ch in enumerate(rest):
        if index and rest[index - 1].islower() and ch.isupper():
            out.append(r"\allowbreak{}")
        if ch in UNICODE_TO_TEX_MATH:
            out.append(f"${UNICODE_TO_TEX_MATH[ch]}$")
        elif ch in UNICODE_TO_TEX_TEXT:
            out.append(UNICODE_TO_TEX_TEXT[ch])
        elif ch in TEX_SPECIAL_CODE:
            out.append(TEX_SPECIAL_CODE[ch])
        else:
            out.append(ch)
        # Keep every visible character while allowing long identifiers to wrap at camel-case
        # boundaries (above) and at qualified-name / snake_case separators.
        if ch in (".", "_"):
            out.append(r"\allowbreak{}")
    return "".join(out)


def escape_tex_prose(text: str) -> str:
    """Convert docstring prose (with inline `...` code spans and **bold**) into pdflatex."""
    # Split by inline code spans `...` first so `**` inside code is untouched
    parts = re.split(r"(`[^`]+`|\[[^\[\]]+\]\s*\[[A-Za-z0-9_:.-]+\])", text)
    rendered = []
    for part in parts:
        reference = re.fullmatch(r"\[([^\[\]]+)\]\s*\[([A-Za-z0-9_:.-]+)\]", part)
        if reference:
            rendered.append(escape_tex_prose(reference.group(1)) +
                            r" {\footnotesize (" + escape_tex_prose(reference.group(2)) + ")}")
        elif part.startswith("`") and part.endswith("`"):
            inner = part[1:-1]
            escaped = escape_tex_code_line(inner)
            rendered.append(f"\\texttt{{{escaped}}}")
        else:
            out = []
            for ch in part:
                if ch in UNICODE_TO_TEX_TEXT:
                    out.append(UNICODE_TO_TEX_TEXT[ch])
                elif ch in TEX_SPECIAL_CODE:
                    out.append(TEX_SPECIAL_CODE[ch])
                else:
                    out.append(ch)
            escaped_prose = "".join(out)
            escaped_prose = re.sub(r"\*\*([^*]+)\*\*", r"\\textbf{\1}", escaped_prose)
            escaped_prose = re.sub(r"\*([^*\s][^*]*)\*", r"\\emph{\1}", escaped_prose)
            escaped_prose = escaped_prose.replace("][", r"]\allowbreak{}[")
            rendered.append(escaped_prose)
    return "".join(rendered)


def render_tex_intro(intro: str) -> list[str]:
    """Render the module docstring, turning `## Heading` lines into paragraphs and `* ` bullet
    lines into an itemized list."""
    lines = []
    in_list = False
    item_parts = []
    paragraph = []

    def flush_paragraph():
        if paragraph:
            lines.append(escape_tex_prose(" ".join(paragraph)))
            paragraph.clear()

    for raw in intro.splitlines():
        line = raw.strip()
        if line.startswith("* "):
            flush_paragraph()
            if not in_list:
                lines.append("\\begin{itemize}\\raggedright")
                in_list = True
            else:
                lines.append("\\item{} " + escape_tex_prose(" ".join(item_parts)))
            item_parts = [line[2:]]
            continue
        if in_list and line and raw[:1].isspace():
            item_parts.append(line)
            continue
        if in_list and line:
            # The empty group prevents a reference's `[author/title]` from becoming the
            # optional item label. Escape after joining continuations so emphasis survives.
            lines.append("\\item{} " + escape_tex_prose(" ".join(item_parts)))
            lines.append("\\end{itemize}")
            in_list = False
        heading = re.match(r"^##\s*(.+)$", line)
        if heading:
            flush_paragraph()
            lines.append(f"\\subsubsection*{{{escape_tex_prose(heading.group(1).strip())}}}")
        elif line:
            paragraph.append(line)
        else:
            flush_paragraph()
    if in_list:
        lines.append("\\item{} " + escape_tex_prose(" ".join(item_parts)))
        lines.append("\\end{itemize}")
    flush_paragraph()
    return lines


def render_tex_paragraphs(text: str) -> list[str]:
    """Render docstring prose into complete LaTeX paragraphs, preserving blank-line boundaries."""
    paragraphs = []
    for block in re.split(r"\n\s*\n", text.strip()):
        lines = [line.strip() for line in block.splitlines() if line.strip()]
        if lines:
            paragraphs.append(escape_tex_prose(" ".join(lines)))
    return paragraphs


def render_tex(title: str, intro: str, sections: list[dict]) -> str:
    lines = [f"\\subsection{{{escape_tex_prose(title)}}}", "", *render_tex_intro(intro), ""]
    for item in presentation_sections(sections):
        doc = item["doc"]
        if item["kind"] == "section":
            m = re.match(r"^##\s*([^\n]+)\n?(.*)", doc, re.DOTALL)
            if m:
                heading = escape_tex_prose(m.group(1).strip())
                paragraphs = render_tex_paragraphs(m.group(2))
                lines.append(f"\\subsubsection*{{{heading}}}")
                for paragraph in paragraphs:
                    lines.extend(["", paragraph])
            else:
                for index, paragraph in enumerate(render_tex_paragraphs(doc)):
                    if index:
                        lines.append("")
                    lines.append(paragraph)
        else:
            for index, paragraph in enumerate(render_tex_paragraphs(doc)):
                if index:
                    lines.append("")
                lines.append(paragraph)
        code = clean_code_for_display(item["code"], is_undocumented_tail=(item["kind"] == "section"))
        if code:
            code_lines = [escape_tex_code_line(l) for l in code.splitlines()]
            joined = " \\\\\n".join(l if l else "~" for l in code_lines)
            lines.extend([
                "\\begin{quote}\\small\\ttfamily\\raggedright\\noindent",
                joined,
                "\\end{quote}",
            ])
        lines.append("")
    return "\n".join(lines).strip() + "\n"


def render_markdown(title: str, intro: str, sections: list[dict]) -> str:
    lines = [f"# {title}", "", intro, ""]
    for item in presentation_sections(sections):
        lines.append(item["doc"])
        code = clean_code_for_display(item["code"], is_undocumented_tail=(item["kind"] == "section"))
        if code:
            lines.extend(["", "```lean", code, "```"])
        lines.append("")
    return "\n".join(lines).strip() + "\n"


def render_source(path: Path, format: str) -> str:
    """Render one source and its shared foundations for a standalone local preview."""
    path = path.resolve()
    renderer = render_tex if format == "tex" else render_markdown
    result = renderer(*parse_abstract(path.read_text()))
    root = path.parent.parent.parent
    modules = foundation_modules(path, root)
    for module in modules:
        source = module_source_path(module, root)
        title, intro, sections = parse_abstract(source.read_text())
        sha = hashlib.sha256(source.read_bytes()).hexdigest()
        provenance = f"Source: `{source.relative_to(root)}`. SHA256: `{sha}`."
        if format == "markdown":
            provenance = f"[Lean source]({source.as_uri()}). SHA256: `{sha}`."
        result += "\n" + renderer("Shared foundation: " + title,
                                    provenance + "\n\n" + intro, sections)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path, help="Path to *Abstract.lean file")
    parser.add_argument("--format", choices=("markdown", "tex"), default="markdown")
    args = parser.parse_args()
    try:
        sys.stdout.write(render_source(args.path, args.format))
    except (OSError, ValueError) as error:
        parser.exit(1, f"Abstract render failed: {error}\n")


if __name__ == "__main__":
    main()
