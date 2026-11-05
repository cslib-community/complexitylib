#!/usr/bin/env python3
"""Assemble the Operator's Manual or the short human Agent Operator's Manual.

Use scripts/build_operator_manual.py for the checked entry point. This converter
requires Pandoc; the PDF build additionally uses XeLaTeX/pdfinfo.
"""
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

import build_latex as base
import visuals

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
WORKFLOWS = ['README.md', 'workflows/index.md', 'workflows/getting-started.md',
             'workflows/choosing-models.md', 'workflows/deterministic-workflows.md',
             'workflows/probabilistic-workflows.md', 'workflows/finding-results.md',
             'workflows/troubleshooting.md', 'workflows/contributing.md', 'COMMANDS.md']
REFERENCE = [f'{s}/{n}.md' for s, names in base.ORDER[:-1] for n in names]
HISTORY = [f'development-history/{n}.md' for n in base.ORDER[-1][1]]
APPENDICES = ['model-map.md', 'MAINTAINING.md', 'BUILD.md', 'workflows/agent-operations.md', 'index.md']
FILES = WORKFLOWS + REFERENCE + HISTORY + APPENDICES
STEM = 'complexitylib-operators-manual'
AGENT_STEM = 'complexitylib-agent-operators-manual'
AGENT_FILES = ['AGENT_OPERATORS.md']
HISTORICAL_REVISION = '13e6a31951bf1c89a1a6258c44f9444aecbbefd8'
EXCLUDED_DIRECTORIES = {'_build', '_generated', '__pycache__'}
# Bibliography bodies are rendered separately; the old paper plan is archival editorial context.
NON_CHAPTER_DOCUMENTS = {'sources.md', 'paper-plan.md', 'AGENT_OPERATORS.md'}
CONVERTER_INPUTS = ['data/build_manual.py', 'data/build_latex.py', 'data/visuals.py']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_bibliography(text):
    """Read canonical keys, headings and full bodies from sources.md text."""
    markers = list(re.finditer(r'^<a id="([a-z0-9-]+)"></a>\s*\n## ([^\n]+)\n', text, re.M))
    if not markers:
        raise ValueError('No bibliography entries in sources.md')
    if len(markers) != len(re.findall(r'<a\s+id=', text)):
        raise ValueError('Malformed bibliography anchor or heading in sources.md')
    entries = {}
    for index, marker in enumerate(markers):
        key, heading = marker.groups()
        if key != heading.strip() or key in entries:
            raise ValueError(f'Duplicate or mismatched bibliography key: {key}')
        end = markers[index + 1].start() if index + 1 < len(markers) else len(text)
        body = text[marker.end():end].strip()
        if not body:
            raise ValueError(f'Empty bibliography entry: {key}')
        entries[key] = body
    return entries


def bibliography_entries(path):
    return parse_bibliography(path.read_text())


def validate_inputs(root, files, agent=False):
    """Fail when a maintained page is absent from the book or appears twice."""
    if len(files) != len(set(files)):
        raise ValueError('Duplicate book chapter input')
    if not (root / 'AGENT_OPERATORS.md').is_file():
        raise ValueError("Missing Agent Operator's Manual: AGENT_OPERATORS.md")
    expected = set(AGENT_FILES) if agent else {
        path.relative_to(root).as_posix() for path in root.rglob('*.md')
        if not EXCLUDED_DIRECTORIES.intersection(path.relative_to(root).parts)
    } - NON_CHAPTER_DOCUMENTS
    missing, extra = expected - set(files), set(files) - expected
    if missing or extra:
        raise ValueError(f'Book chapter inputs differ: missing={sorted(missing)}, extra={sorted(extra)}')


def validate_manifest(root, output, files, check_pdf=True, agent=False):
    """Reject stale or incomplete source provenance, including bibliography drift."""
    validate_inputs(root, files, agent=agent)
    stem = AGENT_STEM if agent else STEM
    name = 'agent-manual-source-manifest.json' if agent else 'manual-source-manifest.json'
    manifest = json.loads((output / name).read_text())
    if manifest.get('manual_kind') != ('agent-operators' if agent else 'operators'):
        raise ValueError('Manifest describes the other manual')
    if set(manifest['chapter_inputs']) != set(files):
        raise ValueError('Manifest chapter inputs differ from the book')
    for path in files:
        if manifest['chapter_inputs'][path] != sha(root / path):
            raise ValueError(f'Stale chapter hash: {path}')
    if manifest['bibliography_sha256'] != (None if agent else sha(root / 'sources.md')):
        raise ValueError('Stale bibliography hash: sources.md')
    if manifest['bibliography_keys'] != ([] if agent else list(bibliography_entries(root / 'sources.md'))):
        raise ValueError('Manifest bibliography keys differ from sources.md')
    tex = output / (stem + '.tex')
    if manifest['latex_sha256'] != sha(tex):
        raise ValueError('Stale generated LaTeX hash')
    if re.findall(r'^% Source: (.+)$', tex.read_text(), re.M) != files:
        raise ValueError('Generated LaTeX chapter order differs from the book')
    if manifest.get('figure_inputs') != {}:
        raise ValueError('Unexpected figure inputs; rebuild from the maintained sources')
    figures = manifest.get('diagram_outputs', {})
    if set(figures) != visuals.expected_diagrams(root, files):
        raise ValueError('Manifest diagrams differ from the source diagrams')
    for name, digest in figures.items():
        if not (output / name).is_file() or sha(output / name) != digest:
            raise ValueError(f'Missing or changed diagram output: {name}')
    if manifest.get('converter_inputs') != {path: sha(root / path) for path in CONVERTER_INPUTS}:
        raise ValueError('Stale converter inputs')
    if check_pdf:
        pdf = output / (stem + '.pdf')
        if pdf.exists() or 'pdf_sha256' in manifest:
            if not pdf.is_file() or manifest.get('pdf_sha256') != sha(pdf):
                raise ValueError('PDF is missing, changed or not from this full build; rebuild the PDF')


def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args], text=True).strip()


def write(ast):
    return base.run(['pandoc', '-f', 'json', '-t', 'latex', '--no-highlight',
                     '--top-level-division=chapter', '--wrap=none'], input=json.dumps(ast))


def preamble(revision, dirty, agent=False):
    title = "Complexitylib Agent Operator's Manual" if agent else "Complexitylib Operator's Manual"
    short_title = "Agent Operator's Manual" if agent else "Operator's Manual"
    stem = AGENT_STEM if agent else STEM
    text = base.PREAMBLE.split(r'\begin{document}')[0]
    text = text.replace('% Generated from the reviewed Complexitylib research dossier.',
                        '% Generated from the canonical ' + title + '.')
    text = text.replace('xelatex complexitylib-survey.tex (twice for cross-references).',
                        f'xelatex {stem}.tex (three times for cross-references).')
    text = text.replace('Complexitylib: models, design, and development', title)
    text = text.replace('Complexitylib: Models, Design, and Automated Development', title)
    text = text.replace('Source-based survey at revision 13e6a319',
                        'Human direction of agents' if agent else 'Using and extending Complexitylib')
    text = text.replace('pdfauthor={Research draft}', 'pdfauthor={}')
    text += r'''
\makeatletter
\renewcommand*\l@section{\@dottedtocline{1}{1.5em}{3.5em}}
\makeatother
\begin{document}
\begin{titlepage}
\vspace*{1.1in}
{\Huge\bfseries Complexitylib\par}
\vspace{0.25in}
{\LARGE MANUAL-TITLE\par}
\vspace{0.4in}
{\large Using, extending, and reviewing the library\par}
\vspace{0.65in}
\begin{minipage}{0.87\textwidth}
A practical guide for humans or agents: install the library, check a complete
client, select a model, state a resource contract, compose proofs, diagnose failures,
and prepare a reviewed contribution. Model and theorem references follow the task
instructions. The separate Agent Operator's Manual guides the human driving agents.
\end{minipage}
\vfill
{\large Built from the source checkout\par}
'''
    text = text.replace('MANUAL-TITLE', short_title)
    if agent:
        text = text.replace('Using, extending, and reviewing the library', 'A short guide for the human directing agents')
        text = text.replace('A practical guide for humans or agents: install the library, check a complete\n'
                            'client, select a model, state a resource contract, compose proofs, diagnose failures,\n'
                            'and prepare a reviewed contribution. Model and theorem references follow the task\n'
                            "instructions. The separate Agent Operator's Manual guides the human driving agents.",
                            'Choose roles, assign bounded work, arrange independent review, inspect evidence,\n'
                            'hand off safely and intervene when a session goes off course. Codebase tasks\n'
                            "are documented in the substantial Operator's Manual.")
    text += '{\\small\\ttfamily ' + base.tex_escape(revision + (' (working changes)' if dirty else '')) + '\\par}\n'
    if not agent:
        text += r'''
\vspace{0.25in}
{\small The baseline source survey and historical measurements are dated
2 November 2026 at revision 13e6a319. Desktop conversations are absent from that
historical dataset. See the source manifest for this build's inputs.\par}
'''
    text += r'''
\end{titlepage}
\pagenumbering{roman}
\tableofcontents
\clearpage
\pagenumbering{arabic}
'''
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tex-only', action='store_true')
    parser.add_argument('--output-dir', type=Path, default=ROOT / '_build')
    parser.add_argument('--check-build', type=Path,
                        help='Check an existing build manifest against current inputs without rebuilding')
    parser.add_argument('--agent-manual', action='store_true',
                        help="Build or check the short human Agent Operator's Manual")
    args = parser.parse_args()
    files = AGENT_FILES if args.agent_manual else FILES
    stem = AGENT_STEM if args.agent_manual else STEM
    manifest_name = 'agent-manual-source-manifest.json' if args.agent_manual else 'manual-source-manifest.json'
    if args.check_build:
        validate_manifest(ROOT, args.check_build.resolve(), files, agent=args.agent_manual)
        print(json.dumps({'status': 'pass', 'build_inputs_current': True,
                          'manual_kind': 'agent-operators' if args.agent_manual else 'operators',
                          'pdf_verified': (args.check_build / (stem + '.pdf')).is_file(),
                          'output_directory': str(args.check_build.resolve())}))
        return
    validate_inputs(ROOT, files, agent=args.agent_manual)
    bibliography_source = b'' if args.agent_manual else (ROOT / 'sources.md').read_bytes()
    entries = {} if args.agent_manual else parse_bibliography(bibliography_source.decode())
    bibliography_hash = None if args.agent_manual else hashlib.sha256(bibliography_source).hexdigest()
    converter_inputs = {path: sha(ROOT / path) for path in CONVERTER_INPUTS}
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    base.FILES = files
    base.OUTPUT_ROOT = out
    original_transform = base.transform

    def transform(node, path, chapter_index=False, references=False):
        if isinstance(node, dict) and node.get('t') == 'Str' and re.fullmatch(
                r'(?:TeX|LaTeX|XeLaTeX)[.,;:!?]?', node.get('c', '')):
            return base.raw('RawInline', r'\mbox{' + base.tex_escape(node['c']) + '}')
        return original_transform(node, path, chapter_index, references)

    base.transform = transform
    revision, dirty = git('rev-parse', 'HEAD'), bool(git('status', '--porcelain'))
    base.SOURCE_REVISION = revision
    base.SOURCE_PATHS = set(git('ls-tree', '-r', '-t', '-z', '--name-only', revision).split('\0'))
    base.CHANGED_PATHS = set(git('diff', '--name-only', '-z', revision, '--').split('\0'))
    parts, inputs, figure_outputs = [preamble(revision, dirty, agent=args.agent_manual)], {}, {}
    for relative in files:
        if not args.agent_manual and relative == WORKFLOWS[0]:
            parts.append(r'\part{Using Complexitylib}' + '\n')
        elif relative == REFERENCE[0]:
            parts.append(r'\part{Models, theorems, and design reference}' + '\n')
        elif relative == HISTORY[0]:
            parts.append(r'\part{Historical development record}' + '\n')
        elif relative == APPENDICES[0]:
            parts.append(r'\appendix' + '\n')
        path = ROOT / relative
        inputs[relative] = sha(path)
        ast = base.ast_for(path.read_text())
        ast['blocks'] = base.remove_navigation(ast['blocks'])
        ast['blocks'] = visuals.render_blocks(ast['blocks'], relative, out, figure_outputs, base.tex_escape)
        is_chapter = args.agent_manual or relative in WORKFLOWS or relative in APPENDICES or relative.endswith('/index.md')
        ast = base.transform(ast, relative, is_chapter)
        parts.append(f'\n% Source: {relative}\n' + write(ast))
    keys = list(entries)
    if keys:
        parts.append('\n\\clearpage\n\\phantomsection\n\\label{doc-sources}\n'
                     '\\addcontentsline{toc}{chapter}{Bibliography and source provenance}\n')
        parts.append(r'\renewcommand{\bibname}{Bibliography and source provenance}' + '\n')
        parts.append(r'\begin{thebibliography}{99}' + '\n')
        for key in keys:
            ast = base.transform(base.ast_for(entries[key]), 'sources.md', references=True)
            parts.append(r'\bibitem{' + key + '}\n' + write(ast))
        parts.append(r'\end{thebibliography}' + '\n')
    parts.append(r'\end{document}' + '\n')
    target = out / (stem + '.tex')
    target.write_text(''.join(parts))
    manifest = {
        'validates': 'Generated book chapter and bibliography identity; not Lean or semantic validation.',
        'manual_kind': 'agent-operators' if args.agent_manual else 'operators',
        'source_revision': revision, 'source_checkout_dirty': dirty,
        'historical_revision': None if args.agent_manual else HISTORICAL_REVISION, 'chapter_inputs': inputs,
        'bibliography_keys': keys, 'bibliography_sha256': bibliography_hash,
        'latex_sha256': sha(target), 'workflow_documents': 1 if args.agent_manual else len(WORKFLOWS),
        'model_reference_documents': 0 if args.agent_manual else len(REFERENCE),
        'history_documents': 0 if args.agent_manual else len(HISTORY),
        'appendix_documents': 0 if args.agent_manual else len(APPENDICES),
        'figure_inputs': {}, 'diagram_outputs': figure_outputs, 'converter_inputs': converter_inputs,
    }
    if not args.tex_only:
        for _ in range(3):
            result = subprocess.run(['xelatex', '-halt-on-error', '-interaction=nonstopmode',
                                     '-file-line-error', target.name], cwd=out,
                                    text=True, capture_output=True)
            if result.returncode:
                print((result.stdout + result.stderr)[-7000:])
                raise SystemExit(result.returncode)
        (out / ('agent-manual-build-output.txt' if args.agent_manual else 'manual-build-output.txt')).write_text(result.stdout + result.stderr)
        manifest['pdf_sha256'] = sha(out / (stem + '.pdf'))
        print(base.run(['pdfinfo', str(out / (stem + '.pdf'))]))
    (out / manifest_name).write_text(json.dumps(manifest, indent=2) + '\n')
    validate_manifest(ROOT, out, files, check_pdf=not args.tex_only, agent=args.agent_manual)
    print(json.dumps({'latex': str(target), 'chapter_documents': len(files),
                      'bibliography_entries': len(keys)}))


if __name__ == '__main__':
    main()
