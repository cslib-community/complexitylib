#!/usr/bin/env python3
"""Shared Pandoc and LaTeX helpers for the two maintained manuals.

Use scripts/build_operator_manual.py; no archived datasets are needed.
"""
import copy
import json
import re
import subprocess
from pathlib import Path
from urllib.parse import quote, unquote, urlparse

ROOT = Path(__file__).resolve().parents[1]
OUTPUT_ROOT = ROOT / '_build'
SOURCE_REVISION = None
SOURCE_PATHS = set()
CHANGED_PATHS = set()
REPOSITORY_URL = 'https://github.com/cslib-community/complexitylib'
ORDER = [
    ('design-and-assurance', ['index', 'architecture', 'automation', 'assurance', 'upstream-and-credit']),
    ('machines-and-classes', ['index', 'native-and-resources', 'intermediate-and-legacy',
      'computability-and-description', 'verifiers-counting-interaction', 'reductions',
      'parameterized-complexity', 'search-and-promises', 'endpoints-and-hierarchies', 'native-counting']),
    ('circuits-logic-and-other-models', ['index', 'circuits-and-formulas', 'networks-and-iteration',
      'algebraic-and-quantum', 'query-and-communication', 'finite-model-logic',
      'proof-systems', 'learning-and-testing', 'metacomplexity-and-methods', 'fair-division']),
    ('programs-crypto-and-probability', ['index', 'programs-and-realization',
      'security-games-and-primitives', 'interactive-reductions', 'protocols-and-privacy',
      'average-case-hardness', 'homomorphic-encryption']),
    ('algorithms-and-memory', ['index', 'ram-variants', 'wordram-and-bridges',
      'memory-specifications', 'online-and-streaming', 'catalytic-and-tree-evaluation', 'algorithm-endpoints']),
    ('development-history', ['index', 'methods', 'timings', 'case-studies', 'transcripts', 'study-design']),
]
FILES = ['index.md'] + [f'{section}/{name}.md' for section, names in ORDER for name in names] + ['model-map.md']


def run(args, **kwargs):
    return subprocess.run(args, check=True, text=True, capture_output=True, **kwargs).stdout


def raw(kind, text):
    return {'t': kind, 'c': ['latex', text]}


def label(path, fragment=''):
    return 'doc-' + re.sub(r'[^a-zA-Z0-9-]', '-', path.removesuffix('.md')) + ('--' + fragment if fragment else '')


def tex_escape(text):
    special = {'\\': r'\textbackslash{}', '{': r'\{', '}': r'\}', '%': r'\%',
               '$': r'\$', '&': r'\&', '#': r'\#', '_': r'\_', '~': r'\textasciitilde{}', '^': r'\textasciicircum{}'}
    return ''.join(special.get(c, c) for c in text)


MATH = {'ℕ': r'\mathbb{N}', 'ℝ': r'\mathbb{R}', 'ℓ': r'\ell', '→': r'\to',
        '←': r'\leftarrow', '↔': r'\leftrightarrow', '↦': r'\mapsto', '↪': r'\hookrightarrow',
        '∀': r'\forall', '∃': r'\exists', '∈': r'\in', '∧': r'\wedge', '∩': r'\cap',
        '≠': r'\ne', '≤': r'\le', '≥': r'\ge', '⊆': r'\subseteq', '⊊': r'\subsetneq',
        '⊕': r'\oplus', '∞': r'\infty', '−': '-', '×': r'\times', 'Γ': r'\Gamma',
        'Σ': r'\Sigma', 'α': r'\alpha', 'β': r'\beta', 'δ': r'\delta', 'ε': r'\varepsilon',
        'η': r'\eta', 'ι': r'\iota', 'κ': r'\kappa', 'λ': r'\lambda', 'μ': r'\mu',
        'σ': r'\sigma', '₁': '_1', '₂': '_2', 'ᵢ': '_i', 'ⱼ': '_j', '¹': '^1', '²': '^2', '³': '^3'}


def inline_tex(text):
    # Math symbols remain inspectable even inside identifiers and table cells.
    return ''.join(r'\ensuremath{' + MATH[c] + '}' if c in MATH else tex_escape(c) for c in text)


def ast_for(text):
    return json.loads(run(['pandoc', '-f', 'markdown+autolink_bare_uris', '-t', 'json'], input=text))


def write_latex(ast):
    return run(['pandoc', '-f', 'json', '-t', 'latex', '--top-level-division=chapter', '--wrap=none'], input=json.dumps(ast))


def repository_link(resolved, parsed):
    """Link to committed repository content, never an unpublished local target."""
    try:
        relative = resolved.relative_to(ROOT.parent).as_posix()
    except ValueError as error:
        raise ValueError(f'Link target is outside the repository: {resolved}') from error
    if SOURCE_REVISION is None or relative not in SOURCE_PATHS:
        raise ValueError(f'Link target is absent from the rendered revision: {relative}; commit it first')
    if any(path == relative or path.startswith(relative + '/') for path in CHANGED_PATHS):
        raise ValueError(f'Link target has uncommitted changes: {relative}; commit them first')
    kind = 'tree' if resolved.is_dir() else 'blob'
    repository = urlparse(REPOSITORY_URL)
    path = f'{repository.path}/{kind}/{SOURCE_REVISION}/{quote(relative, safe="/")}'
    return parsed._replace(scheme=repository.scheme, netloc=repository.netloc, path=path).geturl()


def transform(node, path, chapter_index=False, references=False):
    if isinstance(node, list):
        return [transform(x, path, chapter_index, references) for x in node]
    if not isinstance(node, dict):
        return node
    typ = node.get('t')
    if typ == 'Header':
        level, attr, content = copy.deepcopy(node['c'])
        old_id = attr[0]
        attr[0] = label(path, '' if level == 1 else old_id)
        # Chapter index becomes the chapter; every leaf's title is a section.
        if path not in {'index.md', 'model-map.md'} and not chapter_index:
            level += 1
        return {'t': typ, 'c': [level, attr, transform(content, path, chapter_index, references)]}
    if typ == 'Link':
        attr, content, target = node['c']
        href, title = target
        parsed = urlparse(href)
        if not parsed.scheme and not parsed.netloc:
            resolved = (ROOT / path).parent.joinpath(unquote(parsed.path)).resolve() if parsed.path else ROOT / path
            try:
                relative = resolved.relative_to(ROOT).as_posix()
            except ValueError:
                relative = ''
            if relative == 'sources.md' and parsed.fragment:
                return raw('RawInline', r'\cite{' + parsed.fragment + '}')
            if relative == 'sources.md':
                return {'t': 'Link', 'c': [attr, transform(content, path, chapter_index, references), ['#doc-sources', title]]}
            if relative in FILES:
                return {'t': 'Link', 'c': [attr, transform(content, path, chapter_index, references), ['#' + label(relative, parsed.fragment), title]]}
            href = repository_link(resolved, parsed)
        return {'t': 'Link', 'c': [attr, transform(content, path, chapter_index, references), [href, title]]}
    if typ == 'Code':
        text = node['c'][1]
        # Allow breaks at semantic separators and within long opaque hashes.
        escaped = inline_tex(text)
        escaped = re.sub(r'(?<=[a-z0-9])(?=[A-Z])', lambda _: r'\allowbreak{}', escaped)
        escaped = escaped.replace(r'\_', r'\_\allowbreak{}').replace('.', r'.\allowbreak{}').replace('/', r'/\allowbreak{}').replace('-', r'-\allowbreak{}')
        escaped = escaped.replace('*', r'*\allowbreak{}').replace('+', r'+\allowbreak{}')
        if re.fullmatch(r'[0-9a-f]{32,}', text):
            escaped = r'\allowbreak{}'.join(text[i:i+8] for i in range(0, len(text), 8))
        return raw('RawInline', r'{\small\ttfamily ' + escaped + '}')
    if typ == 'Str' and (any(c in MATH for c in node['c']) or '/' in node['c'] or '_' in node['c'] or re.search(r'[a-z][A-Z]', node['c'])):
        escaped = inline_tex(node['c']).replace('/', r'/\allowbreak{}').replace(r'\_', r'\_\allowbreak{}')
        escaped = re.sub(r'(?<=[a-z0-9])(?=[A-Z])', lambda _: r'\allowbreak{}', escaped)
        return raw('RawInline', escaped)
    if typ in {'RawBlock', 'RawInline'} and node['c'][0] == 'html':
        match = re.search(r'<a id="([^"]+)"', node['c'][1])
        return raw(typ, r'\phantomsection\label{' + label(path, match[1]) + '}') if match else raw(typ, '')
    result = {k: transform(v, path, chapter_index, references) for k, v in node.items()}
    return result


def remove_navigation(blocks):
    """Remove redundant link-only navigation, preserving substantive paragraphs."""
    out = []
    for block in blocks:
        if block.get('t') == 'Para':
            content = block['c']
            if '"t": "Image"' not in json.dumps(content) and any(x.get('t') == 'Link' for x in content) and all(
                x.get('t') in {'Link', 'Space', 'SoftBreak'} or
                (x.get('t') == 'Str' and x.get('c') in {'·', '|', '.'}) for x in content):
                continue
        out.append(block)
    return out


PREAMBLE = r'''% Generated from the reviewed Complexitylib research dossier.
% Build: xelatex complexitylib-survey.tex (twice for cross-references).
\documentclass[11pt,letterpaper,oneside]{report}
\usepackage[margin=1in,headheight=15pt]{geometry}
\usepackage{fontspec}
\setmainfont{texgyrepagella-regular.otf}[BoldFont=texgyrepagella-bold.otf,ItalicFont=texgyrepagella-italic.otf,BoldItalicFont=texgyrepagella-bolditalic.otf]
\setsansfont{texgyreheros-regular.otf}[BoldFont=texgyreheros-bold.otf,ItalicFont=texgyreheros-italic.otf]
\setmonofont{DejaVuSansMono.ttf}[Scale=0.82,BoldFont=DejaVuSansMono-Bold.ttf,ItalicFont=DejaVuSansMono-Oblique.ttf]
\usepackage{amsmath,amssymb}
\usepackage{microtype}
\usepackage{longtable,booktabs,array,calc}
\newcounter{none}
\usepackage{graphicx}
\usepackage{fvextra}
\usepackage{xcolor}
\definecolor{inkblue}{HTML}{193C5A}
\definecolor{examplepaper}{HTML}{F3F6FA}
\usepackage[skins,breakable]{tcolorbox}
\newtcolorbox[auto counter,number within=chapter]{manualexample}[1]{
  enhanced,breakable,ignore nobreak,colback=examplepaper,colframe=inkblue,
  colbacktitle=inkblue,coltitle=white,fonttitle=\sffamily\bfseries\small,
  title={Worked example \thetcbcounter\enspace---\enspace #1},
  title after break={Worked example \thetcbcounter\enspace (continued)},
  boxrule=0.4pt,arc=1.5pt,left=10pt,right=10pt,top=7pt,bottom=7pt,
  before skip=12pt,after skip=12pt,pad at break*=5pt,
  before upper={\setlength{\parskip}{0.35em}}}
% tcolorbox loads verbatim; apply fvextra's wrapping after that package.
\DefineVerbatimEnvironment{verbatim}{Verbatim}{breaklines,breakanywhere,fontsize=\small}
\usepackage{fancyhdr}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small Complexitylib: models, design, and development}
\fancyfoot[C]{\thepage}
\renewcommand{\headrulewidth}{0.3pt}
\usepackage{xurl}
\usepackage{hyperref}
\hypersetup{colorlinks=true,linkcolor=inkblue,citecolor=inkblue,urlcolor=inkblue,
  pdftitle={Complexitylib: Models, Design, and Automated Development},
  pdfsubject={Source-based survey at revision 13e6a319},pdfauthor={Research draft}}
\urlstyle{same}
\usepackage{bookmark}
\usepackage{etoolbox}
\AtBeginEnvironment{longtable}{\small\setlength{\tabcolsep}{4pt}\renewcommand{\arraystretch}{1.15}}
\setlength{\emergencystretch}{3em}
\setlength{\parskip}{0.35em}
\setlength{\parindent}{0pt}
\setcounter{secnumdepth}{2}
\setcounter{tocdepth}{1}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\providecommand{\pandocbounded}[1]{#1}
\makeatletter
\def\maxwidth{\ifdim\Gin@nat@width>\linewidth\linewidth\else\Gin@nat@width\fi}
\def\maxheight{\ifdim\Gin@nat@height>0.85\textheight0.85\textheight\else\Gin@nat@height\fi}
\makeatother
\setkeys{Gin}{width=\maxwidth,height=\maxheight,keepaspectratio}
\begin{document}
\begin{titlepage}
\vspace*{1.25in}
{\Huge\bfseries Complexitylib\par}
\vspace{0.35in}
{\LARGE Models, Design, and Automated Development\par}
\vspace{0.5in}
{\large A source-based survey and research draft\par}
\vspace{0.7in}
\begin{minipage}{0.86\textwidth}
This survey describes the library's computational models, major results and bridges,
resource conventions, proof-engineering choices, and available development record.
The accompanying research corpus retains declaration-level evidence, data, and scripts.
This is a working survey for an academic paper; authorship and publication details
have not been assigned.
\end{minipage}
\vfill
{\large Source snapshot: 2 November 2026\par}
{\small\ttfamily 13e6a31951bf1c89a1a6258c44f9444aecbbefd8\par}
\vspace{0.2in}
{\small Desktop conversation records remain unavailable. Source inspection, hosted
validation evidence, and independent agent review have distinct scopes.\par}
\end{titlepage}
\pagenumbering{roman}
\chapter*{Abstract}
\addcontentsline{toc}{chapter}{Abstract}
Complexitylib is a Lean library of computational complexity theory built on CSLib
and Mathlib. This survey examines its computational models and their connections,
with explicit attention to encodings, uniformity, resource measures, and quantifier
order. It describes native machine interfaces, circuits, logical and information-access
models, probabilistic programs and cryptography, and RAM-based algorithms and
specifications. Major theorems are presented with the hypotheses and model boundaries
of their formal statements. The design discussion explains compositional resource
proofs, automation, semantic refinement, module interfaces, and upstream reuse.
A separate observational study uses repository history, CI records, and available
project conversations to examine automated development and human direction.
The survey includes 265 curated model and interface entries and a complete source-file
census at the stated revision. It does not certify every proof, establish a causal
productivity comparison, or claim complete coverage of conversations across machines.
\tableofcontents
\clearpage
\pagenumbering{arabic}
'''
