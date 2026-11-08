"""Render the manual's small Mermaid flowcharts and explicit worked examples.

Markdown is the single source. GitHub renders the Mermaid blocks; the PDF build
uses Graphviz for the documented flowchart subset. Unsupported syntax fails
rather than silently dropping part of a mathematical model diagram.
"""
import hashlib
import json
import re
import subprocess
import textwrap
from pathlib import PurePosixPath

FENCE = re.compile(r'^\s*(`{3,}|~{3,})(.*)$')
IDENTIFIER = r'[A-Za-z][A-Za-z0-9_]*'
NODE = re.compile(rf'({IDENTIFIER})\["([^"\n]+)"\]')
EDGE = re.compile(rf'({IDENTIFIER})\s+(-->|-\.->)(?:\|"([^"\n]+)"\|)?\s+({IDENTIFIER})')
OPEN_EXAMPLE = '<!-- worked-example -->'
CLOSE_EXAMPLE = '<!-- /worked-example -->'
TITLE = re.compile(r'^\*\*Worked example: (.+)\*\*$')


def flowchart(source):
    lines = [(number, line.strip()) for number, line in enumerate(source.splitlines(), 1)
             if line.strip() and not line.lstrip().startswith('%%')]
    if not lines or not re.fullmatch(r'flowchart (TB|LR)', lines[0][1]):
        raise ValueError('Diagram must start with flowchart TB or flowchart LR')
    nodes, edges = {}, []
    for number, line in lines[1:]:
        node, edge = NODE.fullmatch(line), EDGE.fullmatch(line)
        if node:
            key, label = node.groups()
            if key in nodes:
                raise ValueError(f'Diagram line {number}: duplicate node {key}')
            if re.search(r'[<>]', label.replace('<br/>', '')):
                raise ValueError(f'Diagram line {number}: only <br/> is supported in labels')
            nodes[key] = label.replace('<br/>', '\n')
        elif edge:
            start, arrow, label, end = edge.groups()
            if label and re.search(r'[<>]', label.replace('<br/>', '')):
                raise ValueError(f'Diagram line {number}: only <br/> is supported in labels')
            edges.append((start, end, (label or '').replace('<br/>', '\n'), arrow == '-.->'))
        else:
            raise ValueError(f'Diagram line {number}: unsupported flowchart syntax: {line}')
    if not nodes or not edges:
        raise ValueError('Diagram needs named nodes and at least one edge')
    for start, end, _, _ in edges:
        if start not in nodes or end not in nodes:
            raise ValueError(f'Diagram edge {start} -> {end}: define both nodes explicitly')
    return lines[0][1].split()[1], nodes, edges


def diagram_sources(text):
    """Return top-level Mermaid blocks, ignoring literal fenced examples."""
    result, body, fence, mermaid = [], [], None, False
    for number, line in enumerate(text.splitlines(), 1):
        match = FENCE.match(line)
        if fence:
            if match and match[1][0] == fence[0] and len(match[1]) >= len(fence) and not match[2].strip():
                if mermaid:
                    result.append('\n'.join(body))
                fence, body, mermaid = None, [], False
            else:
                body.append(line)
        else:
            # Recognize nested openings only to reject them. Pandoc's AST is
            # checked too, including nesting that needs full Markdown parsing.
            unquoted = re.sub(r'^(?:[ \t]*>[ \t]*)+', '', line)
            unnested = re.sub(r'^[ \t]*(?:[-+*]|\d+[.)])[ \t]+', '', unquoted)
            nested = FENCE.match(unnested)
            if nested and nested[2].strip() == 'mermaid' and (
                    unnested != line or line != line.lstrip()):
                raise ValueError(f'Line {number}: Mermaid fences must be unindented top-level blocks')
            if match:
                fence, mermaid = match[1], match[2].strip() == 'mermaid'
    if fence and mermaid:
        raise ValueError('Unclosed Mermaid code fence')
    return result


def check_markup(text):
    """Check diagram syntax and example boundaries without publishing tools."""
    diagrams = diagram_sources(text)
    for source in diagrams:
        flowchart(source)
    active, awaiting_title, fence, examples = False, False, None, 0
    for number, line in enumerate(text.splitlines(), 1):
        match = FENCE.match(line)
        if fence:
            if match and match[1][0] == fence[0] and len(match[1]) >= len(fence) and not match[2].strip():
                fence = None
            continue
        if match:
            if awaiting_title:
                raise ValueError(f'Line {number}: example needs a bold Worked example title first')
            fence = match[1]
            continue
        stripped = line.strip()
        if stripped == OPEN_EXAMPLE:
            if active:
                raise ValueError(f'Line {number}: nested worked examples are not supported')
            active, awaiting_title = True, True
            examples += 1
        elif stripped == CLOSE_EXAMPLE:
            if not active or awaiting_title:
                raise ValueError(f'Line {number}: unmatched or empty worked example')
            active = False
        elif awaiting_title and stripped:
            if not TITLE.fullmatch(stripped):
                raise ValueError(f'Line {number}: expected **Worked example: Title**')
            awaiting_title = False
        elif active and re.match(r'\s{0,3}#{1,6}\s', line):
            raise ValueError(f'Line {number}: end the worked example before a heading')
    if active:
        raise ValueError('Unclosed worked example')
    return {'diagrams': len(diagrams), 'worked_examples': examples}


def diagram_name(document, number):
    if not re.fullmatch(r'(?:[A-Za-z0-9_-]+/)*[A-Za-z0-9_-]+\.md', document):
        raise ValueError(f'Unsupported diagram source path: {document}')
    # Preserve the source hierarchy: topic-one.md and topic/one.md must never
    # overwrite each other's assets or collapse in the freshness manifest.
    stem = PurePosixPath(document).with_suffix('').as_posix()
    return f'figures/{stem}-{number}.pdf'


def expected_diagrams(root, files):
    return {diagram_name(document, number)
            for document in files
            for number, _ in enumerate(diagram_sources((root / document).read_text()), 1)}


def graphviz_source(source):
    direction, nodes, edges = flowchart(source)
    quote = lambda value: json.dumps(value, ensure_ascii=False)
    def wrap(value, width):
        return '\n'.join(textwrap.fill(line, width, break_long_words=False, break_on_hyphens=False)
                         for line in value.split('\n'))
    lines = ['digraph model {', f'  rankdir={direction};',
             '  graph [bgcolor="transparent", pad="0.12", nodesep="0.36", ranksep="0.55"];',
             '  node [shape=box, style="rounded,filled", color="#36576B", fillcolor="#F0F5F8",',
             '        fontcolor="#193C5A", fontname="Arial", fontsize=13, penwidth=1.1, margin="0.16,0.12"];',
             '  edge [color="#39766E", fontcolor="#344F59", fontname="Arial", fontsize=12, arrowsize=0.7];']
    lines.extend(f'  {key} [label={quote(wrap(label, 22))}];' for key, label in nodes.items())
    for start, end, label, dotted in edges:
        attrs = [f'label={quote(wrap(label, 16))}'] if label else []
        if dotted:
            attrs.append('style=dashed')
        lines.append(f'  {start} -> {end} [{", ".join(attrs)}];')
    return '\n'.join(lines + ['}', ''])


def inline_text(inlines):
    parts = []
    for item in inlines:
        if item['t'] == 'Str':
            parts.append(item['c'])
        elif item['t'] in {'Space', 'SoftBreak'}:
            parts.append(' ')
        else:
            raise ValueError('Worked-example titles must be plain bold text')
    return ''.join(parts)


def contains_diagram(node):
    if isinstance(node, list):
        return any(contains_diagram(child) for child in node)
    if not isinstance(node, dict):
        return False
    if node.get('t') == 'CodeBlock':
        return 'mermaid' in node['c'][0][1]
    return any(contains_diagram(child) for child in node.values())


def render_blocks(blocks, document, output, figure_outputs, tex_escape):
    """Replace visual source blocks in Pandoc's AST before the normal conversion."""
    rendered, active, awaiting_title, number = [], False, False, 0
    raw = lambda text: {'t': 'RawBlock', 'c': ['latex', text]}
    for block in blocks:
        kind, content = block['t'], block.get('c')
        if kind != 'CodeBlock' and contains_diagram(block):
            raise ValueError(f'{document}: Mermaid fences must be top-level blocks')
        html = content[1].strip() if kind == 'RawBlock' and content[0] == 'html' else ''
        if html == OPEN_EXAMPLE:
            if active:
                raise ValueError(f'{document}: nested worked example')
            active, awaiting_title = True, True
            continue
        if html == CLOSE_EXAMPLE:
            if not active or awaiting_title:
                raise ValueError(f'{document}: unmatched or empty worked example')
            rendered.append(raw(r'\end{manualexample}'))
            active = False
            continue
        if awaiting_title:
            if kind != 'Para' or len(content) != 1 or content[0]['t'] != 'Strong':
                raise ValueError(f'{document}: expected a bold Worked example title')
            title = inline_text(content[0]['c'])
            if not title.startswith('Worked example: '):
                raise ValueError(f'{document}: expected Worked example: Title')
            rendered.append(raw(r'\begin{manualexample}{' + tex_escape(title.removeprefix('Worked example: ')) + '}'))
            awaiting_title = False
            continue
        if kind == 'CodeBlock' and 'mermaid' in content[0][1]:
            number += 1
            name = diagram_name(document, number)
            target = output / name
            target.parent.mkdir(parents=True, exist_ok=True)
            try:
                subprocess.run(['dot', '-Tpdf', '-o', str(target)],
                               input=graphviz_source(content[1]), text=True, check=True, capture_output=True)
            except FileNotFoundError as error:
                raise RuntimeError('Model diagrams require Graphviz: install the dot command; see manual/BUILD.md') from error
            figure_outputs[name] = hashlib.sha256(target.read_bytes()).hexdigest()
            rendered.append(raw(r'\begin{center}\includegraphics[width=0.98\linewidth,height=0.62\textheight,keepaspectratio]{'
                                + name + r'}\end{center}'))
        else:
            rendered.append(block)
    if active:
        raise ValueError(f'{document}: unclosed worked example')
    return rendered
