#!/usr/bin/env python3
"""Validates: plotted history and observation intervals equal the exported data.

Creates optional standalone SVG and PNG files. Requires matplotlib. Git history
includes imported work; observation spans do not imply continuous log coverage.
"""
import argparse
import datetime as dt
import json
import os
import tempfile
from pathlib import Path
from git_history import REVISION

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / '_generated/development-history/data'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-dir', type=Path, default=DATA, help='Directory containing extracted Git and private-session summaries')
    parser.add_argument('--census-dir', type=Path, default=ROOT / '_generated/data')
    parser.add_argument('--output', type=Path, default=ROOT / '_generated/development-history/figures')
    parser.add_argument('--data-only', action='store_true', help='Recompute plotted data using only the standard library')
    args = parser.parse_args()
    daily = json.loads((args.data_dir / 'git_daily.json').read_text())
    codex = json.loads((args.data_dir / 'session_summary.json').read_text())
    claude = json.loads((args.data_dir / 'claude_summary.json').read_text())
    git = json.loads((args.data_dir / 'git_summary.json').read_text())
    census = json.loads((args.census_dir / 'source_census.json').read_text())
    if git['revision'] != REVISION or census['revision'] != REVISION:
        raise ValueError('Git and census data must describe the fixed historical revision')
    running = 0
    rows = []
    for day, record in sorted(daily.items()):
        running += record['library_added'] - record['library_deleted']
        rows.append({'date': day, 'library_lines': running,
                     'first_parent_commits': record['first_parent_commits']})
    assert running == census['library_physical_lines']
    assert sum(r['first_parent_commits'] for r in rows) == git['first_parent_commits']
    intervals = [
        {'label': 'Git integration history', 'start': git['first_committer_time'],
         'end': git['snapshot_committer_time']},
        {'label': 'Local Codex records',
         'start': codex['cohorts']['current_checkout_identity']['earliest_start'],
         'end': codex['cohorts']['current_checkout_identity']['latest_observed']},
        {'label': 'Local Claude records',
         'start': claude['cohorts']['current_checkout_identity']['earliest_record'],
         'end': claude['cohorts']['current_checkout_identity']['latest_record']},
    ]
    args.output.mkdir(parents=True, exist_ok=True)
    output_data = {'revision': git['revision'], 'timezone': 'UTC', 'daily': rows,
                   'intervals': intervals,
                   'meaning': 'Current-checkout identity only. Intervals join first and last observed records, not continuous coverage. Physical lines include imports and refactors.'}
    (args.output / 'history-data.json').write_text(json.dumps(output_data, indent=2) + '\n')

    if args.data_only:
        print(json.dumps({'status': 'pass', 'daily_rows': len(rows), 'library_lines': running}))
        return

    with tempfile.TemporaryDirectory(prefix='complexitylib-history-mpl-') as config:
        os.environ['MPLCONFIGDIR'] = config
        import matplotlib
        matplotlib.use('Agg')
        import matplotlib.dates as mdates
        import matplotlib.pyplot as plt
        from matplotlib.ticker import FuncFormatter
        plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 10,
                             'svg.hashsalt': 'complexitylib-13e6a319'})
        dates = [dt.datetime.fromisoformat(r['date']).replace(tzinfo=dt.timezone.utc) for r in rows]
        parse = lambda x: dt.datetime.fromisoformat(x.replace('Z', '+00:00'))
        fig, axes = plt.subplots(3, 1, figsize=(10, 8), sharex=True,
                                 gridspec_kw={'height_ratios': [2, 1.5, 1.45]})
        fig.subplots_adjust(left=.20, right=.97, top=.88, bottom=.22, hspace=.38)
        fig.suptitle('Complexitylib: integration history and available local records',
                     x=.05, ha='left', y=.97, fontsize=14, fontweight='bold')
        fig.text(.05, .927, 'Source snapshot 13e6a319 · all dates UTC · current-checkout identity cohort', color='#46505c')
        axes[0].plot(dates, [r['library_lines'] for r in rows], color='#243c5a', lw=2, marker='o', ms=3)
        axes[0].yaxis.set_major_formatter(FuncFormatter(lambda value, _: f'{value / 1e6:.1f}M'))
        axes[0].set_ylabel('Library physical lines')
        axes[0].set_ylim(0, 1200000)
        axes[0].annotate(f'{running:,}', (dates[-1], rows[-1]['library_lines']), xytext=(-6, 8),
                         textcoords='offset points', ha='right', fontsize=9)
        axes[1].bar(dates, [r['first_parent_commits'] for r in rows], width=.7, color='#317b83')
        axes[1].set_ylabel('First-parent commits')
        axes[1].set_ylim(0, 250)
        axes[1].annotate('Nov 2 is partial', (dates[-1], rows[-1]['first_parent_commits']),
                         xytext=(-8, 15), textcoords='offset points', ha='right', fontsize=9)
        colors = ['#243c5a', '#317b83', '#a76728']
        for y, (record, color) in enumerate(zip(intervals, colors)):
            axes[2].plot([parse(record['start']), parse(record['end'])], [2-y, 2-y],
                         color=color, lw=5, marker='|', ms=12, solid_capstyle='butt')
        axes[2].set_yticks([2, 1, 0], [r['label'] for r in intervals])
        axes[2].set_ylim(-.6, 2.6)
        axes[2].set_xlim(parse('2026-10-12T12:00:00Z'), parse('2026-11-02T12:00:00Z'))
        axes[2].xaxis.set_major_locator(mdates.DayLocator(interval=3, tz=dt.timezone.utc))
        axes[2].xaxis.set_major_formatter(mdates.DateFormatter('%b %d', tz=dt.timezone.utc))
        for axis in axes:
            axis.spines[['top', 'right']].set_visible(False)
            axis.grid(axis='y', alpha=.16)
            axis.set_axisbelow(True)
        fig.text(.05, .085,
                 'Line counts include imported work, proof plumbing and refactors; they do not measure new mathematics.\n'
                 'Bars in the last panel join first and last observations, not continuous transcript coverage.\n'
                 'Claude path identity predates this Git root; desktop records remain unavailable.',
                 fontsize=9, linespacing=1.5, color='#46505c')
        fig.savefig(args.output / 'history.svg', metadata={'Date': None})
        fig.savefig(args.output / 'history.png', dpi=180, metadata={'Software': 'Complexitylib dossier plot_history.py'})
        plt.close(fig)
    print(json.dumps({'output': str(args.output), 'daily_rows': len(rows),
                      'library_lines': running, 'first_parent_commits': git['first_parent_commits']}))


if __name__ == '__main__':
    main()
