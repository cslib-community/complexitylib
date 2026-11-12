# Lean source history dashboard

The daily **API documentation** workflow publishes this static site at
<https://www.cslib.io/cslib-frontier/stats/> in the same Pages upload as the API and guide.
It also runs on `workflow_dispatch`; only runs on `main` deploy. No separate Pages deployment
or scheduled commit bot is needed. A failed statistics build fails that docs run rather than
silently publishing stale data.

From the repository root, with Python 3.11+ and full Git history:

```sh
bash tools/stats/install-tokei.sh /tmp/frontier-tokei
python3 tools/stats/build.py --tokei /tmp/frontier-tokei/tokei
python3 -m unittest discover -s tools/stats -p 'test_*.py'
node tools/stats/test_dashboard.cjs
```

The installer pins the Linux x86-64 musl Tokei 12.1.2 release and verifies its archive SHA-256.
For other platforms supply a Tokei 12.1.2 executable with `--tokei`. This version supports Lean;
newer releases currently have no equivalent release binary. Upgrade deliberately, updating the
installer, version check, and regression counts together.

`_site/` contains the page, chart code, CSS, `data.json` and `data.csv`. Serve these together
through a static host (opening `index.html` via `file:` cannot fetch JSON in many browsers).
`--output`, `--cache`, `--repo`, `--ref`, and `--until YYYY-MM-DD` support independent builds.
The dashboard uses no remote JavaScript, fonts or chart libraries. Its table and CSV provide
exact values; controls select a measure and category subset. Summary cards always show totals.

## Counting contract

Each UTC date selects the latest first-parent ancestor, by ancestry order, with committer time
before the following midnight. Quiet days repeat the last eligible commit. Today is partial;
merge history is counted only when it reaches the selected branch. Commit-clock skew is handled
by testing each ancestor's timestamp without assuming monotonic timestamps. A shallow clone is
rejected. Nothing is inferred about history before the repository's first recorded commit.

Only tracked regular `.lean` files in `git archive` are scanned, not symlinks, submodules,
dependencies, working-tree changes or generated untracked outputs. Tracked generated Lean files
are included. Tokei distinguishes code, comments and blanks (a mixed code/comment line follows
Tokei's code classification). Every Lean file belongs to exactly one category in `config.json`;
first matching category wins and exactly one fallback is required. Rename-era roots share their
category. These are source-volume metrics, not counts of results or measures of quality.

Counts are cached by commit SHA under a fingerprint of generator source, config and Tokei
version. The Actions cache reuses previous counts; new commits are counted once, and cache loss
simply rebuilds the history. Output JSON records the selected head, each snapshot's commit,
generation time, category config and tool version. Data is regenerated, not committed.
