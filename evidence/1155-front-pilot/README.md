# #1155 option-B pilot: measurement (worker jetski-390f-front, #4077)

Source: `main` at `e0d9859df4`. Probe: [`Probe.lean.inc`](Probe.lean.inc), injected after the
import block of a scratch copy of each sampled file by [`inject.py`](inject.py) and run with
`lake env lean` against cached outputs ([`runner.sh`](runner.sh)). It registers a newer elaborator
for the `polytime`/`ppt` syntax, so library files elaborate unchanged except for the measurement.
For every call, from the same saved state, it records (units: maxHeartbeats units, i.e. raw/1000):

- `today_hb`: the current tactic, whose result is committed (so file behavior is unchanged);
- `memo_hb`: `Internal.withPlainRuleMemo (pure ())` alone, i.e. building the per-invocation
  plain-rule classification memo;
- `today_memo_prebuilt_hb`: the current tactic run inside an already-built memo;
- `front_*`: a prototype front end, run inside an already-built memo: shared goal preparation,
  then (a) a local fact whose conclusion determines all arguments, (a') registered
  `program_certificate`s keyed on the goal head with premises solved recursively by the front end
  only (no Aesop), (b) one `funPropWithPlainBoundary 64` call (`fun_prop (maxSteps := 64)` for
  tidy goals). Oracle `ppt` goals are skipped (today's path is already `fun_prop`).

Sample: 372 calls in 33 files (12 library modules in Crypto and Complexity, 21 test modules
including the Automation/PPT/PolyTime regression files). Per-call data: [`calls.csv`](calls.csv);
summarizer: [`summarize.py`](summarize.py), [`analysis.txt`](analysis.txt).

Caveats: inclusive heartbeats of one thread, not wall time; phases run sequentially in one
process so later phases may benefit from environment-level caches (the import-closure thunk is
paid by the first `memo` measurement of each file); ~20 hinted calls (`polytime [f]`) in the
first batch ran the front end without the hint. A few declarations exceeded their budget after
the probe's extra work; the calls themselves were recorded.
