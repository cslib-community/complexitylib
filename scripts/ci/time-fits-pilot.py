"""Temporary hosted-only measurement for #5469; never merge this scratch PR."""
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import time
import tomllib

BASE = '9af08c2a55f93b996fe744c2056a86133b07cdab'
HEAD = '392091a58706cd3c47913d1eb18dc4edd9c82e42'
FILES = [
    'CslibFrontier/Algorithms/WordRAM/ExactTriangle/RecordProduct/Decode.lean',
    'CslibFrontier/Algorithms/WordRAM/ThreeSum/ChanHe/TraversalLocalDelivery.lean',
]
OUT = Path(os.environ['RUNNER_TEMP']) / 'fits-pilot-timings'
OUT.mkdir(parents=True, exist_ok=True)

def run(args, **kwargs):
    print('+', ' '.join(map(str, args)), flush=True)
    return subprocess.run(args, check=True, **kwargs)

# Only the hosted runner's disposable checkout is modified. Keep the harness alive.
for config in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
    assert subprocess.check_output(['git', 'show', f'{BASE}:{config}']) == subprocess.check_output(['git', 'show', f'{HEAD}:{config}'])
run(['git', 'restore', '--source', BASE, '--', 'CslibFrontier', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'])
run(['scripts/cache/ensure.sh'])
# setup-file builds imports only, outside measurements; retain its full module setup,
# including imported module artifacts and exported options, for both source variants.
setups = {}
for f in FILES:
    setup = OUT / (Path(f).stem + '.setup.json')
    result = run(['lake', 'setup-file', f], capture_output=True, text=True)
    print(result.stderr, flush=True)
    json.loads(result.stdout)  # fail rather than time a malformed setup
    setup.write_text(result.stdout)
    setups[f] = setup
# Match the root package's strong AND weak Lean options. No heartbeat overrides.
config = tomllib.loads(Path('lakefile.toml').read_text())
options = config['leanOptions']
flags = []
def flatten(table, prefix=''):
    for name, value in table.items():
        key = f'{prefix}.{name}' if prefix else name
        if isinstance(value, dict):
            yield from flatten(value, key)
        else:
            yield key.removeprefix('weak.'), value

for name, value in flatten(options):
    flags.append(f'-D{name}={str(value).lower()}')
metadata = {'baseline': BASE, 'changed': HEAD, 'files': FILES, 'flags': flags,
            'cpu': Path('/proc/cpuinfo').read_text(), 'runner': dict((k, v) for k, v in os.environ.items() if k.startswith('RUNNER_')),
            'warmups_per_variant': 1, 'measured_repetitions': 5,
            'limits': '900 seconds per elaboration; default/source heartbeat settings unchanged; wall time includes Lean startup/import/output, excludes Lake setup and builds'}
(OUT / 'metadata.json').write_text(json.dumps(metadata, indent=2))
rows = []
for f in FILES:
    original_imports = [line for line in Path(f).read_text().splitlines() if 'import ' in line]
    for rep in range(6):
        order = [('before', BASE), ('after', HEAD)]
        if rep % 2:
            order.reverse()
        for label, sha in order:
            source = subprocess.check_output(['git', 'show', f'{sha}:{f}'])
            Path(f).write_bytes(source)
            assert [line for line in source.decode().splitlines() if 'import ' in line] == original_imports
            dest = OUT / f'{Path(f).stem}-{label}-{rep}'
            dest.mkdir()
            cmd = ['lake', 'env', 'lean', '--setup', str(setups[f]), *flags,
                   '-o', str(dest / 'result.olean'), '-i', str(dest / 'result.ilean'), f]
            print(f'MEASURING {f} {label} rep={rep} warmup={rep == 0}', flush=True)
            started = time.perf_counter()
            with (dest / 'lean.log').open('w') as log:
                result = subprocess.run(cmd, stdout=log, stderr=subprocess.STDOUT, timeout=900)
            elapsed = time.perf_counter() - started
            row = dict(file=f, variant=label, commit=sha, repetition=rep, warmup=rep == 0,
                       seconds=elapsed, returncode=result.returncode, source_sha256=hashlib.sha256(source).hexdigest(), command=cmd)
            rows.append(row)
            (OUT / 'results.json').write_text(json.dumps(rows, indent=2))
            print(json.dumps(row), flush=True)
            if result.returncode:
                print((dest / 'lean.log').read_text(), flush=True)
                raise SystemExit(result.returncode)
summary = ['Exact pilot timings (seconds; five repetitions after one warmup per variant).', '']
for f in FILES:
    a = [r['seconds'] for r in rows if r['file'] == f and r['variant'] == 'before' and not r['warmup']]
    b = [r['seconds'] for r in rows if r['file'] == f and r['variant'] == 'after' and not r['warmup']]
    summary.append(f'{f}: before={a}; after={b}; medians={statistics.median(a):.3f}/{statistics.median(b):.3f}; ratio={statistics.median(b)/statistics.median(a):.4f}')
text = '\n'.join(summary) + '\n'
print(text)
(OUT / 'summary.txt').write_text(text)
with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as report:
    report.write(text)
