#!/usr/bin/env python3
import json, sys, collections, os
S = os.path.dirname(os.path.abspath(__file__)) + '/m'
def load(label):
    calls = collections.defaultdict(list)
    for l in open(f'{S}/{label}/calls.jsonl'):
        r = json.loads(l)
        f = os.path.basename(r['file']).replace('.lean', '')
        calls[f].append(r)
    files = {}
    for l in open(f'{S}/{label}/files.txt'):
        if l.startswith('DONE'): continue
        name, rest = l.split(' ', 1)
        parts = dict(p.split('=') for p in rest.replace('time=', 'time=').split() if '=' in p)
        t = rest.split('time=')[1].split(' errors=')[0].split()
        files[name.replace('/', '_').replace('.lean', '')] = dict(rc=parts['rc'], wall=float(t[0]), user=float(t[1]), sys=float(t[2]), errors=rest.split('errors=')[1].strip())
    return calls, files
nc, nf = load('new'); oc, of = load('old')
tot = collections.Counter()
print(f"{'file':55} {'calls':>5} {'tactic hb old':>13} {'new':>8} {'wall old':>8} {'new':>6} {'cpu old':>7} {'new':>6} outcome")
for f in sorted(nf):
    if f not in of: continue
    o = oc.get(f, []); n = nc.get(f, [])
    ohb = sum(r['hb'] for r in o); nhb = sum(r['hb'] for r in n)
    same = sorted((r['line'], r['col'], r['ok']) for r in o) == sorted((r['line'], r['col'], r['ok']) for r in n)
    same = same and of[f]['errors'] == nf[f]['errors'] and of[f]['rc'] == nf[f]['rc']
    ocpu = of[f]['user'] + of[f]['sys']; ncpu = nf[f]['user'] + nf[f]['sys']
    lib = not f.startswith('CslibFrontierTests')
    key = 'lib' if lib else 'tests'
    tot[key+'_ohb'] += ohb; tot[key+'_nhb'] += nhb; tot[key+'_ow'] += of[f]['wall']; tot[key+'_nw'] += nf[f]['wall']
    tot[key+'_oc'] += ocpu; tot[key+'_nc'] += ncpu; tot[key+'_calls'] += len(n)
    print(f"{f[:55]:55} {len(n):5} {ohb:13} {nhb:8} {of[f]['wall']:8.1f} {nf[f]['wall']:6.1f} {ocpu:7.1f} {ncpu:6.1f} {'same' if same else 'DIFF'}")
for k in ['tests', 'lib']:
    print(f"TOTAL {k}: calls={tot[k+'_calls']} tactic hb {tot[k+'_ohb']} -> {tot[k+'_nhb']} ({100*(tot[k+'_nhb']-tot[k+'_ohb'])/max(1,tot[k+'_ohb']):+.0f}%), wall {tot[k+'_ow']:.0f}s -> {tot[k+'_nw']:.0f}s, cpu {tot[k+'_oc']:.0f}s -> {tot[k+'_nc']:.0f}s")
