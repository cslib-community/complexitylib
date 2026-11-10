#!/usr/bin/env python3
import json, sys, statistics as st, collections
rows = []
for p in sys.argv[1:]:
    for l in open(p):
        l = l.strip()
        if not l: continue
        try: rows.append(json.loads(l))
        except Exception as e: print('bad', l[:100], file=sys.stderr)
def pct(xs, q):
    xs = sorted(xs); return xs[min(len(xs)-1, int(q*len(xs)))] if xs else 0
print(f"calls={len(rows)}")
for tac in ['polytime', 'ppt']:
    R = [r for r in rows if r['tac'] == tac]
    if not R: continue
    ok = [r for r in R if r['today_ok']]
    print(f"\n== {tac}: calls={len(R)} today_ok={len(ok)} today_fail={len(R)-len(ok)}")
    stages = collections.Counter(r['front'] if r['front_ok'] else 'FAIL' for r in ok)
    print(' front outcome on today-successful calls:', dict(stages))
    lost = [r for r in R if r['front_ok'] and not r['today_ok']]
    print(' front succeeds where today fails:', len(lost))
    t = [r['today_hb'] for r in ok]
    print(f" today hb (successful): min={min(t)} p50={pct(t,.5)} p90={pct(t,.9)} max={max(t)} sum={sum(t)}")
    w = [r.get('today_warm_hb',0) for r in ok]
    print(f" today hb with memo prebuilt (successful): min={min(w)} p50={pct(w,.5)} p90={pct(w,.9)} sum={sum(w)}")
    memo = [r['memo'] for r in R]
    print(f" memo-only hb: p50={pct(memo,.5)} max={max(memo)}")
    fc = [r for r in ok if r['front_ok']]
    if fc:
        f = [r['front_hb'] for r in fc]; tt = [r['today_hb'] for r in fc]
        print(f" on front-closed calls: front p50={pct(f,.5)} sum={sum(f)} | today p50={pct(tt,.5)} sum={sum(tt)}")
    ff = [r for r in ok if not r['front_ok']]
    if ff:
        f = [r['front_hb'] for r in ff]
        print(f" wasted front cost on fallback calls: p50={pct(f,.5)} max={max(f)} sum={sum(f)}")
    # projected: front closes -> front cost; else front cost + today
    proj = sum(r['front_hb'] if r['front_ok'] else r['front_hb'] + r['today_hb'] for r in ok)
    print(f" projected total (front + fallback) = {proj} vs today {sum(t)}  [front_hb excludes memo; add memo per call: {proj + sum(r['memo'] for r in ok)}]")
    projw = sum(r['front_hb'] if r['front_ok'] else r['front_hb'] + r.get('today_warm_hb',0) for r in ok)
    print(f" memo cached: today {sum(w)} vs front+fallback {projw}")
    tf = [r for r in R if not r['today_ok']]
    if tf:
        print(f" failing calls (negative controls): today hb p50={pct([r['today_hb'] for r in tf],.5)}; front fail msgs:")
        for r in tf[:8]:
            print('   ', r['file'].split('/')[-1], r['line'], 'front_ok=' + str(r['front_ok']), r['front'][:160])
