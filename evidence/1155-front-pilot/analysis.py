import json, sys
R=[json.loads(l) for l in open(sys.argv[1])]
ok=[r for r in R if r['today_ok']]
def med(xs): xs=sorted(xs); return xs[len(xs)//2]
islib=lambda r: r['file'].split('/')[-1].startswith('CslibFrontier_')
print(f"calls={len(R)} today-successful={len(ok)}")
for name,rows in [('library',[r for r in ok if islib(r)]),('tests',[r for r in ok if not islib(r)])]:
    for tac in ['polytime','ppt']:
        X=[r for r in rows if r['tac']==tac]
        print(f"{name:8} {tac:8} n={len(X):3} today p50={med([r['today_hb'] for r in X]):6} memo p50={med([r['memo'] for r in X]):6} prebuilt-memo p50={med([r['today_warm_hb'] for r in X]):6} front closes {sum(r['front_ok'] for r in X)}/{len(X)}")
for tac in ['polytime','ppt']:
    X=[r for r in ok if r['tac']==tac]
    t=sum(r['today_hb'] for r in X); w=sum(r['today_warm_hb'] for r in X)
    print(f"{tac}: total today={t} prebuilt-memo={w} ({100*(w-t)/t:+.0f}%)")
    for C in [1000,2000,None]:
        proj=0
        for r in X:
            cap = C if C else 10**12
            if r['front_ok'] and r['front_hb']<=cap: proj+=r['front_hb']
            else: proj+=min(r['front_hb'],cap)+r['today_warm_hb']
        print(f"   front then fallback, prebuilt memo, front cap={C}: {proj} ({100*(proj-w)/w:+.1f}% vs prebuilt-memo today)")
