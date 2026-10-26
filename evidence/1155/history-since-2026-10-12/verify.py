#!/usr/bin/env python3
"""Validate captured history evidence without network, Lean or cache access."""
import collections,hashlib,json,pathlib,re
P=pathlib.Path(__file__).resolve().parent
load=lambda n:json.loads((P/n).read_text())
pages=load('search-pages.json');assert len({p['query'] for p in pages})==16
for p in pages:assert not p.get('error') and not p.get('incomplete_results') and p['total_count']<=1000 and len(p['numbers'])==p['returned']
for q in {p['query'] for p in pages}:
 group=[p for p in pages if p['query']==q];assert sum(p['returned'] for p in group)>=group[-1]['total_count']
corpus=load('github-corpus.json');assert len(corpus)==648;assert len({x['number'] for x in corpus})==648
for x in corpus:
 for r in x['records']:
  assert hashlib.sha256(r['body'].encode()).hexdigest()==r['body_sha256']
  if r['kind']=='comment':assert max(r['created_at'],r['updated_at'])>='2026-10-12T00:00:00Z'
records=load('deduplicated-evidence.json');keys=[]
for r in records:
 assert hashlib.sha256(r['body'].encode()).hexdigest()==r['body_sha256'];keys.append(r['url']+'@'+r['body_sha256'])
assert len(keys)==len(set(keys))
old=json.loads((P.parent/'current-5bffdf/regression-index.json').read_text())['records'];cases=load('curated-cases.json')['cases'];assert {r['id'] for r in old}<={r['id'] for r in cases}
liu=next(r for r in cases if r['id']=='liupass-current-negative');assert 'OPEN' in liu['current_disposition'];assert 'still' in liu['reported_claim'] and '256' in liu['reported_claim']
summary=load('main-diff-summary.json');assert summary['all_first_parent_commits_scanned']==1344;assert summary['commits_with_matching_Lean_diff_hunks']==len(load('main-diff-index.json'))
budgets=[h for r in load('main-diff-index.json') for h in r['matching_hunks'] if h['budget_directive_delta']];assert len(budgets)==14
for value in ['1600000','2000000']:
 assert any(any(l.startswith('+set_option maxHeartbeats '+value) for l in h['lines']) for h in budgets)
 assert any(any(l.startswith('-set_option maxHeartbeats '+value) for l in h['lines']) for h in budgets)
reviews=load('review-retrieval-manifest.json');assert not reviews['errors'];assert reviews['recovered_errors'][0]['number']==240
assert load('classification-summary.json')['no_Lean_or_new_timing']
print('PASS: sixteen complete query page chains;648 threads/body hashes/date boundaries; exact URL/body dedup; retained16 prior case IDs; OPEN LiuPass rejection;1344 main transitions/14 budget hunks with both historical raises and removals; targeted network recovery; no invented runtime fields.')
