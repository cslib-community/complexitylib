#!/usr/bin/env python3
"""Deduplicate retrieved public evidence and separate lexical triage from curated case meanings."""
import collections,csv,hashlib,json,pathlib,re
P=pathlib.Path(__file__).resolve().parent;OLD=P.parent/'current-5bffdf'
def load(n):return json.loads((P/n).read_text())
def save(n,x):(P/n).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
all_records=[]
for item in load('github-corpus.json'):
 for r in item['records']:all_records.append({**r,'source_surface':'GitHub issue/PR body or issue comment','issue_title':item['title']})
all_records += [{**r,'source_surface':'GitHub PR review'} for r in load('pr-review-corpus.json')]
all_records += [{**r,'source_surface':'GitHub repository-wide inline review'} for r in load('inline-review-corpus.json')]
for r in json.loads((OLD/'historical-comment-corpus.json').read_text()):
 if r['status']=='fetched':all_records.append({**r,'source_surface':'retained132-comment corpus'})
for name in ['liupass-current-facts.json','liupass-supplier-facts.json']:all_records.append({**load(name),'source_surface':'explicit current LiuPass follow-up'})
unique={}
for r in all_records:
 b=r['body'];assert hashlib.sha256(b.encode()).hexdigest()==r['body_sha256']
 key=r['url']+'@'+r['body_sha256'];entry=unique.setdefault(key,{**r,'snapshot_id':key,'source_surfaces':[]});entry['source_surfaces'].append(r['source_surface'])
kw=re.compile(r'polytime|fun_prop|\bppt\b|\baesop\b|heartbeat|maxSteps|timeout|timed.out|encoding|rule[ -]order|(?:manual|explicit).{0,40}(?:compos|proof)|proof.{0,20}replac|regression',re.I)
fail=re.compile(r'timeout|timed.out|exhaust|panic|crash|unknown.constant|\bfail(?:s|ed|ure)?\b|regress',re.I)
perf=re.compile(r'profil|slow|cost|heartbeats?|maxSteps|seconds|\bHB\b',re.I)
routine=re.compile(r'(?:simplif|refactor|boilerplate|plumbing|redundant|duplicate)',re.I)
for r in unique.values():
 paragraphs=[x for x in r['body'].split('\n\n') if kw.search(x)];r['matching_paragraphs']=paragraphs
 r['lexical_triage']=[]
 if any(fail.search(x) for x in paragraphs):r['lexical_triage'].append('reported-failure/regression-wording candidate')
 if any(perf.search(x) for x in paragraphs):r['lexical_triage'].append('performance/budget-wording candidate')
 if any(routine.search(x) for x in paragraphs):r['lexical_triage'].append('cleanup/routine-composition-wording candidate')
 if not r['lexical_triage']:r['lexical_triage']=['other keyword/context candidate' if paragraphs else 'retrieved context without target keywords']
 r['semantic_qualification']='Triage is lexical. Actual claims/causes/status are assigned only in curated-cases.json; routine composition is not inferred to be a workaround.'
save('deduplicated-evidence.json',sorted(unique.values(),key=lambda r:r['snapshot_id']))
cases=json.loads((OLD/'regression-index.json').read_text())['records']
# Cases below were read as reports, not inferred from nearby source changes.
def case(id,title,kind,status,claim,urls,causal='No causal claim beyond the cited reported comparison.',extra=None):
 d={'id':id,'case':title,'semantic_classification':kind,'current_disposition':status,'reported_claim':claim,'causal_scope':causal,'sources':[{'url':u} for u in urls],'current_pin_measurement_by_this_worker':None}
 if extra:d.update(extra)
 cases.append(d)
case('routine-counting-composition','AWPP/SBP explicit-plumbing cleanup','routine proof simplification, not reported automation failure','historical cleanup; no current timing inferred',
 '#71/#74 deliberately replace six hand-written composition certificates with existing fun_prop, remove redundant aliases, and report no material module-level regression. Explicit comp in the old source is not evidence of a workaround.',
 ['https://github.com/cslib-community/complexitylib/issues/71','https://github.com/cslib-community/complexitylib/pull/74'])
case('local-call-matcher-cost','Repeated local-call matching','reported performance bottleneck/optimization, not baseline-pass/new-fail regression','historical #267/#287 benchmark context; costs not transferred to5bff',
 'Repeated applicability scans/reduce/isDefEq were reported up to nine times per goal. #287 reports a twelve-file before/after total and tradeoffs; these are historical whole-module costs, not current per-call coverage.',
 ['https://github.com/cslib-community/complexitylib/issues/267','https://github.com/cslib-community/complexitylib/pull/287'])
case('plain-tidy-mixed-failure','WPP mixed plain/tidy and verifier routes','reported slow rejection plus capability gaps','historical documented bounded/conversion workaround; not a new global transition or current all-cases guarantee',
 '#558 identifies WPP default-fun_prop slow failure, verifier conversion plumbing and two missing composite routes. #567 reports verifier rules and a bounded32-step attempt followed by explicit supplied-fact conversion succeeding under2k; default failure used20k. This is a motivated workaround because the source explicitly reports it, not because .tidy/.comp occurs.',
 ['https://github.com/cslib-community/complexitylib/issues/558','https://github.com/cslib-community/complexitylib/pull/567'])
case('zero-knowledge-map-search','ZeroKnowledge three slow PPT searches','reported slow positive search and explicit composition replacement','historical test rewrite; exact ppt goal-shape coverage was explicitly lost',
 '#648 reports three ppt searches with an existing hrun replaced by hrun.map(by fun_prop). It explicitly preserves theorem/nonvacuity/runtime checks but admits loss of ppt coverage of that shape. Its reported92.7M heartbeat unit is retained as authored, not silently normalized to user heartbeats or pooled with current events.',
 ['https://github.com/cslib-community/complexitylib/pull/648'])
case('graph-complement-membership','Guide graph-complement membership','reported capability gap, not proved historical rule-order regression','reported provider repair #612; current per-call outcome not remeasured here',
 '#612 says the natural complement defeated both tactics at list membership and required an eight-line Boolean rewrite before generic negation/membership rules. It documents the specific missing subterm rather than merely manual syntax.',
 ['https://github.com/cslib-community/complexitylib/pull/612'])
case('binary-entry-import','Binary division/list-length entry point','reported missing import/provider scope','historical #627/#685 support; no blanket current encoding inference claim',
 '#627 reports binary division/mod/testBit certificates already existed but were absent from Tactic.PolyTime imports; binary list length required unary-to-binary composition. This is a documented entry-point/capability gap, distinct from rule-order causality.',
 ['https://github.com/cslib-community/complexitylib/issues/627','https://github.com/cslib-community/complexitylib/pull/685'])
case('plain-driver-selection','Plain versus raw driver selection','reported frontend capability failure','historical #728 repair; current strict backend evolved afterward',
 'Plain AND and checkedConstant passed fun_prop but failed polytime because selection/indexing and an early bridge prevented the plain path; #728 documents predicate-sensitive dispatch and named-key lookup controls.',
 ['https://github.com/cslib-community/complexitylib/pull/728'])
case('certificate-predicate-diagnostic','Unsupported program_certificate predicate','reported missing diagnostic, not a missing mathematics theorem','historical #756/#766 guard repair',
 'An unrelated predicate could be silently registered as an inert certificate. The repair rejects unsupported forms and checks actual Signature/MAC projection keys and named-only opaque contracts. This is not ordinary composition being a workaround.',
 ['https://github.com/cslib-community/complexitylib/issues/756','https://github.com/cslib-community/complexitylib/pull/766'])
case('plain-pure-provider-context','Plain pure-PPT registration/provider context','reported original-source regression with corrected causal A/B','historical #813 integration repaired by library-only #811+#823 context',
 'Fresh original GMWPointwise/OraclePPT failed at an old prefix when the plain function route was used. #813 explicitly corrects causality: missing ordinary encoding/projection providers were sufficient; removing the raw rule alone was not a fix, and BEq was not required. Do not revive the rejected initial registration-only explanation.',
 ['https://github.com/cslib-community/complexitylib/pull/813','https://github.com/cslib-community/complexitylib/pull/813#issuecomment-6386870517'])
case('private-registry-recurrence','Unavailable private fun_prop rules','reported module-import failure, with recurrence','#1037 reports an earlier fix; broader #1205 is in final5bff source',
 '#1037 reports OneWayToSignature leaked private rules into importers; #1205 repairs36 private registrations across five modules and checks all four imported registries including lazy entries. These are related failure-family occurrences, not automatically one root-cause event or a timing regression.',
 ['https://github.com/cslib-community/complexitylib/pull/1037','https://github.com/cslib-community/complexitylib/pull/1205'])
case('bitonic-budget-override','Bitonic ZeroOne proof enumeration budget','actual historical elaboration-budget raise; not polytime search evidence','2M heartbeat/10k recursion overrides removed by #349',
 'The main diff introduces then removes2,000,000 heartbeats/10,000 recursion for bool_min_bitonic enumeration. #337/#349 explain replacing brute-force enumeration by six inequalities/default-budget proof. It is mathematics-proof elaboration rather than a certificate-search regression.',
 ['https://github.com/cslib-community/complexitylib/issues/337','https://github.com/cslib-community/complexitylib/pull/349'])
case('routines-budget-override','Nondeterministic query-machine routines budget','actual historical elaboration-budget raise, removed','1.6M override removed by #911; absent current source',
 'The pinned main transitions introduce1,600,000 heartbeats for framed callback assembly normalizing eight space budgets, then #911 removes the obsolete override after default-budget elaboration. No source clock/model bound or automatic-search necessity is inferred.',
 ['https://github.com/cslib-community/complexitylib/pull/911'])
case('liupass-current-negative','LiuPass original threshold and full rejection','verified reported current positive timeout; partial provider remedy; OPEN default negative/universe gap','OPEN at pinned5bff; PR1215 is separate unmerged supplier evidence, not a pin advance',
 'Worker559 reports original unfold thresholdValue; fun_prop/default200k times out at both d7d and5bff. Three computed unary add/sub/mul rules make the exact original positive and complete supplied-leaf positive pass, but the full missing-leaf default and configured256-step negatives still whnf-time out. Three-operation smaller missing-left/right controls pass. Type* frontend attempt meets existing shared-universe composition limitation; successful diagnostic uses Type. No failing positive is blessed as a negative and no limit is raised.',
 ['https://github.com/cslib-community/complexitylib/issues/1155#issuecomment-6424349736','https://github.com/cslib-community/complexitylib/issues/1155#issuecomment-6424639637','https://github.com/cslib-community/complexitylib/pull/1215'],
 causal='Trace reports binary intermediate exploration before outer unary constraint; no unsupported attribute-erasure A/B was run and no unique registration/order cause is asserted.',
 extra={'formula':'let m := n + γ * Nat.log 2 n - c; m - (2 * Nat.log 2 n + 3) - d * (Nat.log 2 m + 1)','prototype_evidence':'7c2a9fdb5d5de8c745476c8e0f3b0649e788b45f','supplier_head_reported':'a9e2b3fe'})
# Keep each source report once by semantic case ID, preserving the earlier16 records unchanged.
assert len({c['id'] for c in cases})==len(cases)
save('curated-cases.json',{'source_pin':'5bffdf2f248bbbfddea6039ee25a953616dff15b','cases':cases,'qualification':'Case groups are not additive counts of regressions. Earlier curated cases can overlap later occurrences/families; citations and exact dated contexts distinguish them.'})
# Resolve citation availability, without silently calling uncollected text verified.
byurl=collections.defaultdict(list)
for r in unique.values():byurl[r['url']].append(r['snapshot_id'])
links=[]
for c in cases:
 for source in c.get('sources',[]):
  u=source['url'];links.append({'case_id':c['id'],'url':u,'retrieved_snapshots':byurl.get(u,[]),'status':'body-pinned' if u in byurl else 'immutable/external/reference-only; not silently treated as fetched'})
save('case-source-links.json',links)
summary={'retrieved_records_before_dedup':len(all_records),'distinct_URL_body_snapshots':len(unique),'distinct_URLs':len({r['url'] for r in unique.values()}),'matching_keyword_snapshots':sum(bool(r['matching_paragraphs']) for r in unique.values()),'lexical_triage_counts':dict(collections.Counter(k for r in unique.values() for k in r['lexical_triage'])),'curated_case_groups':len(cases),'case_group_count_is_regression_count':False,'unresolved_examples':['global automatic binary addition','original LiuPass full missing-leaf default and256-step rejection','Type* captured arithmetic universe coverage','current all-call runtime and rules/reachability collection'],'no_Lean_or_new_timing':True}
save('classification-summary.json',summary);print(json.dumps(summary,indent=2))
