#!/usr/bin/env python3
"""Independent derived/raw event and bounded rule-occurrence checks; excludes static joins."""
import collections,csv,gzip,hashlib,io,json,pathlib,re,subprocess
P=pathlib.Path(__file__).resolve().parent;REV='c41194730ceb87aeb52641c7a5f90846a140187d';D='evidence/1155/current-5bff/survey-default/'
def raw(p):return subprocess.check_output(['git','show',REV+':'+D+p],cwd=P.parents[2])
def js(p):return json.loads(raw(p))
commands=js('commands.json');grid={(c['path'],c['mode']):c for c in commands};raw_events={};raw_traces=[]
for c in commands:
 if c['mode'] not in ('measured','traced'):continue
 for line in raw('runs/'+c['file_id']+'/'+c['mode']+'.jsonl').splitlines():
  e=json.loads(line)
  if e['phase']=='trace':raw_traces.append(e);continue
  if e['phase']=='unsupported_dispatch':continue
  g=raw_events.setdefault(e['event_id'],{});assert e['phase'] not in g;g[e['phase']]=e
attempts=js('attempts.json');byevent={a['event_id']:a for a in attempts};assert len(byevent)==len(attempts)==len(raw_events)==9822;assert set(byevent)==set(raw_events)
for eid,a in byevent.items():
 g=raw_events[eid];assert a['begin']==g['begin'];assert a.get('end')==g.get('end')
 if 'end' not in g:assert a['status']=='censored_unknown' and a['raw_body_thread_heartbeats'] is None and not a['accepted_whole_file_cost']
traces=json.loads(gzip.decompress(raw('trace-messages.json.gz')));assert len(traces)==len(raw_traces)==12779
canon=lambda t:hashlib.sha256(json.dumps({k:t[k] for k in ('phase','event_id','message','start','end')},sort_keys=True,ensure_ascii=False).encode()).hexdigest()
assert collections.Counter(map(canon,traces))==collections.Counter(map(canon,raw_traces))
for t in traces:
 a=byevent[t['event_id']];assert t['path']==a['path'] and t['mode']==a['mode']
funprop=re.compile(r'^\s*\[Meta\.Tactic\.fun_prop\].*?\bapplying:\s+(\S+)');aesop=re.compile(r'\b(?:norm|safe|unsafe)\|(?:apply|tactic|forward|cases|constructors|simp|destruct)\|(?:global|local|builtin)\|[^\s,;\])]+')
counts=collections.Counter();owners=collections.defaultdict(set);modes=collections.defaultdict(collections.Counter)
for t in traces:
 for line in t['message'].splitlines():
  entries=[];m=funprop.search(line)
  if m:entries.append(('fun_prop_applying_line',m[1]))
  if '[aesop]' in line:entries.extend(('aesop_rule_key_mention',m[0]) for m in aesop.finditer(line))
  for k in entries:counts[k]+=1;owners[k].add(t['event_id']);modes[k][t['mode']]+=1
rule=js('rule-evidence.json');assert len(rule['top'])==80;assert collections.Counter(r['category'] for r in rule['top'])=={'fun_prop_applying_line':40,'aesop_rule_key_mention':40}
assert rule['all_detected_category_occurrences']=={cat:sum(v for (c,_),v in counts.items() if c==cat) for cat in ('fun_prop_applying_line','aesop_rule_key_mention')}
for cat in ('fun_prop_applying_line','aesop_rule_key_mention'):
 expected=sorted(((k,n) for k,n in counts.items() if k[0]==cat),key=lambda x:(-x[1],x[0][1]))[:40]
 actual=[r for r in rule['top'] if r['category']==cat];assert [(r['printed_key'],r['retained_line_occurrences']) for r in actual]==[(k[1],n) for k,n in expected]
 for row in actual:
  k=(cat,row['printed_key']);assert row['distinct_owner_attempts']==len(owners[k]) and row['occurrence_mode_counts']==dict(modes[k])
  for ex in row['examples']:
   t=traces[ex['trace_message_index']];a=byevent[ex['event_id']];assert t['event_id']==ex['event_id'];assert t['message'].splitlines()[ex['line_index']]==ex['native_line'];assert ex['owner_tactic_status']==a['status'];assert ex['whole_command_returncode']==grid[a['path'],a['mode']]['returncode']
rows=list(csv.DictReader(io.StringIO(raw('attempt-metrics.csv').decode())));assert len(rows)==len(byevent) and len({r['event_id'] for r in rows})==len(rows)
trace_costs=0;failed_mode_eligible=0
for r in rows:
 a=byevent[r['event_id']];b=a['begin'];e=a.get('end') or {};c=grid[a['path'],a['mode']]
 def good(c):return c['returncode']==0 and c['external_warning_acceptance'] and c.get('context_error') is None and c['actual_context'] is not None
 eligible=bool(a['mode']=='measured' and a['static_head_id'] and good(grid[a['path'],'baseline']) and good(grid[a['path'],'import-only']) and good(c) and a['status']=='returned' and e.get('goals_after')==0 and a['raw_body_thread_heartbeats'] is not None)
 # Supplied static mapping is a conditional input, never independently approved here.
 assert (r['primary_returned_closed_goal_cost_eligible']=='True')==eligible
 assert (r['mode_acceptance']=='True')==good(c);assert r['status']==a['status'];assert json.loads(r['goal_heads_json'])==b['goal_heads']
 expected=a['body_user_heartbeat_units'];actual=None if not r['body_user_heartbeat_units'] else float(r['body_user_heartbeat_units']);assert actual==expected
 if a['mode']=='traced':trace_costs+=eligible
 if not good(c):failed_mode_eligible+=eligible;assert not a['accepted_whole_file_cost']
assert trace_costs==failed_mode_eligible==0
result={'revision':REV,'status':'PASS','raw_derived_event_pairs_exact':9822,'raw_derived_trace_record_multiset_exact':12779,'rule_top_rows':80,'category_line_occurrences':rule['all_detected_category_occurrences'],'all_bounded_examples_point_to_exact_raw_native_lines':True,'csv_rows_consistent_with_raw_status_units_heads_and_per_mode_acceptance':len(rows),'traced_or_failed_mode_primary_costs':0,'static_selection_joins_and_mapping_correctness':'EXCLUDED','interpretation':'Retained line occurrences/mentions and owner attempts, not unique engine applications or final-proof dependencies. Native source/head/CSV metadata remains unnormalized; censored exceptions are not successful costs.'}
(P/'table-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
