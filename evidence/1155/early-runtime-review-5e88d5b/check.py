#!/usr/bin/env python3
"""Independent bounded raw-data sanity check; excludes static census/joins and runs no Lean."""
import collections,hashlib,json,pathlib,subprocess
REV='5e88d5bedc4aa8187298284d09e346f612056b61';ROOT='evidence/1155/current-5bff/early-completed-snapshot/';PIN='5bffdf2f248bbbfddea6039ee25a953616dff15b'
P=pathlib.Path(__file__).resolve().parent
raw=lambda p:subprocess.check_output(['git','show',REV+':'+ROOT+p],cwd=P)
js=lambda p:json.loads(raw(p));sha=lambda b:hashlib.sha256(b).hexdigest()
manifest=js('snapshot-manifest.json');side=js('run-sidecar.json');digest=sha(raw('run-sidecar.json'))
assert side['source_pin']==manifest['source_pin']==PIN
for f in manifest['files']:assert sha(raw(f['path']))==f['sha256'],f['path']
assert len(manifest['files'])==33
# Verify only producer/provenance bytes; no assessment of self-authored static selection/joins.
ref=manifest['plan_source_revision'];prefix='evidence/1155/current-5bff/'
for name,d in side['producer_sources'].items():
 b=subprocess.check_output(['git','show',ref+':'+prefix+'method-v3/'+name],cwd=P);assert sha(b)==d
for field,path in [('collector_sha256','collector/collect.py'),('parser_sha256','collector/parse.py'),('plan_sha256','survey/plan.json'),('headers_sha256','survey/headers.json')]:
 b=subprocess.check_output(['git','show',ref+':'+prefix+path],cwd=P);assert sha(b)==side[field]
commands=js('commands.json');assert len(commands)==12
files=collections.defaultdict(list)
for c in commands:files[c['file_id']].append(c)
assert len(files)==3
seen_events=set();report=[];observations=[]
for file_id,rows in files.items():
 assert {c['mode'] for c in rows}=={'baseline','import-only','measured','traced'}
 base=next(c for c in rows if c['mode']=='baseline');ctx0=base['actual_context'];original=raw('originals/'+base['path'])
 assert original==subprocess.check_output(['git','show',PIN+':'+base['path']],cwd=P)
 per_mode=[]
 for c in rows:
  assert c['returncode']==0 and not c['external_timeout'] and c['run_id']==side['run_id'] and c['provenance']==digest
  variant=raw('variants/'+file_id+'/'+c['mode']+'/'+c['path']);assert sha(variant)==c['source_sha256'];assert sha(original)==c['original_sha256']
  for i in sorted(c['insertions'],key=lambda i:i['original_byte'],reverse=True):
   a=i['original_byte']+sum(j['bytes'] for j in c['insertions'] if j['original_byte']<i['original_byte']);variant=variant[:a]+variant[a+i['bytes']:]
  assert variant==original
  ctx=c['actual_context'];assert ctx['module']==ctx0['module'] and ctx['source_declaration_names']==ctx0['source_declaration_names']
  assert (ctx['directImports'] if c['mode']=='baseline' else ctx['directImports'][:-1])==ctx0['directImports']
  if c['mode']!='baseline':assert ctx['directImports'][-1][0]=='Diag1155.Measure'
  flags=[a for a in c['command'] if a.startswith('-D')]
  normal=[a for a in base['command'] if a.startswith('-D')]
  assert [a for a in flags if not a.startswith('-Dtrace.')]==normal
  if c['mode']!='traced':assert raw('runs/'+file_id+'/'+c['mode']+'.log')==b''
  if c['mode'] in ('baseline','import-only'):continue
  events=[json.loads(l) for l in raw('runs/'+file_id+'/'+c['mode']+'.jsonl').splitlines()];groups=collections.defaultdict(dict);trace_counts=collections.Counter();stack=collections.defaultdict(list);nested=0
  instrumented=raw('variants/'+file_id+'/'+c['mode']+'/'+c['path'])
  for e in events:
   eid=e['event_id']
   if e['phase']=='trace':trace_counts[eid]+=1;continue
   assert e['phase'] in ('begin','end') and e['phase'] not in groups[eid];assert e['run_id']==side['run_id'] and e['provenance']==digest
   groups[eid][e['phase']]=e
   if e['phase']=='begin':
    if stack[e['thread_id']]:nested+=1
    stack[e['thread_id']].append(eid)
   else:assert stack[e['thread_id']].pop()==eid
  assert all(not s for s in stack.values())
  assert set(trace_counts)<=set(groups), 'orphan native trace owner'
  kinds=collections.Counter();heads=collections.Counter();synthetic=0
  for eid,g in groups.items():
   assert eid not in seen_events;seen_events.add(eid);assert set(g)=={'begin','end'}
   b,e=g['begin'],g['end'];assert b['thread_id']==e['thread_id']==e['start_thread_id'] and e['same_thread']
   assert e['status']=='returned' and e['goals_after']==0
   assert type(e['raw_body_thread_heartbeats']) is int and 0<=e['raw_body_thread_heartbeats']<=e['raw_region_thread_heartbeats']
   assert type(e['body_wall_nanoseconds']) is int and e['body_wall_nanoseconds']>=0
   assert b['maxHeartbeats_user']==200000 and b['core_max_raw_heartbeats']==b['maxHeartbeats_user']*1000
   assert 0<=b['remaining_raw_heartbeats']<=b['core_max_raw_heartbeats']
   assert b['filemap_equals_input_file'] and b['local_filemap_source'] is None and b['filemap_bytes']==len(instrumented)
   a,z=b['start'],b['end'];assert instrumented[a:z].decode()==b['text']
   # Invert actual recorded insertions directly; do not use static candidate IDs or guessed extents.
   shift=sum(i['bytes'] for i in c['insertions'] if a>=i['original_byte']+sum(j['bytes'] for j in c['insertions'] if j['original_byte']<i['original_byte'])+i['bytes'])
   assert original[a-shift:z-shift].decode()==b['text']
   assert b['module']==ctx['module'];assert e['trace_entries']==trace_counts[eid]
   kinds[b['kind']]+=1;synthetic+=not b['original_source_info']
   for h in b['goal_heads']:assert h['normalized'] is False;heads[h['head_after_foralls_mdata']]+=1
   observations.append({'file':c['path'],'mode':c['mode'],'event_id':eid,'kind':b['kind'],'original_source_info':b['original_source_info'],'macro_stack_depth':b['macro_stack_depth'],'text':b['text'],'syntactic_goal_heads':b['goal_heads'],'body_raw_heartbeats':e['raw_body_thread_heartbeats'],'body_user_heartbeat_units':e['raw_body_thread_heartbeats']/1000,'qualification':'Inclusive diagnostic body; synthetic/nested/repeated events and traced/untraced modes are not additive source-call costs; no final proof/rule attribution.'})
  per_mode.append({'mode':c['mode'],'attempts':len(groups),'synthetic_source_info':synthetic,'per_thread_nested_attempts':nested,'trace_messages':sum(trace_counts.values()),'kinds':dict(kinds),'raw_syntactic_heads':dict(heads)})
 report.append({'path':base['path'],'whole_commands':4,'all_whole_commands_pass':True,'source_variants_reversible':True,'native_context_names_count':len(ctx0['source_declaration_names']),'modes':per_mode})
result={'reviewed_snapshot':REV,'source_pin':PIN,'scope':'Exactly three frozen completed files; no global647-file coverage/collector approval and no self-authored static census/joins assessment','snapshot_artifact_hashes_checked':33,'whole_commands':12,'all_pass':True,'complete_unique_attempt_pairs':len(seen_events),'file_results':report,'limits':['Raw syntactic heads are unnormalized, not semantic classification of all goals.','Retained native traces are search-attempt evidence, not final winning proof or counts of rules fired.','Thread-local raw heartbeat counts divided by1000 are user units; nanoseconds are not seconds; process wall is shared-host and includes imports.','Diagnostic overhead consumes unchanged command budget; nested/repeated/synthetic and traced/untraced costs are not summed as distinct authored calls.','No Lean/build/cache rerun; compiler digests are not independent recompilation evidence.']}
(P/'result.json').write_text(json.dumps(result,indent=2)+'\n');(P/'observations.json').write_text(json.dumps(observations,indent=2,ensure_ascii=False)+'\n');print(json.dumps(result,indent=2))
