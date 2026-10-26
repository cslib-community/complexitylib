"""Check the forwarding prototype's real controls; no invented runtime rows."""
import hashlib,json,pathlib
P=pathlib.Path(__file__).resolve().parents[1]/'pilot1155-current-controls-v2'
def need(x,m):
 if not x:raise ValueError(m)
rows=json.loads((P/'results.json').read_text());side=(P/'sidecar.json').read_bytes();digest=hashlib.sha256(side).hexdigest();meta=json.loads(side)
need(meta['source_pin']=='5bffdf2f248bbbfddea6039ee25a953616dff15b','pin')
need([x['mode'] for x in rows]==['baseline','import-only','measured'],'modes')
need(all(x['exit']==0 for x in rows),'whole-command failure')
ctx=json.loads((P/'native-contexts.json').read_text());base=ctx['baseline']
for mode,c in ctx.items():
 need(c['module']==base['module']=='MethodControls','module context')
 need(c['source_declaration_names']==base['source_declaration_names'],'source declarations')
 if mode!='baseline':
  need(c['directImports'][:-1]==base['directImports'],'imports')
  need(c['directImports'][-1][0]=='Diag1155.Measure','diagnostic import')
events=[json.loads(x) for x in (P/'measured.jsonl').read_text().splitlines()];groups={}
for e in events:
 need(e['phase'] in ('begin','end'),'unexpected control record')
 need(e['run_id']==meta['run_id'] and e['provenance']==digest,'provenance')
 need(type(e.get('thread_id')) is int and 0<=e['thread_id']<2**64,'thread')
 g=groups.setdefault(e['event_id'],{});need(e['phase'] not in g,'duplicate phase');g[e['phase']]=e
need(len(groups)==7 and len(events)==14,'attempt count')
failed=[];generated=[];positions={}
source=(P/'baseline/MethodControls.lean').read_bytes();need(hashlib.sha256(source).hexdigest()==meta['source_sha256'],'original hash')
shift=next(x['insertion_bytes'] for x in rows if x['mode']=='measured')
for ident,g in groups.items():
 need(set(g)=={'begin','end'},'censored attempt')
 b,e=g['begin'],g['end'];need(b['thread_id']==e['thread_id'],'attempt owner')
 need(b['maxHeartbeats_user']==200000,'budget')
 need(e['status'] in ('returned','exception'),'unexpected/censored outcome')
 for key in ['raw_body_thread_heartbeats','raw_region_thread_heartbeats','body_wall_nanoseconds']:
  need(type(e[key]) is int and e[key]>=0,'counter')
 need(e['raw_region_thread_heartbeats']>=e['raw_body_thread_heartbeats'],'region counter')
 a,z=b['start']-shift,b['end']-shift
 need(0<=a<z<=len(source) and source[a:z].decode()==b['text'],'full native span')
 if b['original_source_info']:
  need(b['text'].startswith(('polytime','fun_prop','ppt')),'authored keyword')
  positions.setdefault((a,z),[]).append(ident)
 else:generated.append(b)
 if e['status']=='exception':failed.append(b)
 else:need(e['goals_after']==0,'control positive left goals')
need(len(failed)==1 and failed[0]['text']=='fun_prop','caught failure')
need(len(generated)==1 and generated[0]['text']=='diag1155_generated','generated classification')
need(sorted(map(len,positions.values()))==[1,1,1,1,2],'repeated authored site')
# The source quote is not an executed authored site; repeated costs are NOT deduplicated.
need(not any(source[a:z].decode()=='polytime' and b'`(tactic| ' in source[max(0,a-12):a] for a,z in positions),'quote measured')
print(json.dumps({'whole_commands':3,'attempts':7,'ordinary_failure':1,'generated_attempts':1,'distinct_authored_sites_observed':5,'repeated_site_attempts':2,'quoted_target_unexecuted':True,'source_contexts_equal':True,'status':'PASS','no_final_proof_attribution':True},indent=2))
