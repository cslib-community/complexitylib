#!/usr/bin/env python3
"""Bounded independent full-corpus consistency reconciliation; no Lean or static-join approval.

Reads only frozen Git objects. Returned tactic attempts do not imply accepted files or final
proof dependencies. Failures/censored records are preserved and reported, never imputed as zero.
"""
import argparse,collections,gzip,hashlib,json,pathlib,subprocess,tomllib
PIN='5bffdf2f248bbbfddea6039ee25a953616dff15b'
METHOD='e443c8e5112e2a733e065e006fe0164c17e0293d'
RUNNER='31123fbdb047f2fdb8ca31ecec5454434d327133'
BASE='evidence/1155/current-5bff/'
HERE=pathlib.Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('revision');ap.add_argument('--dataset',default=BASE+'survey-default');ap.add_argument('--output',type=pathlib.Path,default=HERE/'result.json');a=ap.parse_args()
 issues=[]
 def need(ok,message):
  if not ok:issues.append(message)
 def obj(path,rev=None):return subprocess.check_output(['git','show',(rev or a.revision)+':'+path],cwd=HERE.parents[2])
 tracked=set(subprocess.check_output(['git','ls-tree','-r','--name-only',a.revision,a.dataset],cwd=HERE.parents[2],text=True).splitlines())
 def raw(rel):return obj(a.dataset+'/'+rel)
 def load(rel):
  path=a.dataset+'/'+rel
  return json.loads(obj(path) if path in tracked else gzip.decompress(obj(path+'.gz')))
 artifact=load('artifact-sha256.json')
 manifested={a.dataset+'/'+f['path'] for f in artifact['files']}
 need(manifested==tracked-{a.dataset+'/artifact-sha256.json'},'artifact manifest file membership')
 for f in artifact['files']:
  content=raw(f['path']);need(len(content)==f['bytes'] and sha(content)==f['sha256'],'artifact hash/size '+f['path'])
 compression=load('compressed-derived-artifact.json');packed=raw(compression['gzip']);unpacked=gzip.decompress(packed)
 need(sha(packed)==compression['gzip_sha256'] and len(unpacked)==compression['uncompressed_bytes'] and sha(unpacked)==compression['uncompressed_sha256'],'lossless derived gzip identity')
 del packed,unpacked
 sidebytes=raw('run-sidecar.json');side=json.loads(sidebytes);digest=sha(sidebytes)
 plan=load('plan.json');commands=load('commands.json');terminal=load('terminal.json');headers=load('headers.json')
 need(side['source_pin']==plan['pin']==PIN,'source pin mismatch')
 for field,file in [('plan_sha256','plan.json'),('headers_sha256','headers.json')]:need(sha(raw(file))==side[field],field+' mismatch')
 for field,file in [('collector_sha256','collect-default.py'),('parser_sha256','parse-default.py')]:need(sha(obj(BASE+'collector/'+file,RUNNER))==side[field],field+' differs from reviewed runner')
 for name,d in side['producer_sources'].items():need(sha(obj(BASE+'method-v3/'+name,METHOD))==d,'producer mismatch '+name)
 need(set(side['modes'])=={'baseline','import-only','measured','traced'},'not four modes')
 need(side['budget_not_overridden'] and side['per_process_lean_threads']==2 and 1<=side['parallel_file_pipelines']<=8,'capacity/budget protocol differs')
 cfg={k:tomllib.loads(obj(p,PIN).decode()) for k,p in [('root','lakefile.toml'),('guide','guide/lakefile.toml')]}
 def flatten(d,p=''):
  o={}
  for k,v in d.items():
   n=p+'.'+k if p else k
   o.update(flatten(v,n)) if isinstance(v,dict) else o.update({n:v})
  return o
 def opts(path):
  c=cfg['guide' if path.startswith('guide/') else 'root'];o=flatten(c.get('leanOptions',{}));lib='ComplexityGuide' if path.startswith('guide/') else 'ComplexityAbstracts' if path.startswith('abstracts/') else path.split('/')[0]
  for x in c.get('lean_lib',[]):
   if x['name']==lib:o.update(flatten(x.get('leanOptions',{})))
  return o
 files={f['file_id']:f for f in plan['files']};need(len(files)==647,'prepared file count differs from647')
 byfile=collections.defaultdict(list)
 for c in commands:byfile[c['file_id']].append(c)
 need(len(commands)==647*4,'command accounting differs from2588')
 need(set(byfile)==set(files),'plan/command file membership differs')
 need(terminal.get('all_processes_terminal') is True,'terminal process state missing')
 need(terminal.get('commands')==len(commands),'terminal command accounting differs')
 status=collections.Counter();file_outcomes=[];all_event_ids=set();traces_total=0;pending_total=0;rows_by_event={};scope_heads=collections.Counter();synthetic=0;accepted_commands=0;unpositioned=0;localmaps=0
 for fid,f in files.items():
  rows=byfile.get(fid,[]);need(collections.Counter(c['mode'] for c in rows)==collections.Counter(side['modes']),'mode accounting '+f['path'])
  original=raw('originals/'+f['path']);need(sha(original)==f['sha256']==sha(obj(f['path'],PIN)),'original source hash '+f['path'])
  need(f['options']==opts(f['path']),'pinned option config '+f['path'])
  prefix='guide/' if f['path'].startswith('guide/') else 'abstracts/' if f['path'].startswith('abstracts/') else ''
  need(f['source_root_prefix']==prefix and f['expected_native_module']==f['path'][len(prefix):-5].replace('/','.'),'configured module root '+f['path'])
  baseline=next((c for c in rows if c['mode']=='baseline'),None);base_ctx=baseline.get('actual_context') if baseline else None
  for c in rows:
   key=f['path']+' '+c['mode'];need(c['run_id']==side['run_id'] and c['provenance']==digest,'command provenance '+key)
   expected={f'-D{k}={str(v).lower()}' for k,v in opts(f['path']).items()};flags={x for x in c['command'] if x.startswith('-D') and not x.startswith('-Dtrace.')}
   need(flags==expected and '--json' in c['command'],'CLI flags '+key)
   need(bool('-DwarningAsError=true' in flags)==f['path'].startswith('guide/'),'configured warning policy '+key)
   variant=raw('variants/'+fid+'/'+c['mode']+'/'+f['path']);need(sha(variant)==c['source_sha256'],'variant hash '+key)
   stripped=variant
   for i in sorted(c['insertions'],key=lambda i:i['original_byte'],reverse=True):
    n=i['original_byte']+sum(j['bytes'] for j in c['insertions'] if j['original_byte']<i['original_byte']);stripped=stripped[:n]+stripped[n+i['bytes']:]
   need(stripped==original,'source reversal '+key)
   ctx=c.get('actual_context')
   if ctx:
    need(ctx['module']==f['expected_native_module'],'native module '+key)
    if base_ctx:
     need(ctx['source_declaration_names']==base_ctx['source_declaration_names'],'native declaration context '+key)
     need((ctx['directImports'] if c['mode']=='baseline' else ctx['directImports'][:-1])==base_ctx['directImports'],'native imports '+key)
   elif c['returncode']==0:need(False,'successful command lacks native context '+key)
   diags=[]
   for line in raw('runs/'+fid+'/'+c['mode']+'.log').decode().splitlines():
    try:m=json.loads(line)
    except ValueError:continue
    if isinstance(m,dict) and all(k in m for k in ('fileName','pos','severity','data','kind')) and not m.get('isSilent',False):diags.append(m)
   warnok=not any(m['severity'] in ('warning','error') for m in diags)
   need(warnok==c['external_warning_acceptance'],'external warning classification '+key)
   need(dict(collections.Counter(m['severity'] for m in diags))==c['diagnostic_severities'],'diagnostic counts '+key)
   accepted=c['returncode']==0 and not c['external_timeout'] and warnok and ctx is not None and c.get('context_error') is None
   accepted_commands+=accepted
   file_outcomes.append({'path':f['path'],'mode':c['mode'],'returncode':c['returncode'],'external_timeout':c['external_timeout'],'external_warning_acceptance':warnok,'context_error':c.get('context_error'),'accepted':accepted})
   if c['mode'] in ('baseline','import-only'):continue
   eventpath='runs/'+fid+'/'+c['mode']+'.jsonl'
   if a.dataset+'/'+eventpath not in tracked:continue
   groups=collections.defaultdict(dict);trace_counts=collections.Counter()
   for line in raw(eventpath).splitlines():
    e=json.loads(line);eid=e['event_id']
    if e['phase']=='trace':trace_counts[eid]+=1;continue
    need(e.get('run_id')==side['run_id'] and e.get('provenance')==digest,'event provenance '+eid)
    if e['phase']=='unsupported_dispatch':status['unsupported_dispatch']+=1;continue
    need(e['phase'] in ('begin','end') and e['phase'] not in groups[eid],'event phase uniqueness '+eid);groups[eid][e['phase']]=e
   need(set(trace_counts)<=set(groups),'orphan native trace owner '+key);traces_total+=sum(trace_counts.values())
   for eid,g in groups.items():
    need(eid not in all_event_ids,'cross-file/mode duplicate event '+eid);all_event_ids.add(eid)
    if 'begin' not in g:need(False,'end without begin '+eid);continue
    b=g['begin'];e=g.get('end');synthetic+=not b['original_source_info']
    for h in b.get('goal_heads',[]):scope_heads[h['head_after_foralls_mdata']]+=1;need(h['normalized'] is False,'goal normalization claim '+eid)
    if b['filemap_equals_input_file']:
     fm=variant;need(b['filemap_bytes']==len(variant),'native FileMap byte size '+eid)
    else:
     localmaps+=1;need(isinstance(b.get('local_filemap_source'),str),'unidentified local FileMap '+eid);fm=(b.get('local_filemap_source') or '').encode()
    if type(b.get('start')) is int and type(b.get('end')) is int:
     need(0<=b['start']<=b['end']<=len(fm) and fm[b['start']:b['end']].decode()==b['text'],'native source span '+eid)
    else:
     unpositioned+=1;need(b['text']=='','unpositioned event invents source text '+eid)
    if e is None:pending_total+=1;status['censored_unknown']+=1;rows_by_event[eid]=(c,None,False);continue
    status[e['status']]+=1;same=b['thread_id']==e['thread_id'];need(e['same_thread']==same and e['start_thread_id']==b['thread_id'],'thread identity '+eid)
    if same:need(type(e['raw_body_thread_heartbeats']) is int and 0<=e['raw_body_thread_heartbeats']<=e['raw_region_thread_heartbeats'],'raw current-thread cost '+eid)
    else:need(e['raw_body_thread_heartbeats'] is None and e['raw_region_thread_heartbeats'] is None,'cross-thread invented cost '+eid)
    need(type(e['body_wall_nanoseconds']) is int and e['body_wall_nanoseconds']>=0,'wall counter '+eid)
    need(e['trace_entries']==trace_counts[eid],'trace count '+eid)
    rows_by_event[eid]=(c,e,accepted and e['status']=='returned')
 # Derived runtime rows are checked only for status/cost/whole-file acceptance, never static joins.
 attempts=load('attempts.json')
 for r in attempts:
  b=r.get('begin',{});eid=b.get('event_id') or r.get('event_id');entry=rows_by_event.get(eid)
  need(entry is not None,'parsed row lacks raw event '+str(eid))
  if entry is None:continue
  c,e,ok=entry;need(r['accepted_whole_file_cost']==ok,'whole-file cost acceptance '+eid)
  if e:
   need(r['status']==e['status'],'parsed status '+eid)
   rawcost=e['raw_body_thread_heartbeats'];need(r['body_user_heartbeat_units']==(None if rawcost is None else rawcost/1000),'HB unit conversion '+eid)
  else:need(r['status']=='censored_unknown' and r['body_user_heartbeat_units'] is None and not r['accepted_whole_file_cost'],'censored treatment '+eid)
 failed=[r for r in file_outcomes if not r['accepted']]
 result={'revision':a.revision,'source_pin':PIN,'method':METHOD,'runner':RUNNER,'issues':issues,'consistency_status':'PASS' if not issues else 'FINDINGS','manifested_files':len(artifact['files']),'prepared_files':len(files),'commands':len(commands),'accepted_commands':accepted_commands,'nonaccepted_commands':failed,'raw_attempt_records':len(all_event_ids),'raw_status_counts':dict(status),'synthetic_source_info_attempts':synthetic,'retained_trace_records':traces_total,'pending_censored':pending_total,'unpositioned_attempts':unpositioned,'local_filemap_attempts':localmaps,'parsed_attempt_rows':len(attempts),'raw_syntactic_goal_heads':dict(scope_heads),'excluded':'Own static census/classifications/joins; no final rule-proof attribution; no new Lean execution. Data consistency PASS does not waive corpus failures or claim all survey goals complete.'}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('nonaccepted_commands','raw_syntactic_goal_heads')},indent=2));return bool(issues)
if __name__=='__main__':raise SystemExit(main())
