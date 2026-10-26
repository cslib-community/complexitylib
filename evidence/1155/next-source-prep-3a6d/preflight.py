#!/usr/bin/env python3
"""Artifact-only mapping and SYNTHETIC fixed-contract controls; no execution driver call."""
import pathlib,json,hashlib,copy
from acceptance import require_complete
p=pathlib.Path(__file__).resolve().parent;cfg=json.loads((p/'config.json').read_text());mb=(p/'mapping.json').read_bytes()
assert hashlib.sha256(mb).hexdigest()==cfg['mapping_sha256']
assert len(cfg['files'])==13 and len(cfg['expected_calls'])==16
for f in cfg['files']:
 raw=(p/f['case']/'baseline'/f['path']).read_bytes()
 assert hashlib.sha256(raw).hexdigest()==f['source_sha256']
 for c in f['calls']:assert raw[c['original_byte_start']:c['original_byte_end']]==c['tactic'].encode()
 for mode,sha in f['variant_sha256'].items():assert hashlib.sha256((p/f['case']/mode/f['path']).read_bytes()).hexdigest()==sha
# Mock records exercise contract logic ONLY; never save real-looking measurement rows.
side=dict(run_id='SYNTHETIC-preflight-only',source_pin=cfg['source_pin'],mapping_sha256=cfg['mapping_sha256'],implementation_sha256=cfg['implementation_sha256'],calls=cfg['expected_calls'])
sb=json.dumps(side).encode();digest=hashlib.sha256(sb).hexdigest()
commands=[dict(case=f['case'],mode=m,returncode=0,run_id=side['run_id'],sidecar_sha256=digest,source_sha256=f['variant_sha256'][m],module_name=f['module_name'],context_verified=True) for f in cfg['files'] for m in cfg['required_modes']]
events=[]
for i,c in enumerate(cfg['expected_calls']):
 base=dict(call_token=c['call_token'],event_id='SYNTHETIC-'+str(i),run_id=side['run_id'],sidecar_sha256=digest,thread_id=1)
 events += [dict(base,phase='begin',maxHeartbeats_user=200000,child_kind=c['expected_kind']),dict(base,phase='end',status='returned',goals_after=0,raw_thread_heartbeats=0,wall_nanoseconds=0)]
assert require_complete(cfg,mb,sb,commands,events)
checks=[]
def reject(name,cmd=commands,ev=events):
 try:require_complete(cfg,mb,sb,cmd,ev)
 except ValueError as e:checks.append(dict(name=name,synthetic=True,rejected=True,reason=str(e)));return
 raise AssertionError(name+' was accepted')
reject('partial_event_pairs',ev=events[:-1]);reject('no_observed_calls',ev=[])
bad=copy.deepcopy(events);bad[-1]['status']='censored_unknown';bad[-1]['raw_thread_heartbeats']=None
reject('censored_not_success',ev=bad)
bad=copy.deepcopy(events);bad[-1]=copy.deepcopy(bad[1]);reject('duplicate_record',ev=bad)
bad=copy.deepcopy(events)
for e in bad:e.pop('thread_id',None)
reject('both_threads_missing',ev=bad)
bad=copy.deepcopy(events)
for e in bad:e['thread_id']=None
reject('both_threads_null',ev=bad)
bad=copy.deepcopy(events)
for e in bad:e['thread_id']=True
reject('bool_thread_invalid',ev=bad)
bad=copy.deepcopy(events)
for e in bad[2:4]:e['event_id']=bad[0]['event_id']
reject('global_cross_call_event_reuse',ev=bad)
bad=copy.deepcopy(events);bad[1]['event_id']='SYNTHETIC-other';reject('unmatched_attempt',ev=bad)
bad=copy.deepcopy(events);bad[0]['sidecar_sha256']='0'*64;reject('sidecar_mismatch',ev=bad)
bad=copy.deepcopy(events);bad[0]['child_kind']='SYNTHETIC-other';reject('wrong_tactic_kind',ev=bad)
bad=copy.deepcopy(commands);bad[-1]['returncode']=1;reject('failed_whole_file_command',cmd=bad)
reject('missing_mode',cmd=commands[:-1])
bad=copy.deepcopy(commands);bad[-1]=copy.deepcopy(bad[0]);reject('duplicate_command',cmd=bad)
bad=copy.deepcopy(commands);bad[-1]['module_name']='SYNTHETIC-renamed';reject('module_context_mismatch',cmd=bad)
report=dict(state='PREPARATION_ONLY',actual_Lean_runs=0,bootstrap_build_cache_operations=0,source_mapping_verified=True,selected_files=13,selected_calls=16,synthetic_complete_smoke_pass=True,synthetic_rejections=checks,actual_runtime_results='NOT_RUN; explicit builder handoff required')
(p/'preflight-results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'source_files':13,'mapped_calls':16,'synthetic_rejections':len(checks),'actual_Lean_runs':0},indent=2))
