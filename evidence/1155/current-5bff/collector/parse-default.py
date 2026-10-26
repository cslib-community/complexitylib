#!/usr/bin/env python3
"""One-off current-pin event reconciliation; no elaboration or cost imputation."""
import argparse,collections,hashlib,json,pathlib
PIN='5bffdf2f248bbbfddea6039ee25a953616dff15b'
KINDS={'Cslib.Tactic.PolyTime.tacticPolytime':'polytime','Mathlib.Meta.FunProp.funPropTacStx':'fun_prop','Cslib.Tactic.PPT.tacticPpt':'ppt'}
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,d):p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')
def parse(out,static):
 sidebytes=(out/'run-sidecar.json').read_bytes();side=json.loads(sidebytes);assert side['source_pin']==PIN
 provenance=sha(sidebytes);plan=json.loads((out/'plan.json').read_text());assert sha((out/'plan.json').read_bytes())==side['plan_sha256']
 tokens=json.loads((static/'index/all-target-tokens.json').read_text());anchors={(t['path'],t['byte_start'],t['tactic']):t for t in tokens}
 commands=json.loads((out/'commands.json').read_text());files={f['file_id']:f for f in plan['files']};attempts=[];unsupported=[];traces=[];ownership={};coverage=[]
 def original_pos(n,insertions):
  total=0
  for x in insertions:
   point=x['original_byte']+total
   if n<point:return n-total
   if n<point+x['bytes']:return None
   total+=x['bytes']
  return n-total
 for c in commands:
  f=files[c['file_id']];raw=(out/'originals'/f['path']).read_bytes();assert sha(raw)==f['sha256']==c['original_sha256']
  root=out/'variants'/f['file_id']/c['mode'];variant=(root/f['path']).read_bytes();assert sha(variant)==c['source_sha256']
  path=out/'runs'/f['file_id']/(c['mode']+'.jsonl');records=[] if not path.exists() else [json.loads(l) for l in path.read_text().splitlines()]
  pending={};ended=set();observed=set();mode_attempts=[]
  for event in records:
   eid=event['event_id'];phase=event['phase']
   if phase!='trace':assert event['run_id']==side['run_id'] and event['provenance']==provenance
   owner=(f['file_id'],c['mode']);assert ownership.setdefault(eid,owner)==owner
   if phase=='trace':
    assert eid in pending or eid in ended
    traces.append(dict(event,path=f['path'],mode=c['mode'],qualification='native retained trace message; attempt evidence, not final proof attribution'));continue
   assert isinstance(event.get('thread_id'),int) and event['thread_id']>0
   if phase in ('begin','unsupported_dispatch'):
    assert eid not in pending and eid not in ended
    assert event['kind'] in KINDS
    mapped=False;reason=None;start=end=None;anchor=None
    if not event.get('filemap_equals_input_file',False):reason='local_or_generated_filemap_not_original_file'
    elif not event.get('original_source_info',False):reason='synthetic_source_info'
    else:
     assert event['filemap_bytes']==len(variant)
     a,b=event['start'],event['end'];assert 0<=a<b<=len(variant)
     assert variant[a:b].decode()==event['text']
     start=original_pos(a,c['insertions']);end=original_pos(b,c['insertions'])
     if start is None or end is None:reason='diagnostic_insertion'
     else:
      assert raw[start:end].decode()==event['text']
      anchor=anchors.get((f['path'],start,KINDS[event['kind']]))
      if anchor and anchor['classification']=='authored_tactic_candidate':mapped=True;observed.add(anchor['call_id'])
      else:reason='generated_quoted_or_unindexed_anchor'
    row={'event_id':eid,'path':f['path'],'mode':c['mode'],'source_pin':PIN,'source_sha256':f['sha256'],'static_head_id':anchor['call_id'] if mapped else None,'runtime_full_syntax_id':f"{f['sha256']}:{f['path']}:{start}-{end}:{KINDS[event['kind']]}" if mapped else None,'mapping': 'exact_native_full_span_and_static_head' if mapped else reason,'begin':event,'whole_command_returncode':c['returncode'],'context_error':c['context_error']}
    if phase=='unsupported_dispatch':unsupported.append(row);ended.add(eid)
    else:pending[eid]=row
   elif phase=='end':
    assert eid in pending and eid not in ended
    row=pending.pop(eid);begin=row['begin'];same=begin['thread_id']==event['thread_id'];assert event['same_thread']==same and event['start_thread_id']==begin['thread_id']
    if not same:assert event['raw_body_thread_heartbeats'] is None and event['raw_region_thread_heartbeats'] is None
    else:
     for k in ('raw_body_thread_heartbeats','raw_region_thread_heartbeats'):assert isinstance(event[k],int) and event[k]>=0
    row.update(end=event,status=event['status'],raw_body_thread_heartbeats=event['raw_body_thread_heartbeats'],body_user_heartbeat_units=None if event['raw_body_thread_heartbeats'] is None else event['raw_body_thread_heartbeats']/1000,body_wall_nanoseconds=event['body_wall_nanoseconds'])
    row['accepted_whole_file_cost']=c['returncode']==0 and c.get('external_warning_acceptance',False) and c['context_error'] is None and event['status']=='returned'
    mode_attempts.append(row);ended.add(eid)
   else:raise ValueError('Unexpected phase '+phase)
  for row in pending.values():row.update(status='censored_unknown',end=None,raw_body_thread_heartbeats=None,body_user_heartbeat_units=None,body_wall_nanoseconds=None,accepted_whole_file_cost=False);mode_attempts.append(row)
  attempts+=mode_attempts
  for head in f['candidate_head_ids']:
   count=sum(a['static_head_id']==head for a in mode_attempts)
   coverage.append({'path':f['path'],'mode':c['mode'],'static_head_id':head,'observed_attempts':count,'state':'observed' if count else 'unsupported_dispatch' if any(u['static_head_id']==head and u['mode']==c['mode'] for u in unsupported) else 'not_observed','whole_command_returncode':c['returncode'],'qualification':'not observed is not zero cost; may be quoted, unreachable, unsupported, bypassed, or failed before invocation'})
 summary={'pin':PIN,'files_with_commands':len({c['file_id'] for c in commands}),'commands':len(commands),'whole_command_failures':sum(c['returncode']!=0 or not c.get('external_warning_acceptance',False) for c in commands),'attempts':len(attempts),'statuses':dict(collections.Counter(a['status'] for a in attempts)),'mapped_attempts':sum(a['static_head_id'] is not None for a in attempts),'unsupported_dispatches':len(unsupported),'native_trace_messages':len(traces),'qualification':'Partial dynamic survey. Returned tactics are not final proof attribution. Thread-local inclusive HB; async/shared-host wall and trace overhead qualified. No missing/censored cost imputed. Original command budgets unchanged.'}
 for name,data in [('attempts',attempts),('unsupported',unsupported),('trace-messages',traces),('coverage',coverage),('summary',summary)]:dump(out/(name+'.json'),data)
 print(json.dumps(summary))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('out',type=pathlib.Path);p.add_argument('--static',required=True,type=pathlib.Path);a=p.parse_args();parse(a.out,a.static)
