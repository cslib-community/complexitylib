#!/usr/bin/env python3
"""Validates: observed project-session counts and recorded turn durations before a cutoff.

Compressed inputs require Python 3.14 for stdlib zstd, or the optional zstandard package. Private
transcripts are read in place. Public outputs omit message text, tool arguments,
credentials, billing/account fields and absolute paths. A completed-turn duration
is reported telemetry, not CPU time, human time, or time spent proving a theorem.
"""
import argparse, collections, datetime as dt, hashlib, json
from pathlib import Path
DEFAULT_OUTPUT=Path(__file__).resolve().parents[2]/'_generated/history/data'

def open_zstd(p):
    try:
        from compression import zstd
    except ImportError:
        try:
            import io, zstandard
        except ImportError as exc:
            raise RuntimeError('Compressed logs require Python 3.14 or the zstandard package') from exc
        return io.TextIOWrapper(zstandard.ZstdDecompressor().stream_reader(p.open('rb')))
    return zstd.open(p,'rt')

def stamp(x):
    return dt.datetime.fromisoformat(x.replace('Z','+00:00')) if isinstance(x,str) else None
def kind(source):
    if isinstance(source,dict):
        sub=source.get('subagent',{})
        if isinstance(sub,dict):
            if 'other' in sub:return 'subagent:'+str(sub['other'])
            return 'subagent:'+','.join(sorted(sub))
        return 'subagent'
    return str(source)
def opened(p):return open_zstd(p) if p.name.endswith('.zst') else p.open()

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('session_root',type=Path);ap.add_argument('--private-output',required=True);ap.add_argument('--output',type=Path,default=DEFAULT_OUTPUT);ap.add_argument('--cutoff',default='2026-11-02T03:45:45Z');a=ap.parse_args()
    if not a.session_root.is_dir():ap.error('session_root must be an existing private log directory')
    cutoff=stamp(a.cutoff);out=Path(a.output);out.mkdir(parents=True,exist_ok=True);priv=Path(a.private_output);priv.mkdir(parents=True,exist_ok=True)
    metadata=[];errors=[]
    for p in sorted(Path(a.session_root).rglob('*')):
        if not p.is_file() or not (p.name.endswith('.jsonl') or p.name.endswith('.jsonl.zst')):continue
        try:
            with opened(p) as f:first=json.loads(f.readline())
            m=first.get('payload',{});cwd=m.get('cwd','');roots=m.get('runtime_workspace_roots',[])
            if 'complexitylib' not in (cwd+' '+str(roots)).lower():continue
            start=m.get('timestamp',first.get('timestamp'))
            if not start or stamp(start)>cutoff:continue
            cohort=('current_checkout_identity' if '/cslib-community/complexitylib' in cwd or cwd.endswith('/complexitylib2') else 'predecessor_checkout_identity')
            metadata.append({'path':str(p),'id':m.get('id'),'parent_thread_id':m.get('parent_thread_id'),'start':start,'cwd':cwd,'cohort':cohort,'source_kind':kind(m.get('source')),'cli_version':m.get('cli_version'),'history_mode':m.get('history_mode'),'subagent_history_start_ordinal':m.get('subagent_history_start_ordinal'),'disk_bytes':p.stat().st_size})
        except RuntimeError:raise
        except Exception as e:errors.append({'file':p.name,'error':type(e).__name__})
    # IDs deduplicate copied containers; longest on-disk record is retained, with all alternatives recorded privately.
    byid={};duplicates=[]
    for m in metadata:
        k=m['id'] or m['path']
        if k in byid:
            duplicates.append({'id':k,'paths':[byid[k]['path'],m['path']]})
            if m['disk_bytes']>byid[k]['disk_bytes']:byid[k]=m
        else:byid[k]=m
    rows=[];turns=[];selection=[]
    for n,m in enumerate(sorted(byid.values(),key=lambda x:x['start'])):
        p=Path(m['path']);counts=collections.Counter();tools=collections.Counter();models=set();events=[];last=None;excluded_earlier=0;excluded_later=0;sha=hashlib.sha256();first_user=None;turnids=set();pr_mentions=set();record_errors=0
        with opened(p) as f:
            for lineno,line in enumerate(f,1):
                sha.update(line.encode())
                try:x=json.loads(line)
                except ValueError:record_errors+=1;continue
                t=stamp(x.get('timestamp'));v=x.get('payload',{});typ=x.get('type')
                if not isinstance(v,dict):continue
                # Inherited prompt history is not a new session event.
                if t and t<stamp(m['start']):excluded_earlier+=1;continue
                if t and t>cutoff:excluded_later+=1;continue
                h=m.get('subagent_history_start_ordinal')
                if isinstance(h,int) and isinstance(x.get('ordinal'),int) and x['ordinal']<h and typ!='session_meta':excluded_earlier+=1;continue
                if t:last=x['timestamp'];events.append(x['timestamp'])
                k=typ+':'+str(v.get('type',''));counts[k]+=1
                if typ=='turn_context' and v.get('model'):models.add(v['model'])
                if typ=='response_item' and v.get('type') in ['function_call','custom_tool_call']:
                    tools[v.get('name','UNKNOWN')]+=1
                if typ=='event_msg' and v.get('type')=='user_message' and first_user is None:
                    first_user={'line':lineno,'timestamp':x.get('timestamp'),'text':str(v.get('message',''))[:1600]}
                if typ=='event_msg' and v.get('type')=='task_complete':
                    tid=v.get('turn_id')
                    if tid in turnids:continue
                    turnids.add(tid)
                    duration=v.get('duration_ms');start=v.get('started_at');end=v.get('completed_at')
                    turns.append({'session_id':m['id'],'turn_id':tid,'cohort':m['cohort'],'source_kind':m['source_kind'],'record_line':lineno,'record_timestamp':x.get('timestamp'),'duration_ms':duration,'started_at_epoch_seconds':start,'completed_at_epoch_seconds':end,'time_to_first_token_ms':v.get('time_to_first_token_ms')})
        row={k:m[k] for k in ['id','parent_thread_id','start','cohort','source_kind','cli_version']}
        row.update({'source_basename':p.name,'uncompressed_sha256':sha.hexdigest(),'last_observed_at_or_before_cutoff':last,'record_counts':dict(counts),'tool_call_counts':dict(tools),'recorded_model_identifiers':sorted(models),'inherited_or_prestart_rows_excluded':excluded_earlier,'postcutoff_rows_excluded':excluded_later,'malformed_rows':record_errors,'completed_turn_count':len(turnids)})
        rows.append(row);selection.append({'id':m['id'],'path':m['path'],'cohort':m['cohort'],'source_kind':m['source_kind'],'first_user':first_user})
        if (n+1)%100==0:print('Processed',n+1,'of',len(byid),'project sessions',flush=True)
    summaries={}
    for cohort in sorted({r['cohort'] for r in rows}):
        subset=[r for r in rows if r['cohort']==cohort];ts=[t for t in turns if t['cohort']==cohort and isinstance(t['duration_ms'],(int,float)) and t['duration_ms']>=0]
        summaries[cohort]={'sessions':len(subset),'source_kinds':dict(collections.Counter(r['source_kind'] for r in subset)),'recorded_model_identifiers':dict(collections.Counter(x for r in subset for x in r['recorded_model_identifiers'])),'completed_turn_records_with_duration':len(ts),'sum_reported_completed_turn_seconds':sum(t['duration_ms'] for t in ts)/1000,'earliest_start':min(r['start'] for r in subset),'latest_observed':max(r['last_observed_at_or_before_cutoff'] or r['start'] for r in subset)}
    summary={'cutoff':a.cutoff,'source':'Local Codex session store only; desktop/other providers not included.','deduplicated_sessions':len(rows),'duplicate_id_records':len(duplicates),'metadata_errors':errors,'cohorts':summaries,'limitations':['Path identity is not a semantic classification of every task.','Earlier/inherited rows are excluded using metadata and timestamps where available; absent metadata prevents perfect historical deduplication.','Concurrent sessions and nested agents overlap; summed turn durations are not elapsed calendar time or human labor.','Completion means a logged turn completed, not that its mathematical task succeeded.','Recorded model labels are telemetry, not independently authenticated model identity.','Sessions lacking completion records remain in session denominators but not duration totals.']}
    for name,value in [('sessions',rows),('completed_turns',turns),('session_summary',summary)]:
        (out/(name+'.json')).write_text(json.dumps(value,indent=2)+'\n')
    (priv/'session_provenance.json').write_text(json.dumps({'metadata':metadata,'duplicates':duplicates,'selection':selection},indent=2)+'\n')
    print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
