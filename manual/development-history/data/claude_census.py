#!/usr/bin/env python3
"""Validates: observed local Claude project-record counts and timestamp coverage.

Does not infer successful work, effort or autonomy from messages. Records are
deduplicated by UUID where present. Private message text is never in public data.
"""
import argparse, collections, datetime as dt, hashlib, json
from pathlib import Path
from session_census import opened, DEFAULT_OUTPUT
def stamp(x):
    try:return dt.datetime.fromisoformat(x.replace('Z','+00:00')) if isinstance(x,str) else None
    except ValueError:return None
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('projects_root',type=Path);ap.add_argument('--output',type=Path,default=DEFAULT_OUTPUT);ap.add_argument('--private-output',required=True);ap.add_argument('--cutoff',default='2026-11-02T03:45:45Z');a=ap.parse_args()
    if not a.projects_root.is_dir():ap.error('projects_root must be an existing private log directory')
    out=Path(a.output);out.mkdir(parents=True,exist_ok=True);priv=Path(a.private_output);priv.mkdir(parents=True,exist_ok=True);cutoff=stamp(a.cutoff)
    dirs=sorted(p for p in Path(a.projects_root).iterdir() if p.is_dir() and 'complexitylib' in p.name.lower())
    files=sorted(p for d in dirs for p in d.rglob('*') if p.is_file() and (p.name.endswith('.jsonl') or p.name.endswith('.jsonl.zst')))
    seen=set();rows=[];provenance=[];durations=[];errors=[]
    for n,p in enumerate(files):
        times=[];counts=collections.Counter();models=set();ids=set();toolcounts=collections.Counter();duplicates=0;first_user=None;sha=hashlib.sha256();paths=set()
        cohort='current_checkout_identity' if 'complexitylib2' in str(p) or 'cslib-community-complexitylib' in str(p) else 'predecessor_checkout_identity'
        try:
            with opened(p) as f:
                for lineno,line in enumerate(f,1):
                    sha.update(line.encode())
                    try:x=json.loads(line)
                    except ValueError:errors.append({'file':p.name,'line':lineno,'error':'invalid_json'});continue
                    t=stamp(x.get('timestamp'))
                    if t and t>cutoff:continue
                    uid=x.get('uuid')
                    if uid and uid in seen:duplicates+=1;continue
                    if uid:seen.add(uid)
                    if t:times.append(x['timestamp'])
                    if x.get('sessionId'):ids.add(x['sessionId'])
                    if x.get('cwd'):paths.add(x['cwd'])
                    typ=x.get('type');sub=x.get('subtype');counts[str(typ)+(':'+str(sub) if sub else '')]+=1
                    m=x.get('message',{});m=m if isinstance(m,dict) else {}
                    if m.get('model'):models.add(m['model'])
                    content=m.get('content',[])
                    if isinstance(content,str):content=[{'type':'text','text':content}]
                    if isinstance(content,list):
                        for c in content:
                            if not isinstance(c,dict):continue
                            if c.get('type')=='tool_use':toolcounts[c.get('name','UNKNOWN')]+=1
                            if typ=='user' and c.get('type')=='text' and first_user is None:
                                first_user={'timestamp':x.get('timestamp'),'line':lineno,'text':str(c.get('text',''))[:1600]}
                    if sub=='turn_duration' and isinstance(x.get('durationMs'),(int,float)):
                        durations.append({'source_basename':p.name,'uuid':uid,'timestamp':x.get('timestamp'),'duration_ms':x['durationMs'],'cohort':cohort,'record_line':lineno})
            if not times:continue
            rows.append({'source_basename':p.name,'cohort':cohort,'session_ids':sorted(ids),'earliest_record':min(times),'latest_record':max(times),'deduplicated_record_counts':dict(counts),'duplicate_uuid_rows_excluded':duplicates,'recorded_model_identifiers':sorted(models),'tool_use_counts':dict(toolcounts),'uncompressed_sha256':sha.hexdigest()})
            provenance.append({'source_basename':p.name,'path':str(p),'cwd_values':sorted(paths),'first_user':first_user})
        except OSError as e:errors.append({'file':p.name,'error':type(e).__name__})
        if (n+1)%100==0:print('Processed',n+1,'of',len(files),'Claude record files',flush=True)
    summary={'cutoff':a.cutoff,'provider':'Local Claude project store only','candidate_project_directories':len(dirs),'candidate_record_files':len(files),'files_with_timestamped_records_before_cutoff':len(rows),'unique_uuid_records_seen':len(seen),'duplicate_uuid_rows_excluded':sum(r['duplicate_uuid_rows_excluded'] for r in rows),'errors':errors,'cohorts':{}}
    for cohort in sorted({r['cohort'] for r in rows}):
        ss=[r for r in rows if r['cohort']==cohort];ts=[r for r in durations if r['cohort']==cohort]
        summary['cohorts'][cohort]={'record_files':len(ss),'distinct_reported_session_ids':len({i for r in ss for i in r['session_ids']}),'earliest_record':min(r['earliest_record'] for r in ss),'latest_record':max(r['latest_record'] for r in ss),'recorded_model_identifiers':dict(collections.Counter(m for r in ss for m in r['recorded_model_identifiers'])),'turn_duration_records':len(ts),'sum_reported_turn_duration_seconds':sum(t['duration_ms'] for t in ts)/1000}
    summary['limitations']=['A record file is not necessarily an independent conversation; subagents, branches and copied history can share session IDs.','UUID deduplication does not authenticate source identity or remove every possible copied text.','No missing completion time is imputed.','Recorded model names and duration telemetry are labels in logs, not independently authenticated provider measurements.','No content-level task-success or autonomous-work fraction is inferred.']
    for name,value in [('claude_records',rows),('claude_turn_durations',durations),('claude_summary',summary)]:
        (out/(name+'.json')).write_text(json.dumps(value,indent=2)+'\n')
    (priv/'claude_provenance.json').write_text(json.dumps(provenance,indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
