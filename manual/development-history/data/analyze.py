#!/usr/bin/env python3
"""Validates: timing tables, Git growth reconciliation, and the selected CI cohort.

Recomputes from the exported records without private-log access or networking.
Durations are never interpreted as autonomous effort or successful theorem time.
"""
import argparse, collections, datetime as dt, json, math, statistics
from pathlib import Path
from git_history import REVISION
DEFAULT_DATA=Path(__file__).resolve().parents[2]/'_generated/development-history/data'

def stamp(s):return dt.datetime.fromisoformat(s.replace('Z','+00:00'))
def stats(xs):
    xs=sorted(xs)
    return {'n':len(xs),'sum_seconds':round(sum(xs),3),'median_seconds':round(statistics.median(xs),3),'p90_nearest_rank_seconds':round(xs[math.ceil(.9*len(xs))-1],3),'max_seconds':round(max(xs),3)} if xs else {'n':0}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--data-dir',type=Path,default=DEFAULT_DATA,help='Directory containing the explicitly extracted Git, private-log and GitHub records');ap.add_argument('--output',type=Path);a=ap.parse_args()
    b=a.data_dir
    read=lambda n:json.loads((b/(n+'.json')).read_text())
    turns=read('completed_turns');claude=read('claude_turn_durations');daily=read('git_daily');git=read('git_summary');ci=read('ci_cohort_2026-10-31')
    if git['revision']!=REVISION:raise ValueError('Git data does not describe the fixed historical revision')
    assert len(ci['runs'])==ci['total_count']==len({r['id'] for r in ci['runs']})
    assert all(r['event']=='merge_group' and r['created_at'].startswith('2026-10-31') for r in ci['runs'])
    out={'git_recorded_span_seconds':(stamp(git['snapshot_committer_time'])-stamp(git['first_committer_time'])).total_seconds(),'net_library_lines_from_first_parent_numstat':sum(d['library_added']-d['library_deleted'] for d in daily.values()),'timing_method':'Nonnegative duration telemetry; nearest-rank p90. No union across providers and no effort interpretation.','github_retrieval':{n:read(n).get('_retrieval') for n in ['ci_cohort_2026-10-31','pr_520','pr_1852','pr_2228','snapshot_ci_jobs']},'codex':{},'claude':{},'case_timings':{},'ci_day':{'date_utc':'2026-10-31','unique_run_ids':len(ci['runs']),'workflow_names':sorted({r['name'] for r in ci['runs']}),'last_reported_conclusions':dict(collections.Counter(r['conclusion'] for r in ci['runs'])),'recorded_attempt_numbers':dict(collections.Counter(r['run_attempt'] for r in ci['runs'])),'status_counts':dict(collections.Counter(r['status'] for r in ci['runs']))}}
    for co in sorted({t['cohort'] for t in turns}):
        out['codex'][co]={}
        for sk in sorted({t['source_kind'] for t in turns if t['cohort']==co}):
            ts=[t['duration_ms']/1000 for t in turns if t['cohort']==co and t['source_kind']==sk and isinstance(t.get('duration_ms'),(int,float)) and t['duration_ms']>=0]
            out['codex'][co][sk]=stats(ts)
    for co in sorted({t['cohort'] for t in claude}):out['claude'][co]=stats([t['duration_ms']/1000 for t in claude if t['cohort']==co and t['duration_ms']>=0])
    for n in ['520','1852','2228']:
        p=read('pr_'+n);out['case_timings']['pr_'+n]={'created_at':p['created_at'],'merged_at':p['merged_at'],'created_to_merged_seconds':(stamp(p['merged_at'])-stamp(p['created_at'])).total_seconds(),'meaning':'PR lead time including review/queue; excludes pre-PR work and may overlap other tasks.'}
    ex={r['excerpt_id']:r for r in read('transcript_excerpts')}
    out['case_timings']['circuit_human_request_to_pr_creation_seconds']=(stamp(read('pr_520')['created_at'])-stamp(ex['e02']['record_timestamp'])).total_seconds()
    out['case_timings']['circuit_human_request_to_pr_merge_seconds']=(stamp(read('pr_520')['merged_at'])-stamp(ex['e02']['record_timestamp'])).total_seconds()
    out['snapshot_ci_jobs']=[]
    for j in read('snapshot_ci_jobs')['jobs']:
        out['snapshot_ci_jobs'].append({'job_id':j['id'],'run_attempt':j['run_attempt'],'conclusion':j['conclusion'],'elapsed_seconds':(stamp(j['completed_at'])-stamp(j['started_at'])).total_seconds(),'steps':[{'name':s['name'],'conclusion':s['conclusion'],'elapsed_seconds':(stamp(s['completed_at'])-stamp(s['started_at'])).total_seconds()} for s in j['steps'] if s.get('completed_at') and s.get('started_at')]})
    output=a.output or b/'analysis.json';output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
