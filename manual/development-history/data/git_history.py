#!/usr/bin/env python3
"""Validates: repository chronology and source-change counts at the pinned revision.

First-parent changes count each integration once. Textual churn is not new
mathematics, agent effort, successful tasks, or a productivity measurement.
"""
import argparse, collections, datetime, json, os, re, subprocess
from pathlib import Path
REVISION='13e6a31951bf1c89a1a6258c44f9444aecbbefd8'
DEFAULT_OUTPUT=Path(__file__).resolve().parents[2]/'_generated/development-history/data'

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('repository',help='Repository with complete history through the fixed revision');ap.add_argument('--output',type=Path,default=DEFAULT_OUTPUT);a=ap.parse_args()
    out=Path(a.output);out.mkdir(parents=True,exist_ok=True)
    env={**os.environ,'GIT_NO_LAZY_FETCH':'1','GIT_NO_REPLACE_OBJECTS':'1','GIT_OPTIONAL_LOCKS':'0'}
    def git(*args):return subprocess.run(['git','-C',a.repository,*args],capture_output=True,text=True,check=True,env=env).stdout
    if git('rev-parse','--is-shallow-repository').strip()!='false':
        ap.error('Complete historical Git objects are required; shallow history is not a full chronology.')
    text=git('log','--first-parent','--reverse',REVISION,'--format=%H%x00%P%x00%aI%x00%cI%x00%an%x00%s%x00%b%x00%x1e')
    rows=[]
    for block in text.split('\x1e'):
        if not block.strip():continue
        bits=block.strip('\n').split('\0')
        sha,parents,author_time,commit_time,author,subject,body=bits[:7]
        pr=re.search(r'\(#(\d+)\)\s*$',subject)
        rows.append({'sha':sha,'parents':parents.split(),'author_time':author_time,'committer_time':commit_time,'author_name':author,'subject':subject,'pr_number':int(pr.group(1)) if pr else None,'coauthor_labels':sorted(set(re.findall(r'(?im)^co-authored-by:\s*([^<\n]+)',body))),'claude_session_urls':sorted(set(re.findall(r'https://claude\.ai/code/session_[A-Za-z0-9]+',body))),'body':body})
    bysha={r['sha']:r for r in rows}; changes=git('log','--first-parent','--reverse','--diff-merges=first-parent','--no-renames','--numstat',REVISION,'--format=@@@%H')
    cur=None
    for line in changes.splitlines():
        if line.startswith('@@@'):cur=bysha[line[3:]];cur['changes']={'library_added':0,'library_deleted':0,'test_added':0,'test_deleted':0,'all_added':0,'all_deleted':0,'binary_entries':0};continue
        m=re.match(r'^(\d+|-)\t(\d+|-)\t(.+)$',line)
        if not m or cur is None:continue
        add,delete,path=m.groups();c=cur['changes']
        if add=='-':c['binary_entries']+=1;continue
        add,delete=int(add),int(delete);c['all_added']+=add;c['all_deleted']+=delete
        prefix='library' if path.startswith('Complexity/') and path.endswith('.lean') else 'test' if path.startswith('ComplexityTests/') and path.endswith('.lean') else None
        if prefix:c[prefix+'_added']+=add;c[prefix+'_deleted']+=delete
    daily={}
    for r in rows:
        day=datetime.datetime.fromisoformat(r['committer_time']).astimezone(datetime.timezone.utc).date().isoformat()
        d=daily.setdefault(day,collections.Counter());d['first_parent_commits']+=1;d['subject_pr_suffixes']+=r['pr_number'] is not None
        d.update(r.get('changes',{}))
    prs={r['pr_number'] for r in rows if r['pr_number']};labels=collections.Counter(x.strip() for r in rows for x in r['coauthor_labels'])
    summary={'revision':REVISION,'reachable_commits':int(git('rev-list','--count',REVISION).strip()),'first_parent_commits':len(rows),'distinct_subject_pr_numbers':len(prs),'first_author_time':rows[0]['author_time'],'first_committer_time':rows[0]['committer_time'],'snapshot_author_time':rows[-1]['author_time'],'snapshot_committer_time':rows[-1]['committer_time'],'first_parent_author_names':dict(collections.Counter(r['author_name'] for r in rows)),'commits_with_coauthor_labels':sum(bool(r['coauthor_labels']) for r in rows),'coauthor_labels_per_commit':dict(sorted(labels.items())),'commits_with_claude_session_url':sum(bool(r['claude_session_urls']) for r in rows),'distinct_claude_session_urls':len({u for r in rows for u in r['claude_session_urls']}),'method':'First-parent integration chronology. Dates are recorded Git metadata, not task start/end times. Coauthor labels and session URLs are disclosures, not independently measured agent identity or contribution.'}
    (out/'git_commits.json').write_text(json.dumps(rows,indent=2)+'\n');(out/'git_daily.json').write_text(json.dumps(daily,indent=2)+'\n');(out/'git_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
