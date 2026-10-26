#!/usr/bin/env python3
"""Read-only GitHub/history retrieval with explicit corpus boundaries; no Lean or production edits."""
import collections, concurrent.futures, datetime, hashlib, json, pathlib, re, subprocess, time
HERE=pathlib.Path(__file__).resolve().parent
REPO='cslib-community/complexitylib'; START='2026-10-12T00:00:00Z'; SOURCE='5bffdf2f248bbbfddea6039ee25a953616dff15b'
TERMS=['polytime','fun_prop','ppt','aesop','heartbeat','heartbeats','maxHeartbeats','maxSteps','timeout','encoding','"rule order"','"rule-order"','"manual composition"','"explicit composition"','"proof replacement"','regression']
KEYWORDS=re.compile(r'polytime|fun_prop|\bppt\b|\baesop\b|heartbeat|maxSteps|timeout|timed.out|encoding|rule[ -]order|(?:manual|explicit).{0,40}(?:compos|proof)|proof.{0,20}replac|regression',re.I)
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(x):return hashlib.sha256(x.encode()).hexdigest()
def dump(path,data):path.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
def gh(endpoint,fields=None):
    cmd=['gh','api',endpoint,'--method','GET']
    for k,v in (fields or {}).items():cmd+=['-f',f'{k}={v}']
    p=subprocess.run(cmd,capture_output=True,text=True)
    if p.returncode:raise RuntimeError(p.stderr)
    return json.loads(p.stdout)
def paginate(endpoint):
    rows=[];page=1
    while True:
        data=gh(endpoint,{'per_page':100,'page':page});rows+=data
        if len(data)<100:return rows
        page+=1

def main():
    begun=now();queries=[];hits={}
    for term in TERMS:
        q=f'repo:{REPO} updated:2026-10-12..2026-10-26 in:title,body,comments {term}'
        page=1;count=0
        while True:
            # Authenticated search allows30requests/minute. Keep a margin for other workers.
            time.sleep(2.2)
            try:data=gh('search/issues',{'q':q,'per_page':100,'page':page})
            except RuntimeError as e:
                queries.append({'query':q,'page':page,'error':str(e),'retrieved_at':now()});break
            rawitems=data['items'];queries.append({'query':q,'page':page,'retrieved_at':now(),'total_count':data['total_count'],'incomplete_results':data.get('incomplete_results'),
                'returned':len(rawitems),'numbers':[x['number'] for x in rawitems]})
            for x in rawitems:
                n=x['number'];entry=hits.setdefault(n,{'issue':x,'matched_queries':[]});entry['matched_queries'].append(term)
            count+=len(rawitems)
            dump(HERE/'search-pages.json',queries);dump(HERE/'search-hits.json',list(hits.values()))
            if len(rawitems)<100 or count>=min(data['total_count'],1000):break
            page+=1
        print('query',term,'hits so far',len(hits),flush=True)
    # Always retain the known review surfaces, even if GitHub search indexing missed them.
    known=[608,733,862,1063,1137,1148,1155,1168,1171,1184]
    for n in known:
        if n not in hits:hits[n]={'issue':gh(f'repos/{REPO}/issues/{n}'),'matched_queries':['explicit historical surface']}
    def fetch(item):
        n,entry=item;x=gh(f'repos/{REPO}/issues/{n}');comments=paginate(f'repos/{REPO}/issues/{n}/comments') if x['comments'] else []
        body=x.get('body') or '';records=[{'kind':'title/body','number':n,'url':x['html_url'],'created_at':x['created_at'],'updated_at':x['updated_at'],'title':x['title'],'body':body,'body_sha256':sha(body),
            'in_requested_date_range':x['updated_at']>=START,'keyword_match':bool(KEYWORDS.search(x['title']+'\n'+body))}]
        for c in comments:
            if c['created_at']<START and c['updated_at']<START:continue
            body=c['body'];records.append({'kind':'comment','number':n,'url':c['html_url'],'created_at':c['created_at'],'updated_at':c['updated_at'],'author':c['user']['login'],'body':body,'body_sha256':sha(body),'in_requested_date_range':True,'keyword_match':bool(KEYWORDS.search(body))})
        return {'number':n,'title':x['title'],'url':x['html_url'],'is_pr':'pull_request' in x,'state':x['state'],'updated_at':x['updated_at'],'comments_total_retrieved':len(comments),'matched_queries':entry['matched_queries'],'records':records}
    corpus=[];errors=[]
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
        future={ex.submit(fetch,item):item[0] for item in sorted(hits.items())}
        for f in concurrent.futures.as_completed(future):
            n=future[f]
            try:corpus.append(f.result())
            except Exception as e:errors.append({'number':n,'error':str(e)})
            dump(HERE/'github-corpus.json',sorted(corpus,key=lambda x:x['number']));dump(HERE/'retrieval-errors.json',errors)
    log=subprocess.check_output(['git','log','--first-parent',f'--since={START}','--format=%H%x00%cI%x00%s',SOURCE],cwd=HERE,text=True).splitlines();commits=[]
    for line in log:
        rev,date,title=line.split('\0',2)
        if KEYWORDS.search(title):
            patch=subprocess.check_output(['git','show','--format=fuller','--no-ext-diff',rev],cwd=HERE,text=True)
            commits.append({'sha':rev,'committer_date':date,'title':title,'selection':'keyword in main first-parent title','patch_sha256':sha(patch),'patch':patch})
    dump(HERE/'main-title-matches.json',commits)
    manifest={'source_pin':SOURCE,'start_inclusive':START,'search_date_end_inclusive':'2026-10-26','collection_began':begun,'collection_finished':now(),'repository':REPO,'terms':TERMS,
        'github_search_surfaces':'issue/PR title,body,comments; updated date; all pages through1000 API ceiling','issues_or_prs_retrieved':len(corpus),'retrieval_errors':errors,
        'full_body_records':sum(len(x['records']) for x in corpus),'keyword_records':sum(r['keyword_match'] for x in corpus for r in x['records']),
        'main_first_parent_commits_in_range':len(log),'main_title_keyword_commits':len(commits),
        'limits':['GitHub search indexing/tokenization/incomplete_results and1000 ceiling are explicit; known historical surfaces included regardless.',
            'Comment API does not expose review inline comments/review bodies; those need separate PR-review retrieval.',
            'Main history is pinned5bff; retrieved GitHub text can postdate this source, with individual timestamps.','No keyword match alone is a verified regression, cause, necessary workaround, or current unresolved defect.']}
    dump(HERE/'retrieval-manifest.json',manifest);print(json.dumps(manifest,indent=2))
if __name__=='__main__':main()
