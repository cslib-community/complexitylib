#!/usr/bin/env python3
"""Supplement search-hit issue comments with PR reviews and repository-wide inline comments."""
import concurrent.futures,datetime,hashlib,json,pathlib,subprocess
P=pathlib.Path(__file__).resolve().parent;REPO='cslib-community/complexitylib';START='2026-10-12T00:00:00Z'
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def gh(endpoint,fields):
 cmd=['gh','api',endpoint,'--method','GET']
 for k,v in fields.items():cmd+=['-f',f'{k}={v}']
 r=subprocess.run(cmd,text=True,capture_output=True)
 if r.returncode:raise RuntimeError(r.stderr)
 return json.loads(r.stdout)
def pages(endpoint,fields=None):
 result=[];page=1
 while True:
  rows=gh(endpoint,{**(fields or {}),'per_page':100,'page':page});result+=rows
  if len(rows)<100:return result
  page+=1
def save(name,x):(P/name).write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def record(x,kind,n):
 body=x.get('body') or '';return {'kind':kind,'number':n,'url':x['html_url'],'created_at':x.get('submitted_at') or x.get('created_at'),'updated_at':x.get('updated_at'),'state':x.get('state'),'author':x['user']['login'],'body':body,'body_sha256':hashlib.sha256(body.encode()).hexdigest()}
hits=json.loads((P/'search-hits.json').read_text());prs=sorted({x['issue']['number'] for x in hits if 'pull_request' in x['issue']});rows=[];errors=[];begun=now()
def get(n):
 return [record(x,'PR review',n) for x in pages(f'repos/{REPO}/pulls/{n}/reviews') if (x.get('submitted_at') or '')>=START]
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
 fs={ex.submit(get,n):n for n in prs}
 for f in concurrent.futures.as_completed(fs):
  try:rows+=f.result()
  except Exception as e:errors.append({'number':fs[f],'error':str(e)})
  save('pr-review-corpus.json',rows);save('review-retrieval-errors.json',errors)
inline=pages(f'repos/{REPO}/pulls/comments',{'since':START,'sort':'updated','direction':'asc'})
inline_rows=[]
for x in inline:
 n=int(x['pull_request_url'].rsplit('/',1)[1]);r=record(x,'inline review comment',n);r.update(path=x['path'],diff_hunk=x.get('diff_hunk'),commit_id=x.get('commit_id'));inline_rows.append(r)
save('inline-review-corpus.json',inline_rows)
save('review-retrieval-manifest.json',{'start_inclusive':START,'collection_began':begun,'collection_finished':now(),'searched_PR_count':len(prs),'retrieved_reviews':len(rows),'repository_wide_inline_comments':len(inline_rows),'errors':errors,'limits':'Review bodies limited to PRs selected by explicit search; inline comments enumerate repository-wide updated-since endpoint. Deleted/inaccessible/pending private reviews are not exposed.'})
print('reviews',len(rows),'inline',len(inline_rows),'errors',len(errors))
