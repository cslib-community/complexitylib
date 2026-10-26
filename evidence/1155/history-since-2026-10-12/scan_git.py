#!/usr/bin/env python3
"""Index actual pinned main diff evidence, not just commit-title keyword hits."""
import datetime,hashlib,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent;PIN='5bffdf2f248bbbfddea6039ee25a953616dff15b';START='2026-10-12T00:00:00Z'
rx=re.compile(r'polytime|fun_prop|\bppt\b|\baesop\b|[Hh]eartbeat|maxSteps|timeout|rule[ -]order|\.(?:comp|prod)\b')
log=subprocess.check_output(['git','log','--first-parent',f'--since={START}','--format=%H%x00%cI%x00%s',PIN],cwd=HERE.parents[2],text=True).splitlines();rows=[]
for raw in log:
 rev,date,title=raw.split('\0',2)
 rawpatch=subprocess.check_output(['git','show','--format=','--no-ext-diff','--diff-merges=first-parent','--unified=3',rev,'--','*.lean'],cwd=HERE.parents[2]);patch=rawpatch.decode('utf-8',errors='replace')
 if not rx.search(patch):continue
 files=[];path=None;header=None;lines=[]
 def add():
  if path and lines and rx.search('\n'.join(lines)):
   added=[x[1:] for x in lines if x.startswith('+') and not x.startswith('+++')];removed=[x[1:] for x in lines if x.startswith('-') and not x.startswith('---')]
   a='\n'.join(added);r='\n'.join(removed)
   files.append({'path':path,'hunk_header':header,'lines':lines,
    'removed_automation_syntax':bool(re.search(r'\b(polytime|fun_prop|ppt|aesop)\b',r)),
    'added_composition_syntax':bool(re.search(r'\.(comp|prod)\b',a)),
    'budget_directive_delta':any('set_option' in x and re.search(r'maxHeartbeats|maxRecDepth',x) for x in added+removed),
    'classification':'lexical diff evidence only; manual-repair motivation/causality require cited report'})
 for line in patch.splitlines():
  if line.startswith('diff --git '):add();path=line.split(' b/',1)[-1];header=None;lines=[]
  elif line.startswith('@@'):add();header=line;lines=[]
  elif header is not None:lines.append(line)
 add()
 if files:rows.append({'sha':rev,'committer_date':date,'title':title,'url':f'https://github.com/cslib-community/complexitylib/commit/{rev}','lean_patch_sha256':hashlib.sha256(rawpatch).hexdigest(),'utf8_replacement_characters':patch.count('�'),'matching_hunks':files})
assert rows, 'No relevant main diffs: check pathspec/root rather than accept empty coverage'
(HERE/'main-diff-index.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
summary={'pin':PIN,'start_inclusive':START,'all_first_parent_commits_scanned':len(log),'commits_with_matching_Lean_diff_hunks':len(rows),'matching_hunks':sum(len(r['matching_hunks']) for r in rows),'possible_removed_automation_added_composition_hunks':sum(h['removed_automation_syntax'] and h['added_composition_syntax'] for r in rows for h in r['matching_hunks']),'budget_directive_hunks':sum(h['budget_directive_delta'] for r in rows for h in r['matching_hunks']),'semantic_inference':'No candidate is automatically a necessary workaround, a heartbeat raise, or a regression.'}
(HERE/'main-diff-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
