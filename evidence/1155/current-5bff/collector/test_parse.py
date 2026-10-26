#!/usr/bin/env python3
"""Artifact-only controls; never treated as measurements or whole-command acceptance."""
import contextlib,importlib.util,io,json,pathlib,shutil,tempfile
HERE=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('parser',HERE/'parse.py');p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
source=HERE.parent/'cloud-v4';static=pathlib.Path('/home/samuel/Code/complexitylib-codex/automation-survey-1155-audit/evidence/1155/current-5bffdf');results=[]
for case in ('complete','censored','missing_thread','duplicate_begin','unmatched_end','wrong_provenance'):
 with tempfile.TemporaryDirectory() as tmp:
  out=pathlib.Path(tmp)/'data';shutil.copytree(source,out)
  eventpath=out/'runs/fe86bf0a8e5e8785/measured.jsonl';events=[json.loads(x) for x in eventpath.read_text().splitlines()]
  if case=='censored':events=[x for x in events if x['phase']=='begin']
  if case=='missing_thread':events[0]['thread_id']=None
  if case=='duplicate_begin':events.insert(1,events[0])
  if case=='unmatched_end':events=[x for x in events if x['phase']=='end']
  if case=='wrong_provenance':events[0]['provenance']='wrong'
  eventpath.write_text(''.join(json.dumps(x)+'\n' for x in events))
  failed=False
  try:
   with contextlib.redirect_stdout(io.StringIO()):p.parse(out,static)
  except (AssertionError,ValueError,KeyError):failed=True
  if case in ('complete','censored'):
   assert not failed
   summary=json.loads((out/'summary.json').read_text())
   if case=='complete':assert summary['attempts']==6 and summary['mapped_attempts']==6
   else:
    rows=json.loads((out/'attempts.json').read_text());unknown=[r for r in rows if r['mode']=='measured'];assert len(unknown)==3
    assert all(r['status']=='censored_unknown' and r['raw_body_thread_heartbeats'] is None and not r['accepted_whole_file_cost'] for r in unknown)
  else:assert failed
  results.append({'synthetic_control':case,'result':'PASS','measurement':False})
print(json.dumps(results,indent=2))
