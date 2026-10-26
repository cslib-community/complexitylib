#!/usr/bin/env python3
"""Validate the fixed batch's raw records; not a general source collector."""
import pathlib,json,csv
from acceptance import require_complete
p=pathlib.Path(__file__).resolve().parent
cfg=json.loads((p/'config.json').read_text());mb=(p/'mapping.json').read_bytes();sb=(p/'runtime-sidecar.json').read_bytes();side=json.loads(sb)
commands=json.loads((p/'results.json').read_text());events=[]
for path in sorted(p.glob('*.events.jsonl')):
    events.extend(json.loads(line) for line in path.read_text().splitlines())
assert require_complete(cfg,mb,sb,commands,events)
rows=[]
for file in cfg['files']:
    for mode in ['baseline','import-only']:assert not (p/f"{file['case']}-{mode}.events.jsonl").exists()
    for call in file['calls']:
        b=next(x for x in events if x['call_token']==call['call_token'] and x['phase']=='begin')
        e=next(x for x in events if x['call_token']==call['call_token'] and x['phase']=='end')
        rows.append(dict(file=file['path'],module_name=file['module_name'],declaration=call['case'],tactic=call['tactic'],observed_child_kind=b['child_kind'],original_line=call['original_line'],original_byte_start=call['original_byte_start'],original_byte_end=call['original_byte_end'],full_call_id=call['call_id'],call_token=call['call_token'],run_id=side['run_id'],thread_id=b['thread_id'],async_option=b['async_option'],user_limit=b['maxHeartbeats_user'],status=e['status'],goals_after=e['goals_after'],raw_current_thread_heartbeats=e['raw_thread_heartbeats'],user_heartbeats=e['raw_thread_heartbeats']/1000,forwarded_wall_nanoseconds=e['wall_nanoseconds'],whole_file_modes_pass=True,final_proof_dependencies=None,methodology_approved=False))
(p/'parsed.json').write_text(json.dumps(rows,indent=2)+'\n')
with (p/'parsed.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n');w.writeheader();w.writerows(rows)
print(json.dumps([{k:x[k] for k in ['declaration','tactic','user_heartbeats','forwarded_wall_nanoseconds','observed_child_kind']} for x in rows],indent=2))
