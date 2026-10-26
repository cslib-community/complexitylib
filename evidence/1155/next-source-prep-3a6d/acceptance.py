"""Strict fixed PREPARED thirteen-file/sixteen-call batch; no runtime collection."""
import hashlib,json

def require_complete(config,mapping_bytes,side_bytes,commands,events):
    def need(ok,msg):
        if not ok:raise ValueError(msg)
    need(hashlib.sha256(mapping_bytes).hexdigest()==config['mapping_sha256'],'mapping digest')
    side=json.loads(side_bytes);digest=hashlib.sha256(side_bytes).hexdigest()
    for key in ('source_pin','mapping_sha256','implementation_sha256'):
        need(side.get(key)==config[key],key)
    need(side.get('calls')==config['expected_calls'],'original call mapping')
    run=side.get('run_id');need(isinstance(run,str) and bool(run),'run ID')
    files={f['case']:f for f in config['files']}
    need(set(files)=={'machine-simulation','gaussian-edge-scores','vertex-gaussian','arthur-merlin-ph','set-lower-bound','monotone-circuit-completeness','subset-sum-mask','unary-prime','space','savitch','boosting-sampling','threesource-seeded','native-extract'} and len(config['expected_calls'])==16,'out of fixed scope')
    expected={(case,mode) for case in files for mode in config['required_modes']}
    need(len(commands)==39,'partial command ledger');seen=set()
    for command in commands:
        pair=(command.get('case'),command.get('mode'))
        need(pair in expected and pair not in seen,'duplicate/unknown command');seen.add(pair)
        f=files[pair[0]]
        need(command.get('returncode')==0,'whole-file command failure')
        need(command.get('run_id')==run and command.get('sidecar_sha256')==digest,'command provenance')
        need(command.get('source_sha256')==f['variant_sha256'][pair[1]],'variant hash')
        need(command.get('module_name')==f['module_name'] and command.get('context_verified') is True,'module context')
    need(seen==expected,'missing mode/file')
    calls={c['call_token']:c for c in config['expected_calls']}
    need(len(events)==32,'partial/censored/repeated events')
    grouped={};owners={}
    for event in events:
        token,phase=event.get('call_token'),event.get('phase')
        need(token in calls and phase in ('begin','end'),'unmapped event')
        need(event.get('run_id')==run and event.get('sidecar_sha256')==digest,'event provenance')
        ident=event.get('event_id');need(isinstance(ident,str) and bool(ident),'event ID')
        need(ident not in owners or owners[ident]==token,'cross-call event ID reuse');owners[ident]=token
        tid=event.get('thread_id');need(type(tid) is int and 0<=tid<2**64,'thread ID')
        pair=grouped.setdefault(token,{})
        need(phase not in pair,'duplicate/repeated event');pair[phase]=event
    need(set(grouped)==set(calls),'unobserved call')
    for token,pair in grouped.items():
        need(set(pair)=={'begin','end'},'unmatched/censored')
        b,e=pair['begin'],pair['end']
        need(b['event_id']==e['event_id'] and b['thread_id']==e['thread_id'],'attempt ownership')
        need(b.get('child_kind')==calls[token]['expected_kind'],'original parsed child kind')
        need(b.get('maxHeartbeats_user')==config['user_limit'],'budget')
        need(e.get('status')=='returned' and e.get('goals_after')==0,'unexpected/partial outcome')
        for field in ('raw_thread_heartbeats','wall_nanoseconds'):
            need(type(e.get(field)) is int and e[field]>=0,'missing/invalid cost')
    return True
