#!/usr/bin/env python3
"""Validate native current-pin source spans against the static index, without running Lean.

Input is a list of records with explicit original_pin, original_path, original_sha256,
original_byte_start/end, original_text, tactic, syntax_kind, and provenance_artifact.
The original span is the FULL parser tactic span, unlike the static HEAD-token identity.
This file does not invent or normalize timing fields or mark a returned tactic as successful.
"""
import argparse, hashlib, json, pathlib, subprocess
HERE=pathlib.Path(__file__).resolve().parent
PIN='5bffdf2f248bbbfddea6039ee25a953616dff15b'
def join(records,candidates,read_source):
    anchors={}
    for c in candidates:
        key=(c['path'],c['source_sha256'],c['byte_start'],c['tactic'])
        if key in anchors:raise ValueError('Ambiguous static source anchor')
        anchors[key]=c
    rows=[];seen=set()
    for r in records:
        if r['original_pin']!=PIN:raise ValueError('Historical measurement is not current-pin evidence')
        path=r['original_path'];raw=read_source(path)
        if hashlib.sha256(raw).hexdigest()!=r['original_sha256']:raise ValueError('Source hash mismatch')
        a,b=r['original_byte_start'],r['original_byte_end']
        if not 0<=a<b<=len(raw):raise ValueError('Invalid UTF-8 byte range')
        if raw[a:b].decode('utf-8')!=r['original_text']:raise ValueError('Parser text/span mismatch')
        if not r['syntax_kind'] or not r['provenance_artifact']:raise ValueError('Missing native kind/provenance')
        key=(path,r['original_sha256'],a,r['tactic'])
        candidate=anchors.get(key)
        if not candidate:raise ValueError('No exact static source anchor; generated/unmapped cases need separate accounting')
        if b<candidate['byte_end']:raise ValueError('Native span does not contain target head')
        # Multiple events at one authored site are possible; never collapse their costs.
        runtime_id=f"{r['original_sha256']}:{path}:{a}-{b}:{r['tactic']}"
        event_key=(runtime_id,r.get('run_id'),r.get('thread_id'),r.get('event_id'))
        if event_key in seen:raise ValueError('Duplicate runtime event identity')
        seen.add(event_key)
        rows.append({'static_head_id':candidate['call_id'],'runtime_full_syntax_id':runtime_id,
            'join_status':'exact-current-pin-source-anchor-and-validated-full-parser-span',
            'static_lexical_classification':candidate['classification'],'native_record':r,
            'qualification':'Source identity join only; verify run freshness, complete context, event ownership, status/goals and whole-file acceptance in the dynamic collector.'})
    return rows
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('records',type=pathlib.Path);ap.add_argument('--output',required=True,type=pathlib.Path);args=ap.parse_args()
    candidates=json.loads((HERE/'index/all-target-tokens.json').read_text())
    def read(path):return subprocess.check_output(['git','show',f'{PIN}:{path}'],cwd=HERE)
    rows=join(json.loads(args.records.read_text()),candidates,read)
    args.output.write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
