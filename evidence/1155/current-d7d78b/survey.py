#!/usr/bin/env python3
"""Auditable static source index; never runs Lean, imports build outputs, or times goals.

Source spans are UTF-8 byte offsets; syntax boundaries and declaration names are lexical
and are NOT Lean parser/elaborator results. Every exact target token is accounted for.
"""
import argparse, bisect, collections, hashlib, importlib.util, io, json, pathlib, re, subprocess, tarfile
PIN = 'd7d78b18a8e9cd7e84212459c6074776b9da8208'
ROOTS = ('Complexity', 'ComplexityTests', 'abstracts', 'guide')
HERE = pathlib.Path(__file__).resolve().parent
REPO = HERE.parents[2]
spec = importlib.util.spec_from_file_location('proof_lengths', REPO/'scripts/proof_lengths.py')
lexer = importlib.util.module_from_spec(spec); spec.loader.exec_module(lexer)
TARGET = re.compile(r'(?<![\w\'])\b(polytime|fun_prop|ppt)\b(?![\w\'])')
DECL = re.compile(r'\b(theorem|lemma|example|def|instance|abbrev|opaque|axiom|structure|class|inductive|macro_rules|elab_rules|macro|elab|syntax)\b(?:\s+([^\s(:={\[]+))?')
OPTION = re.compile(r'\bset_option\s+([\w.]+)\s+([^\s;]+)(\s+in\b)?')
PLUMB = re.compile(r'\.(comp|trans|prod|pair|tidy|of_tidy)\b|\b(first|try|orelse|fail_if_success|guard_msgs)\b|<\|>')
CERT = re.compile(r'\b(?:program_certificate|fun_prop|aesop)\b')
sha = lambda b: hashlib.sha256(b).hexdigest()
def dump(path,x): path.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def source_files(pin):
    raw=subprocess.check_output(['git','archive',pin,*ROOTS],cwd=REPO)
    with tarfile.open(fileobj=io.BytesIO(raw)) as t:
        return [(m.name,t.extractfile(m).read()) for m in sorted(t.getmembers(),key=lambda m:m.name) if m.isfile()]
def classify(code,pos,command):
    prefix=code[max(0,pos-600):pos]; line=prefix.rsplit('\n',1)[-1]
    if pos and code[pos-1]=='.': return 'qualified_identifier_reference'
    if prefix.endswith('`'): return 'quoted_identifier_reference'
    if re.search(r'(?:name|tacticName)\s*:=\s*$',line): return 'metadata_reference'
    # Bracket stack distinguishes nested attribute payloads; quotation handling stays lexical.
    depth=0; opens=[]
    for i,c in enumerate(prefix):
        if c=='[': opens.append(i)
        elif c==']' and opens: opens.pop()
    for i in opens:
        before=prefix[max(0,i-80):i]
        if re.search(r'@\s*$|\battribute\s*$',before):return 'attribute_registration'
        if re.search(r'rule_sets|declare_aesop_rule_sets',before):return 'ruleset_reference'
    if re.search(r'\b(?:namespace|open|export|attribute)\s*$',line): return 'name_reference'
    if re.search(r'`\([^\n]*tactic(?:Seq)?\s*\|',prefix):return 'quoted_tactic_candidate'
    if re.search(r'\b(?:macro|elab|syntax|macro_rules|elab_rules)\b',command[:180]):return 'metaprogram_context_candidate'
    return 'authored_tactic_candidate'
def candidate_end(code,start,limit):
    # Delimiters inside explicit tactic arguments are retained; indentation is conservative.
    depth=0; i=start; base=start-code.rfind('\n',0,start)-1
    while i<limit:
        c=code[i]
        if c in '([{':depth+=1
        elif c in ')]}':
            if depth==0:break
            depth-=1
        if depth==0 and (code.startswith('<;>',i) or c==';' or code.startswith('<|>',i)):break
        if depth==0 and c=='\n':
            j=i+1
            while j<limit and code[j] in ' \t':j+=1
            # continuation args, `disch := by`, etc can be indented; keep when deeper.
            if j>=limit or code[j]=='\n' or j-i-1<=base:break
        i+=1
    return i

def run(out,archive):
    out.mkdir(parents=True,exist_ok=True)
    files=[]; commands=[]; calls=[]; options=[]; plumbing=[]; documentation=[]; routes=[]
    for path,raw in source_files(PIN):
        text=raw.decode('utf-8'); digest=sha(raw)
        if not path.endswith('.lean'):
            if path.endswith(('.md','.rst','.txt')):
                for m in TARGET.finditer(text):documentation.append({'path':path,'line':text.count('\n',0,m.start())+1,'token':m[0],'classification':'non_Lean_text'})
            continue
        code,syntax=lexer.masks(text); starts=lexer.command_starts(syntax)
        if not starts or starts[0]>0: starts.insert(0,0)
        starts.append(len(text)); line_starts=[0]+[m.end() for m in re.finditer('\n',text)]
        byte=[0]; total=0
        for c in text:total+=len(c.encode('utf-8'));byte.append(total)
        line=lambda p:bisect.bisect_right(line_starts,p)
        imports=re.findall(r'^(?:(?:public|private)\s+)?import\s+([^\n]+)',syntax,re.M)
        file_record={'path':path,'sha256':digest,'bytes':len(raw),'module':path[:-5].replace('/','.'),'imports':imports,'target_token_count':0}
        files.append(file_record)
        # Source namespace/section stack, not elaborated namespace resolution.
        scopes=[]; inherited={}; saved=[]; command_rows=[]
        for ci,(a,b) in enumerate(zip(starts,starts[1:])):
            chunk=syntax[a:b]; original=text[a:b]; stripped=chunk.strip()
            ns=re.match(r'namespace\s+(\S+)',stripped); sec=re.match(r'section(?:\s+(\S+))?',stripped)
            if re.match(r'end\b',stripped) and saved:
                scopes,inherited=saved.pop()
            namespace='.'.join(x[1] for x in scopes if x[0]=='namespace')
            # Skip option/open prefixes when choosing declaration; macros need manual confirmation.
            d=DECL.search(chunk)
            decl_name=d[2] if d and d[1] not in ('example','macro_rules','elab_rules','syntax','macro','elab') else None
            name=(namespace+'.' if namespace and decl_name and not decl_name.startswith('_root_.') else '')+(decl_name or '')
            command_id=f'{digest}:{path}:{byte[a]}-{byte[b]}:command'
            row={'id':command_id,'path':path,'start_byte':byte[a],'end_byte':byte[b],'start_line':line(a),'end_line':line(max(a,b-1)),
                 'source_sha256':digest,'command_sha256':sha(original.encode()),'text':original,'lexical_namespace':namespace,
                 'declaration_kind':d[1] if d else None,'lexical_declaration':name or None,'private':bool(re.search(r'\bprivate\s+(?:theorem|lemma|def|instance|abbrev|opaque)',chunk[:d.end()] if d else '')),
                 'context_confidence':'repository top-level command scanner; not parsed or elaborated',
                 'inherited_source_options':dict(inherited),'source_options':[],'target_ids':[],'plumbing_ids':[]}
            for om in OPTION.finditer(chunk):
                p=a+om.start(); opt={'id':f'{digest}:{path}:{byte[p]}-{byte[a+om.end()]}:option','path':path,'line':line(p),'option':om[1],'value_text':om[2],'has_in':bool(om[3]),'command_id':command_id,
                    'scope_class':'command-prefix' if om[3] and not chunk[:om.start()].strip() else ('source-setting' if not om[3] and not chunk[:om.start()].strip() else 'nested-unresolved'),
                    'effective_elaborated_value':None,'raised_relative_to_default':'not inferred'}
                options.append(opt);row['source_options'].append(opt['id'])
                if opt['scope_class']=='source-setting':inherited[om[1]]={'value_text':om[2],'line':line(p),'scope':'lexical section/namespace tracking'}
            if ns or sec:
                saved.append((list(scopes),dict(inherited)));scopes.append(('namespace' if ns else 'section',(ns or sec)[1] or ''))
            command_rows.append(row);commands.append(row)
        for m in TARGET.finditer(syntax):
            p=m.start();ci=bisect.bisect_right(starts,p)-1;row=command_rows[ci];a,b=starts[ci:ci+2]
            end=candidate_end(syntax,p,b);cls=classify(syntax,p,syntax[a:b]);tid=f'{digest}:{path}:{byte[p]}-{byte[m.end()]}:{m[1]}'
            r={'call_id':tid,'call_token':'c'+sha(tid.encode())[:16],'pin':PIN,'path':path,'module':file_record['module'],'source_sha256':digest,
                'byte_start':byte[p],'byte_end':byte[m.end()],'line':line(p),'column':p-line_starts[line(p)-1]+1,'tactic':m[1],
                'classification':cls,'command_id':row['id'],'lexical_declaration':row['lexical_declaration'],'declaration_kind':row['declaration_kind'],
                'token_text':m[0],'candidate_syntax_text':text[p:end],'candidate_syntax_end_byte':byte[end],
                'syntax_kind':None,'syntax_extent_confidence':'lexical balanced delimiters/indentation; command text retained for parser follow-up',
                'parser_confirmed':False,'inherited_source_options':row['inherited_source_options'],'command_option_ids':row['source_options'],
                'effective_budget':None,'dynamic_current_pin':None,'semantic_workaround_status':'unclassified; source composition is not failure evidence',
                'url':f'https://github.com/cslib-community/complexitylib/blob/{PIN}/{path}#L{line(p)}'}
            calls.append(r);row['target_ids'].append(tid);file_record['target_token_count']+=1
        for m in PLUMB.finditer(syntax):
            p=m.start();ci=bisect.bisect_right(starts,p)-1;row=command_rows[ci];pid=f'{digest}:{path}:{byte[p]}-{byte[m.end()]}:plumbing'
            plumbing.append({'id':pid,'path':path,'line':line(p),'byte_start':byte[p],'byte_end':byte[m.end()],'text':m[0],
                'command_id':row['id'],'lexical_declaration':row['lexical_declaration'],'classification':'lexical proof-plumbing occurrence; may be ordinary mathematical operation','evidence_of_workaround':None})
            row['plumbing_ids'].append(pid)
    # Preserve historical artifacts by immutable reference/hash. Never rewrite their manifests.
    archived=[];historical=[];observations=[];seen=set()
    if archive:
        arc_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=archive,text=True).strip()
        tracked=subprocess.check_output(['git','ls-files','evidence/1155'],cwd=archive,text=True).splitlines()
        for rel in tracked:
            p=archive/rel; raw=p.read_bytes()
            archived.append({'path':rel,'sha256':sha(raw),'bytes':len(raw),'archive_commit':arc_head,'url':f'https://github.com/cslib-community/complexitylib/blob/{arc_head}/{rel}'})
            if p.name=='parsed.json':
                measured=json.loads(raw)
                if isinstance(measured,list):
                    for obs in measured:
                        if isinstance(obs,dict) and 'full_call_id' in obs:
                            observations.append({'artifact':rel, 'artifact_sha256':sha(raw), **obs})
            if p.name!='mapping.json':continue
            data=json.loads(raw)
            def visit(x):
                if isinstance(x,dict):
                    if 'call_id' in x and 'original_path' in x and x['call_id'] not in seen:
                        seen.add(x['call_id']);historical.append({'mapping_path':rel,**x})
                    for v in x.values():visit(v)
                elif isinstance(x,list):
                    for v in x:visit(v)
            visit(data)
    current={r['call_id']:r for r in calls};by_path=collections.defaultdict(list)
    for r in calls:by_path[r['path']].append(r)
    joins=[]
    observation_index=collections.defaultdict(list)
    for obs in observations:observation_index[obs['full_call_id']].append(obs)
    for h in historical:
        exact=current.get(h['call_id']);path=h['original_path'];samefile=next((f['sha256']==h.get('original_sha256') for f in files if f['path']==path),False)
        joins.append({'historical_call_id':h['call_id'],'historical_call_token':h.get('call_token'),'mapping_path':h['mapping_path'],
            'historical_pin':h.get('pin'),'path':path,'current_call_id':exact['call_id'] if exact else None,
            'join_status':'exact-source-span-kind' if exact else ('same-source-no-matching-token' if samefile else ('changed-source-requires-parser/context-revalidation' if path in by_path else 'no-current-target-token-in-path')),
            'archived_observation_artifacts':sorted({o['artifact'] for o in observation_index[h['call_id']]}), 'historical_expected':h.get('expected'),'historical_case':h.get('case'),'runtime_transferred':False,
            'note':'Mapping describes selected source only; consult archived results/events for actual execution and freshness. No current timing inferred.'})
    # Source-selected limits are independently distinguished from actual elaborator state.
    opt_index={o['id']:o for o in options}
    for r in calls:
        selected=r['inherited_source_options'].get('maxHeartbeats')
        prefixes=[opt_index[x] for x in r['command_option_ids'] if opt_index[x]['option']=='maxHeartbeats' and opt_index[x]['scope_class']=='command-prefix']
        if prefixes:selected=prefixes[-1]
        r['source_selected_heartbeat_limit']={'value_text':selected['value_text'] if selected else '200000',
            'basis':'source set_option' if selected else 'Lean v4.36.0-rc1 CoreM maxHeartbeats default; lakefile has no override',
            'directive_id':selected.get('id') if selected else None,
            'runtime_confirmed':False,'shared_budget_unit':r['command_id'],
            'qualification':'Per-command source choice; actual CLI/elaborator inherited state and consumption require runtime evidence.'}
        r['historical_exact_observations']=[{'artifact':o['artifact'],'run_id':o.get('run_id'),'status':o.get('status'),'goals_after':o.get('goals_after')} for o in observation_index[r['call_id']]]
    for c in commands:
        if c['path'].startswith('Complexity/Tactic/') and re.search(r'\b(?:evalTactic|aesop|funProp|polytime|ppt)\b',c['text']):
            routes.append({'command_id':c['id'],'path':c['path'],'line':c['start_line'],'lexical_declaration':c['lexical_declaration'],
                'classification':'automation implementation/forwarding source; not additional authored-call count',
                'references':sorted(set(re.findall(r'\b(?:evalTactic|aesop|funProp|polytime|ppt|polytime[A-Z]\w*|ppt[A-Z]\w*)\b',c['text'])))})
    all_command_count=len(commands)
    commands=[c for c in commands if c['target_ids'] or c['plumbing_ids'] or c['source_options'] or any(rt['command_id']==c['id'] for rt in routes)]
    ids=[r['call_id'] for r in calls];tokens=[r['call_token'] for r in calls]
    assert len(ids)==len(set(ids));assert len(tokens)==len(set(tokens))
    counts=collections.Counter(r['classification'] for r in calls)
    summary={'pin':PIN,'archive_pin':arc_head if archive else None,'source_roots':ROOTS,'lean_files':len(files),'all_exact_code_tokens':len(calls),
        'by_classification':dict(counts),'by_root_tactic':dict(collections.Counter(r['path'].split('/')[0]+':'+r['tactic'] for r in calls)),
        'options':len(options),'option_scope_classes':dict(collections.Counter(r['scope_class'] for r in options)),
        'plumbing_occurrences':len(plumbing),'plumbing_classifications_are_semantic':False,'all_source_commands':all_command_count,'indexed_commands_with_context':len(commands),
        'historical_selected_source_calls':len(joins),'historical_join_status':dict(collections.Counter(j['join_status'] for j in joins)),
        'current_pin_calls_measured_by_this_survey':0,'archived_parsed_observations':len(observations),'current_source_calls_with_exact_historical_observation':sum(bool(r['historical_exact_observations']) for r in calls),'parser_confirmed_calls':0,
        'limits':['Complete lexical target-token accounting, not complete Lean AST enumeration. Macro-generated and alias invocations require parser/runtime forwarding.',
                  'Candidate syntax extents and declaration/namespace contexts are source heuristics; full original command is provided for auditable correction.',
                  'Effective elaborator options and shared heartbeat consumption are not derivable from source alone.',
                  'All composition/fallback occurrences are lexical; no workaround, raised-budget necessity, successful fallback or causal regression inferred.',
                  'Historical selected-source maps are joined exactly or explicitly unmatched; measurements remain at original pins.']}
    for name,data in [('files',files),('commands',commands),('all-target-tokens',calls),('options',options),('proof-plumbing',plumbing),('documentation-tokens',documentation),('archived-artifacts',archived),('dynamic-source-join',joins),('automation-routes',routes),('archived-observations',observations),('summary',summary)]:dump(out/(name+'.json'),data)
    print(json.dumps(summary,indent=2))
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=pathlib.Path,default=HERE/'index');ap.add_argument('--archive',type=pathlib.Path);args=ap.parse_args();run(args.output,args.archive)
