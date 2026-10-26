#!/usr/bin/env python3
"""Fixed manually inspected subset: git/source artifacts only, never runs Lean."""
import pathlib,subprocess,json,hashlib,re
out=pathlib.Path(__file__).resolve().parent
pin='3a6d770645c1217689da774f519cd785c253d8a2'
selected=[('addtrivial','Computability/PCP/Encoded/AddTrivial'),('amplification','Computability/PCP/Encoded/Amplification'),('amplification-enumeration','Computability/PCP/Encoded/Amplification/Enumeration'),('constraints','Computability/PCP/Encoded/Constraints'),('preprocess','Computability/PCP/Encoded/Preprocess'),('exact-three-sat','Computability/Complexity/Problems/ExactThreeSAT'),('partition','Computability/Complexity/Problems/Partition'),('generator-padding','Crypto/Computational/GeneratorPadding'),('prediction','Crypto/Computational/Prediction'),('extraction-schedule','Crypto/Computational/Pseudoentropy/ExtractionSchedule'),('repeated-extraction','Crypto/Computational/Pseudoentropy/RepeatedExtraction'),('word-seed-extraction','Crypto/Computational/Pseudoentropy/WordSeedExtraction')]
kinds={'polytime':'Cslib.Tactic.PolyTime.tacticPolytime','fun_prop':'Mathlib.Meta.FunProp.funPropTacStx','ppt':'Cslib.Tactic.PPT.tacticPpt'}
files=[];tokens=set();counts={k:0 for k in kinds}
for case,stem in selected:
 path='Complexity/'+stem+'.lean';raw=subprocess.check_output(['git','show',pin+':'+path]);text=raw.decode();sha=hashlib.sha256(raw).hexdigest()
 matches=list(re.finditer(r'(?m)^  (polytime|fun_prop|ppt)$',text))
 assert matches and '`(' not in text
 assert not re.search(r'(?m)^(?:scoped\s+)?(?:notation|infix[lr]?|prefix|postfix|macro|macro_rules|elab|elab_rules|syntax)\b',text)
 reduced=re.sub(r'@\[fun_prop\]','',text)
 assert len(re.findall(r'\b(?:polytime|fun_prop|ppt)\b',reduced))==len(matches)
 assert not re.findall(r'(?m)^\s*set_option.*$',text),'new option context needs review'
 calls=[]
 for m in matches:
  tactic=m[1];start=len(text[:m.start(1)].encode());end=start+len(tactic)
  assert raw[start:end]==tactic.encode()
  owners=list(re.finditer(r'(?m)^(?:private\s+)?(?:theorem|lemma|def|noncomputable def)\s+([^\s({:]+)',text[:m.start()]))
  assert owners
  label=owners[-1][1];ident=f'{sha}:{path}:{start}-{end}:{tactic}';token='c'+hashlib.sha256(ident.encode()).hexdigest()[:16]
  assert token not in tokens;tokens.add(token);counts[tactic]+=1
  calls.append(dict(case=label,call_id=ident,call_token=token,tactic=tactic,expected_kind=kinds[tactic],pin=pin,original_path=path,original_sha256=sha,original_byte_start=start,original_byte_end=end,original_line=text[:m.start(1)].count('\n')+1,original_text=tactic,expected='returned',authored_selection='manually inspected standalone theorem-body line'))
 imports=[l for l in text.splitlines() if l.startswith(('import ','public import '))]
 assert imports and re.search(r'(?m)^(?:theorem|def|noncomputable def|structure|inductive)\s',text),'not an aggregate-only import file'
 anchor=imports[-1]+'\n';assert text.count(anchor)==1
 added='import Diag1155.Wrapper\n';imported=text.replace(anchor,anchor+added,1)
 iterator=iter(calls)
 wrapped=re.sub(r'(?m)^  (polytime|fun_prop|ppt)$',lambda m:'  diag1155_call '+json.dumps(next(iterator)['call_token'])+' => '+m[1],imported)
 restored=re.sub(r'(?m)^  diag1155_call "c[0-9a-f]{16}" => (polytime|fun_prop|ppt)$',r'  \1',wrapped)
 assert restored==imported and imported.replace(added,'',1)==text
 variants={'baseline':text,'import-only':imported,'wrapped':wrapped}
 for mode,source in variants.items():
  dest=out/case/mode/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(source)
 assert (out/case/'baseline'/path).read_bytes()==raw
 files.append(dict(case=case,path=path,module_name=path[:-5].replace('/','.'),source_sha256=sha,calls=calls,original_imports=imports,variant_sha256={m:hashlib.sha256(s.encode()).hexdigest() for m,s in variants.items()},explicit_private_declarations=len(re.findall(r'(?m)^private\s',text)),private_declaration_lines=[i for i,l in enumerate(text.splitlines(),1) if l.startswith('private ')],original_option_directives=[],namespace_section_lines=[{'line':i,'text':l} for i,l in enumerate(text.splitlines(),1) if re.match(r'^(?:namespace|end|section|variable)\b',l)],source_declaration_header_lines=[{'line':i,'text':l} for i,l in enumerate(text.splitlines(),1) if re.match(r'^(?:private\s+)?(?:(?:noncomputable|opaque)\s+)?(?:theorem|lemma|def|abbrev|structure|class|inductive)\s',l)],declaration_expectation='exact source headers/bodies preserved; future actual native declaration set must match baseline across modes; no pre-elaboration native inventory claim',default_user_heartbeat_limit=200000,source_lines=len(text.splitlines()),all_non_target_code='byte preserved and individually unmeasured'))
assert len(files)==12<=25 and sum(counts.values())==20<=100
impl=out.parent/'wrapper-compact-3a6d/Wrapper.lean'
root_options=json.loads((out.parent/'cloud-source-prep-3a6d/acceptance-config.json').read_text())['options_from_original_lakefile']
mapping=dict(state='SOURCE_MAPPING_PREPARATION_ONLY',source_pin=pin,selection_basis='explicit shortlist from existing67c6census, actual selected3a6sources verified; no global recount',implementation_sha256=hashlib.sha256(impl.read_bytes()).hexdigest(),files=files,selected_files=12,selected_calls=20,tactic_counts=counts,parent_limits={'files':25,'calls':100},unselected='deferred/unmeasured; no eligibility or coverage-percentage claim')
(out/'mapping.json').write_text(json.dumps(mapping,indent=2)+'\n')
config=dict(state='PREPARED_NOT_EXECUTED',source_pin=pin,mapping_sha256=hashlib.sha256((out/'mapping.json').read_bytes()).hexdigest(),implementation_sha256=mapping['implementation_sha256'],required_modes=['baseline','import-only','wrapped'],package_options=root_options,user_limit=200000,files=files,expected_calls=[c for f in files for c in f['calls']],expected_commands=36,expected_events=40)
(out/'config.json').write_text(json.dumps(config,indent=2)+'\n')
print(json.dumps({'selected_files':len(files),'authored_calls':sum(counts.values()),'tactic_counts':counts,'Lean_runs':0},indent=2))
