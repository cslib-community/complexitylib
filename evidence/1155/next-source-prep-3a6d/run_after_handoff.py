#!/usr/bin/env python3
"""Exactly nine processes for the fixed selected batch, stop at first mismatch."""
import argparse,hashlib,json,os,pathlib,subprocess,time,uuid
p=argparse.ArgumentParser();p.add_argument('checkout');a=p.parse_args()
out=pathlib.Path(__file__).resolve().parent;root=pathlib.Path(a.checkout).resolve()
if (out/'results.json').exists() or (out/'runtime-sidecar.json').exists():raise SystemExit('Refusing archive overwrite')
config=json.loads((out/'config.json').read_text());mb=(out/'mapping.json').read_bytes()
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==config['source_pin']
assert subprocess.run(['git','diff','--quiet'],cwd=root).returncode==0
assert hashlib.sha256((root/'Diag1155/Wrapper.lean').read_bytes()).hexdigest()==config['implementation_sha256']
run='limited-3a6d-'+str(uuid.uuid4())
side=dict(run_id=run,source_pin=config['source_pin'],mapping_sha256=hashlib.sha256(mb).hexdigest(),implementation_sha256=config['implementation_sha256'],calls=config['expected_calls'])
(out/'runtime-sidecar.json').write_text(json.dumps(side,indent=2)+'\n');digest=hashlib.sha256((out/'runtime-sidecar.json').read_bytes()).hexdigest()
opts=['-DwarningAsError=true']+[f'-D{k}={str(v).lower()}' for k,v in config['package_options'].items()]
private=root/'.lake/diag1155/limited';private.mkdir(parents=True,exist_ok=True)
results=[];contexts={}
for file in config['files']:
 case=file['case'];contexts[case]={}
 for mode in config['required_modes']:
  variant=out/case/mode;source=variant/file['path'];sourcehash=hashlib.sha256(source.read_bytes()).hexdigest()
  assert sourcehash==file['variant_sha256'][mode]
  telemetry=out/f'{case}-{mode}.events.jsonl';assert not telemetry.exists()
  ilean=private/f'{case}-{mode}.ilean'
  cmd=['lake','env','lean',*opts,'--root='+str(variant),'-i',str(ilean),str(source)]
  env=os.environ.copy();env.update(DIAG1155_OUTPUT=str(telemetry),DIAG1155_RUN_ID=run,DIAG1155_SIDECAR_SHA256=digest)
  start=time.monotonic()
  with (out/f'{case}-{mode}.log').open('w') as log:r=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT)
  row=dict(case=case,mode=mode,returncode=r.returncode,process_wall_seconds=time.monotonic()-start,command=cmd,run_id=run,sidecar_sha256=digest,source_sha256=sourcehash,module_name=None,context_verified=False)
  if r.returncode==0:
   data=json.loads(ilean.read_text());row['module_name']=data['module']
   context=dict(module=data['module'],directImports=data['directImports'],source_declaration_names=sorted(data['decls']),private_ilean_sha256=hashlib.sha256(ilean.read_bytes()).hexdigest(),compiled_output_published=False)
   contexts[case][mode]=context
   assert data['module']==file['module_name'],'actual module mismatch'
   if mode=='baseline':assert [x[0] for x in data['directImports']]==[l.split('import ',1)[1] for l in file['original_imports']]
   else:
    assert data['directImports'][:-1]==contexts[case]['baseline']['directImports'],'original import context mismatch'
    assert data['directImports'][-1][0]=='Diag1155.Wrapper'
    assert context['source_declaration_names']==contexts[case]['baseline']['source_declaration_names'],'source declaration context mismatch'
   row['context_verified']=True
  results.append(row)
  (out/'results.json').write_text(json.dumps(results,indent=2)+'\n');(out/'actual-contexts.json').write_text(json.dumps(contexts,indent=2)+'\n')
  if r.returncode:print(json.dumps(results,indent=2));raise SystemExit(r.returncode)
print(json.dumps([dict(case=x['case'],mode=x['mode'],exit=x['returncode'],context=x['context_verified']) for x in results],indent=2))
