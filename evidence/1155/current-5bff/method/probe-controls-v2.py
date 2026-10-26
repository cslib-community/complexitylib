from pathlib import Path
import subprocess,json,hashlib,time,os,tomllib,uuid
srcpath=Path('/home/samuel/Code/complexitylib-codex/automation-census-1155/evidence/1155/current-5bff/method/Controls.lean');src=srcpath.read_bytes();out=Path('pilot1155-current-controls-v2');out.mkdir();pin=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();assert pin=='5bffdf2f248bbbfddea6039ee25a953616dff15b'
h=subprocess.run(['lake','env','lean','--run','Diag1155/HeaderPositions.lean'],input=json.dumps([str(srcpath)]),text=True,capture_output=True,check=True);offset=json.loads(h.stdout)[0]['header_end_byte'];opts=[]
def flatten(d,p=''):
 for k,v in d.items():
  name=p+'.'+k if p else k
  if isinstance(v,dict):flatten(v,name)
  else:opts.append('-D'+name+'='+str(v).lower())
flatten(tomllib.load(open('lakefile.toml','rb'))['leanOptions']);rows=[];run='method-5bff-'+str(uuid.uuid4());side={'source_pin':pin,'source_sha256':hashlib.sha256(src).hexdigest(),'source_path':'MethodControls.lean','header_end_byte':offset,'run_id':run};(out/'sidecar.json').write_text(json.dumps(side,indent=2)+'\n');digest=hashlib.sha256((out/'sidecar.json').read_bytes()).hexdigest()
for mode in ['baseline','import-only','measured']:
 root=out/mode;root.mkdir();insert=b'' if mode=='baseline' else b'\nimport Diag1155.Measure\n';text=src[:offset]+insert+src[offset:]
 # A command belongs after the complete header, not among imports.
 if mode=='measured':text=src[:offset]+insert+b'\ndiag1155_install\n'+src[offset:]
 assert text[:offset]+text[offset+len(insert)+(len(b'\ndiag1155_install\n') if mode=='measured' else 0):]==src
 path=root/'MethodControls.lean';path.write_bytes(text);env=os.environ.copy();env.update(LEAN_NUM_THREADS='2',DIAG1155_OUTPUT=str((out/(mode+'.jsonl')).resolve()),DIAG1155_RUN_ID=run,DIAG1155_PROVENANCE=digest)
 cmd=['lake','env','lean','-DwarningAsError=true',*opts,'--root='+str(root.resolve()),'-i',str((out/(mode+'.ilean')).resolve()),str(path.resolve())];t=time.monotonic()
 with (out/(mode+'.log')).open('w') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT)
 rows.append({'mode':mode,'exit':r.returncode,'wall':time.monotonic()-t,'command':cmd,'insertion_bytes':len(insert)+(len(b'\ndiag1155_install\n') if mode=='measured' else 0)});(out/'results.json').write_text(json.dumps(rows,indent=2)+'\n');print(mode,r.returncode,flush=True)
 if r.returncode:break
