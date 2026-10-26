#!/usr/bin/env python3
"""One-off #1155 collector. prepare is source-only; run needs the builder lease.
No production proofs, tactic options, installed packages or caches are rewritten.
"""
import argparse,hashlib,json,os,pathlib,subprocess,time,uuid,tomllib,signal,threading
from concurrent.futures import ThreadPoolExecutor,as_completed
PIN='5bffdf2f248bbbfddea6039ee25a953616dff15b'
STATIC='5bc08fe7a82eb89dc744d443f190612f5d06e091'
def sha(b):return hashlib.sha256(b).hexdigest()
def dump(p,v):
 p.parent.mkdir(parents=True,exist_ok=True);tmp=p.with_name(p.name+'.tmp');tmp.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n');os.replace(tmp,p)
def git(root,*a):return subprocess.check_output(['git',*a],cwd=root)
def flatten(d,p=''):
 out={}
 for k,v in d.items():
  key=p+'.'+k if p else k
  if isinstance(v,dict):out.update(flatten(v,key))
  else:out[key]=v
 return out
def source_options(root,path):
 guide=path.startswith('guide/');cfg=tomllib.loads((root/('guide/lakefile.toml' if guide else 'lakefile.toml')).read_text());opts=flatten(cfg.get('leanOptions',{}))
 libname='ComplexityGuide' if guide else 'ComplexityAbstracts' if path.startswith('abstracts/') else path.split('/')[0]
 for lib in cfg.get('lean_lib',[]):
  if lib['name']==libname:opts.update(flatten(lib.get('leanOptions',{})))
 return opts

def prepare(root,static,out):
 if out.exists():raise ValueError('Refusing overwrite')
 assert git(root,'rev-parse','HEAD').decode().strip()==PIN
 files=json.loads((static/'index/files.json').read_text());tokens=json.loads((static/'index/all-target-tokens.json').read_text());selected={x['path'] for x in tokens if x['classification']=='authored_tactic_candidate'}
 plan=[]
 for f in files:
  path=f['path']
  if path not in selected:continue
  raw=git(root,'show',PIN+':'+path);assert sha(raw)==f['sha256']
  prefix='guide/' if path.startswith('guide/') else 'abstracts/' if path.startswith('abstracts/') else ''
  dest=out/'originals'/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw)
  plan.append({'file_id':sha(path.encode())[:16],'path':path,'sha256':sha(raw),'bytes':len(raw),
   'static_module_hint':f['module'],'expected_native_module':path[len(prefix):-5].replace('/','.'),
   'source_root_prefix':prefix,'project':'guide' if prefix=='guide/' else '.',
   'original_import_hints':f['imports'],'options':source_options(root,path),
   'candidate_head_ids':[x['call_id'] for x in tokens if x['path']==path and x['classification']=='authored_tactic_candidate']})
 dump(out/'plan.json',{'pin':PIN,'static_source':STATIC,'static_manifests':{n:sha((static/'index'/n).read_bytes()) for n in ['files.json','all-target-tokens.json','commands.json','options.json']},'files':plan,'candidates':sum(len(f['candidate_head_ids']) for f in plan),'state':'PREPARED_NOT_EXECUTED'})
 print(json.dumps({'files':len(plan),'candidates':sum(len(f['candidate_head_ids']) for f in plan)}))

def run(root,out,headers_path,producer,traces,timeout,jobs):
 assert 1<=jobs<=8
 assert git(root,'rev-parse','HEAD').decode().strip()==PIN
 assert subprocess.run(['git','diff','--quiet'],cwd=root).returncode==0
 plan=json.loads((out/'plan.json').read_text());assert plan['pin']==PIN
 headers={r['path']:r for r in json.loads(headers_path.read_text())};assert len(headers)==len(plan['files'])
 for f in plan['files']:
  header=headers[str((out/'originals'/f['path']).resolve())];f['header_end_byte']=header['header_end_byte'];f['install_byte']=header['install_byte']
 modes=['baseline','import-only','measured']+(['traced'] if traces else []);run_id='current-5bff-'+str(uuid.uuid4())
 side={'collector_sha256':sha(pathlib.Path(__file__).read_bytes()),'parser_sha256':sha(pathlib.Path(__file__).with_name('parse-default.py').read_bytes()),'protocol':'original-Lake-options; JSON diagnostics; external Lake-equivalent warning acceptance','run_id':run_id,'source_pin':PIN,'static_source':STATIC,'plan_sha256':sha((out/'plan.json').read_bytes()),'headers_sha256':sha(headers_path.read_bytes()),'producer_sources':{p.name:sha(p.read_bytes()) for p in producer.glob('*.lean')},'private_producer_hashes':{p.name:sha(p.read_bytes()) for p in (root/'.lake/build/lib/lean/Diag1155').glob('Measure*.olean*')},'modes':modes,'external_timeout_seconds':timeout,'budget_not_overridden':True,'trace_flags':['trace.Meta.Tactic.fun_prop=true','trace.aesop=true'] if traces else [],'compiled_outputs_published':False,'parallel_file_pipelines':jobs,'per_process_lean_threads':2}
 if (out/'run-sidecar.json').exists():raise ValueError('Refusing retry/overwrite')
 dump(out/'run-sidecar.json',side);digest=sha((out/'run-sidecar.json').read_bytes());ledger=[]
 lock=threading.Lock();stop=threading.Event();active={}
 def pipeline(f):
  if stop.is_set():return None
  file_rows=[]
  raw=(out/'originals'/f['path']).read_bytes();assert sha(raw)==f['sha256'];offset=f['header_end_byte'];assert 0<=offset<=len(raw)
  for mode in modes:
   if stop.is_set():return None
   mode_root=out/'variants'/f['file_id']/mode;source=mode_root/f['path']
   import_bytes=b'' if mode=='baseline' else b'\nimport Diag1155.Measure\n'
   install_bytes=b'\ndiag1155_install\n' if mode in ('measured','traced') else b''
   install_offset=f['install_byte'];assert offset<=install_offset<=len(raw)
   variant=raw[:offset]+import_bytes+raw[offset:install_offset]+install_bytes+raw[install_offset:]
   recovered=variant[:offset]+variant[offset+len(import_bytes):install_offset+len(import_bytes)]+variant[install_offset+len(import_bytes)+len(install_bytes):]
   assert recovered==raw
   insertion=import_bytes+install_bytes
   source.parent.mkdir(parents=True,exist_ok=True);source.write_bytes(variant);case=out/'runs'/f['file_id'];case.mkdir(parents=True,exist_ok=True)
   events=case/(mode+'.jsonl');log=case/(mode+'.log');assert not events.exists() and not log.exists()
   native=root/'.lake/diag1155/full'/run_id/(f['file_id']+'-'+mode+'.ilean');native.parent.mkdir(parents=True,exist_ok=True)
   cwd=root/f['project'];root_arg=mode_root/f['source_root_prefix'];cmd=['lake','env','lean','--json',*[f'-D{k}={str(v).lower()}' for k,v in f['options'].items()]]
   if mode=='traced':cmd+=['-Dtrace.Meta.Tactic.fun_prop=true','-Dtrace.aesop=true']
   cmd+=['--root='+str(root_arg.resolve()),'-i',str(native.resolve()),str(source.resolve())]
   env=os.environ.copy();env.update(LEAN_NUM_THREADS='2',DIAG1155_OUTPUT=str(events.resolve()),DIAG1155_RUN_ID=run_id,DIAG1155_PROVENANCE=digest)
   assert git(root,'rev-parse','HEAD').decode().strip()==PIN
   for name,h in side['producer_sources'].items():
    assert sha((producer/name).read_bytes())==h
    assert sha((root/'Diag1155'/name).read_bytes())==h
   for name,h in side['private_producer_hashes'].items():
    assert sha((root/'.lake/build/lib/lean/Diag1155'/name).read_bytes())==h
   # Shared-host pressure pauses new launches rather than changing original proof limits.
   while int(next(x.split()[1] for x in pathlib.Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))<8*1024*1024:
    if stop.is_set():return None
    time.sleep(1)
   start=time.monotonic();timed_out=False
   with log.open('w') as stream:
    process=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
    with lock:
     active[f['file_id']]={'path':f['path'],'mode':mode,'pid':process.pid,'process_group':process.pid,'command':cmd}
     dump(out/'active.json',active)
    try:code=process.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
     timed_out=True;code=None
     # Kill only the process group created for THIS owned command, including Lean children.
     os.killpg(process.pid,signal.SIGTERM)
     try:process.wait(timeout=5)
     except subprocess.TimeoutExpired:
      os.killpg(process.pid,signal.SIGKILL);process.wait()
     try:os.killpg(process.pid,signal.SIGKILL)
     except ProcessLookupError:pass
    except BaseException:
     try:os.killpg(process.pid,signal.SIGTERM)
     except ProcessLookupError:pass
     try:process.wait(timeout=5)
     except subprocess.TimeoutExpired:
      os.killpg(process.pid,signal.SIGKILL);process.wait()
     raise
    finally:
     with lock:
      active.pop(f['file_id'],None);dump(out/'active.json',active)
   elapsed=time.monotonic()-start
   diagnostics=[]
   for line in log.read_text().splitlines():
    try:message=json.loads(line)
    except (ValueError,TypeError):continue
    if isinstance(message,dict) and all(k in message for k in ('fileName','pos','severity','data','kind')) and not message.get('isSilent',False):diagnostics.append(message)
   assert all(m['severity'] in ('information','warning','error') for m in diagnostics)
   warning_failure=any(m['severity'] in ('warning','error') for m in diagnostics)
   row={'external_warning_acceptance':not warning_failure,'diagnostic_severities':dict(__import__('collections').Counter(m['severity'] for m in diagnostics)),'file_id':f['file_id'],'path':f['path'],'mode':mode,'run_id':run_id,'provenance':digest,'returncode':code,'external_timeout':timed_out,'process_wall_seconds':elapsed,'command':cmd,'cwd':str(cwd),'source_sha256':sha(variant),'original_sha256':f['sha256'],'insertion_offset':offset,'insertion_bytes':len(insertion),'insertions':[{'original_byte':offset,'bytes':len(import_bytes)},{'original_byte':install_offset,'bytes':len(install_bytes)}],'actual_context':None,'context_error':None}
   if native.exists() and code==0:
    data=json.loads(native.read_text());context={'module':data['module'],'directImports':data['directImports'],'source_declaration_names':sorted(data['decls']),'private_ilean_sha256':sha(native.read_bytes()),'outputs_published':False};row['actual_context']=context
    if context['module']!=f['expected_native_module']:row['context_error']='module mismatch'
    prior=next((x for x in file_rows if x['mode']=='baseline'),None)
    if mode!='baseline' and prior and prior['actual_context']:
     base=prior['actual_context']
     if context['source_declaration_names']!=base['source_declaration_names']:row['context_error']='source declaration mismatch'
     if context['directImports'][:-1]!=base['directImports'] or context['directImports'][-1][0]!='Diag1155.Measure':row['context_error']='original import mismatch'
   elif code==0:row['context_error']='missing native context'
   file_rows.append(row)
   with lock:
    ledger.append(row);dump(out/'commands.json',ledger)
   print(json.dumps({'path':f['path'],'mode':mode,'exit':code,'context_error':row['context_error']}),flush=True)
   if row['context_error']:
    stop.set()
    with lock:dump(out/'STOPPED.json',{'reason':'native context mismatch; do not retry/repair silently','row':row})
    return 2
   assert source.read_bytes()==variant and sha(git(root,'show',PIN+':'+f['path']))==f['sha256']
  return 0
 with ThreadPoolExecutor(max_workers=jobs) as pool:
  futures=[pool.submit(pipeline,f) for f in plan['files']]
  try:
   for future in as_completed(futures):
    if future.result()==2:stop.set()
  except BaseException:
   stop.set()
   with lock:
    for process in active.values():
     try:os.killpg(process['process_group'],signal.SIGTERM)
     except ProcessLookupError:pass
   raise
 if stop.is_set():return 2
 dump(out/'terminal.json',{'all_processes_terminal':True,'files_attempted':len(plan['files']),'commands':len(ledger),'whole_file_failures':sum(x['returncode']!=0 or not x['external_warning_acceptance'] for x in ledger),'full_completion_claim':False});return 0

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('action',choices=['prepare','run']);p.add_argument('--checkout',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--static',type=pathlib.Path);p.add_argument('--headers',type=pathlib.Path);p.add_argument('--producer',type=pathlib.Path);p.add_argument('--traces',action='store_true');p.add_argument('--timeout',type=int,default=1800);p.add_argument('--jobs',type=int,default=1);a=p.parse_args()
 if a.action=='prepare':prepare(a.checkout.resolve(),a.static.resolve(),a.out.resolve())
 else:raise SystemExit(run(a.checkout.resolve(),a.out.resolve(),a.headers,a.producer,a.traces,a.timeout,a.jobs))
