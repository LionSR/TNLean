import pathlib,json,subprocess,os,time,datetime,fcntl,signal,shutil,hashlib,sys
r=pathlib.Path('/workspace/tn-interaction-integration');o=pathlib.Path('/workspace/reviews/interaction-peps-remaining');shared=pathlib.Path('/workspace/reviews/interaction-shared-validation');overlay=shared/'olean';warm=pathlib.Path('/workspace/tn-pin729-other');q=warm/'.lake/packages/qiclean';head='dccc85e5607077b51822664e9d475287d300d607';pin='729428582b78ab7529b3796099193649f947354a'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()==head
lock=(shared/'validation.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
plans=json.loads((o/'plan.json').read_text());imports=json.loads((o/'imports.json').read_text());manifest=json.loads((r/'lake-manifest.json').read_text());packages={}
for p in manifest['packages']:
 root=warm/'.lake/packages'/p['name']
 if root.exists() and p['type']=='git':
  actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip();assert actual==p['rev'],p['name'];packages[p['name']]=actual
assert packages['qiclean']==pin
paths=[overlay,warm/'.lake/build/lib/lean',q/'.lake/build/lib/lean',pathlib.Path('/workspace/elan/toolchains/leanprover--lean4---v4.36.0-rc1/lib/lean')]+[p/'.lake/build/lib/lean' for p in (warm/'.lake/packages').iterdir() if p.name!='qiclean'];env=os.environ.copy();env.update(LEAN_PATH=':'.join(map(str,paths)),LEAN_NUM_THREADS='2');lean='/workspace/elan/toolchains/leanprover--lean4---v4.36.0-rc1/bin/lean';flags=['-DautoImplicit=false','-DrelaxedAutoImplicit=false','-Dpp.unicode.fun=true','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true'];records=[json.loads(x) for x in (shared/'results.jsonl').read_text().splitlines()];mine=[json.loads(x) for x in (o/'results.jsonl').read_text().splitlines()] if (o/'results.jsonl').exists() else []
def sh(b):return hashlib.sha256(b).hexdigest()
def src(m):return (q if m.startswith('QICLean.') else r)/(m.replace('.','/')+'.lean')
sources={m:sh(src(m).read_bytes()) for m in imports}
(o/'source-hashes.json').write_text(json.dumps({'head':head,'packages':packages,'sources':sources},indent=2)+'\n')
closurememo={}
def closure(m):
 if m not in closurememo:
  closurememo[m]={m}
  for d in imports.get(m,[]):closurememo[m]|=closure(d)
 return closurememo[m]
gitmaps={}
def tree(h):
 if h not in gitmaps:
  raw=subprocess.check_output(['git','ls-tree','-r',h,'--','TNLean'],cwd=r,text=True);gitmaps[h]={line.split('\t',1)[1]:line.split()[2] for line in raw.splitlines()}
 return gitmaps[h]
current=tree(head)
def unchanged(m,old):
 return all(current.get(d.replace('.','/')+'.lean')==tree(old).get(d.replace('.','/')+'.lean') for d in closure(m) if d.startswith('TNLean.'))
valid=set()
for x in records:
 if x['phase']=='compile' and x['exit_code']==0 and x['pin']==pin and x['module'] in imports and unchanged(x['module'],x['head']):valid.add(x['module'])
for x in mine:
 if x.get('phase')=='compile' and x['exit_code']==0:valid.add(x['module'])
initialvalid=sorted(valid);(o/'reused-record-modules.json').write_text(json.dumps(initialvalid,indent=2)+'\n')
failed={x['module'] for x in mine if x.get('phase')=='compile' and x['exit_code']!=0}
done={(x['module'],x.get('phase')) for x in mine}
artifacts={}
def artifact(m):
 rel=m.replace('.','/')+'.olean'
 for p in paths:
  f=p/rel
  if f.exists():
   st=f.stat();key=str(f);stamp=[st.st_size,st.st_mtime_ns]
   if key not in artifacts or artifacts[key]['stamp']!=stamp:artifacts[key]={'stamp':stamp,'sha256':sh(f.read_bytes())}
   return artifacts[key]['sha256']
 raise RuntimeError('missing artifact '+m)
def record(x):
 with (o/'results.jsonl').open('a') as f:f.write(json.dumps(x)+'\n')
 print(x['module'],x['phase'],x['exit_code'],round(x.get('seconds',0),3),flush=True)
def run(m,phase):
 if shutil.disk_usage(r).free<2**30:raise SystemExit('1 GiB disk guard')
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip()==head
 for d in closure(m):
  if d in sources:assert sh(src(d).read_bytes())==sources[d], 'dependency source changed: '+d
 dependency_hashes={d:artifact(d) for d in sorted(closure(m)-{m})}
 fingerprint=sh(json.dumps({'sources':{d:sources[d] for d in sorted(closure(m)) if d in sources},'artifacts':dependency_hashes,'packages':packages},sort_keys=True).encode())
 root=q if m.startswith('QICLean.') else r;p=m.replace('.','/')+'.lean';cmd=[lean,*flags]
 if phase=='compile':
  dest=overlay/(m.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.is_symlink():dest.unlink()
  cmd+=['-o',str(dest)]
 else:cmd+=['-DwarningAsError=true']
 cmd+=[p];start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic();log=o/f'{time.time_ns()}.log'
 with log.open('w') as f:
  proc=subprocess.Popen(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
  try:rc=proc.wait(timeout=180)
  except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGTERM);proc.wait();rc=124
 x=dict(head=head,pin=pin,module=m,phase=phase,command=cmd,cwd=str(root),start=start,seconds=time.monotonic()-t,exit_code=rc,pid=proc.pid,pgid=proc.pid,source_sha256=sources[m],dependency_fingerprint=fingerprint,log=log.name)
 record(x);done.add((m,phase))
 if phase=='compile':
  (valid if rc==0 else failed).add(m)
 if rc:print(log.read_text()[:4000],flush=True)
 return rc
limit=int(sys.argv[1]);priority={p[:-5].replace('/','.') for p in (o/'snake-priority46.txt').read_text().splitlines()};targets=sorted(plans,key=lambda t:(t not in priority,len(set(plans[t])-valid),t));attempted=0
for target in targets:
 if (target,'strict') in done or (target,'blocked') in done:continue
 required=[m for m in plans[target] if m not in valid]
 if any(m.startswith('TNLean.MPS.') for m in required):record(dict(head=head,pin=pin,module=target,phase='blocked',exit_code=125,reason='MPS lane dependency'));continue
 if len(required)>limit:continue
 attempted+=1
 for m in required:
  if m in failed:break
  if m not in valid and run(m,'compile'):break
 if any(m in failed for m in plans[target]):record(dict(head=head,pin=pin,module=target,phase='blocked',exit_code=125,reason='failed compilation dependency'));continue
 run(target,'strict')
(o/'artifact-hashes.json').write_text(json.dumps(artifacts,indent=2)+'\n')
print('FINISHED batch targets',attempted,'free bytes',shutil.disk_usage(r).free,flush=True)
