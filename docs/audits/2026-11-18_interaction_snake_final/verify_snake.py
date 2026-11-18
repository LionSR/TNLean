import pathlib,json,subprocess,os,time,datetime,fcntl,signal,shutil,hashlib
r=pathlib.Path('/workspace/tn-interaction-final'); old=pathlib.Path('/workspace/reviews/interaction-peps-remaining'); out=pathlib.Path(__file__).parent; overlay=pathlib.Path('/workspace/reviews/interaction-final-validation/olean'); warm=pathlib.Path('/workspace/tn-pin729-other');q=warm/'.lake/packages/qiclean';head='42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d';pin='729428582b78ab7529b3796099193649f947354a'
def sha(b):return hashlib.sha256(b).hexdigest()
def write(n,d):(out/n).write_text(json.dumps(d,indent=2)+'\n')
def git(*args,cwd=r):return subprocess.check_output(['git',*args],cwd=cwd,text=True).strip()
assert git('rev-parse','HEAD')==head
assert not git('status','--porcelain')
lock=open('/workspace/reviews/interaction-shared-validation/validation.lock','a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
mods=json.loads((old/'snake-final-gap.json').read_text())['remaining_modules_topological']; imports=json.loads((old/'snake-imports.json').read_text());memo={}
def closure(m):
 if m not in memo:
  memo[m]={m}
  for d in imports.get(m,[]):memo[m]|=closure(d)
 return memo[m]
lean=pathlib.Path('/workspace/elan/toolchains/leanprover--lean4---v4.36.0-rc1/bin/lean');paths=[overlay,pathlib.Path('/workspace/reviews/interaction-shared-validation/olean'),warm/'.lake/build/lib/lean',q/'.lake/build/lib/lean',lean.parent.parent/'lib/lean']+[p/'.lake/build/lib/lean' for p in (warm/'.lake/packages').iterdir() if p.name!='qiclean']
def artifact(m):
 for p in paths:
  f=p/(m.replace('.','/')+'.olean')
  if f.is_file():return dict(path=str(f),sha256=sha(f.read_bytes()))
 return None
packages={p['name']:p['rev'] for p in json.loads((r/'lake-manifest.json').read_text())['packages'] if p['type']=='git'}
for n,h in packages.items():assert git('rev-parse','HEAD',cwd=warm/'.lake/packages'/n)==h
assert packages['qiclean']==pin
sources={m:sha(((q if m.startswith('QICLean.') else r)/(m.replace('.','/')+'.lean')).read_bytes()) for m in closure(mods[-1]) if m.startswith(('TNLean.','QICLean.'))}
missing=sorted(m for m in closure(mods[-1]) if artifact(m) is None);assert set(missing)==set(mods),(missing,mods)
prior=json.loads((old/'source-hashes.json').read_text())['sources']
for m,h in sources.items():
 if m in prior:assert h==prior[m],m
oldart=json.loads((old/'all-dependency-artifacts.json').read_text());checked=0
for m in closure(mods[-1])-set(mods):
 a=artifact(m)
 if m in oldart:assert a['sha256']==oldart[m]['sha256'],m;checked+=1
metadata=dict(head=head,pin=pin,packages=packages,toolchain=(r/'lean-toolchain').read_text().strip(),lean_version=subprocess.check_output([str(lean),'--version'],text=True).strip(),lean_sha256=sha(lean.read_bytes()),manifest_sha256=sha((r/'lake-manifest.json').read_bytes()),sources=sources,allowed_topological=mods,missing=missing,prior_artifact_hashes_rechecked=checked,duplicate_cost_authorized=True,free_bytes=shutil.disk_usage(r).free)
write('preflight.json',metadata)
flags=['-DautoImplicit=false','-DrelaxedAutoImplicit=false','-Dpp.unicode.fun=true','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true'];env=os.environ.copy();env.update(LEAN_PATH=':'.join(map(str,paths)),LEAN_NUM_THREADS='2');results=[]
for m in mods:
 for phase in (['compile','strict'] if m==mods[-1] else ['compile']):
  assert shutil.disk_usage(r).free>=2**30
  assert git('rev-parse','HEAD')==head
  for d in closure(m):
   if d in sources:assert sha(((q if d.startswith('QICLean.') else r)/(d.replace('.','/')+'.lean')).read_bytes())==sources[d]
  deps={d:artifact(d) for d in sorted(closure(m)-{m})};assert all(deps.values())
  fingerprint=dict(sources={d:sources[d] for d in sorted(closure(m)) if d in sources},artifacts=deps,packages=packages,lean_sha256=metadata['lean_sha256']);fingerprint_hash=sha(json.dumps(fingerprint,sort_keys=True).encode());write(fingerprint_hash+'.json',fingerprint)
  cmd=[str(lean),*flags];dest=overlay/(m.replace('.','/')+'.olean')
  if phase=='compile':dest.parent.mkdir(parents=True,exist_ok=True);cmd+=['-o',str(dest)]
  else:cmd+=['-DwarningAsError=true']
  cmd+=[m.replace('.','/')+'.lean'];log=out/(m+'.'+phase+'.log');start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic()
  with log.open('w') as f:
   p=subprocess.Popen(cmd,cwd=r,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
   write('current.json',dict(module=m,phase=phase,pid=p.pid,pgid=p.pid,command=cmd,start=start))
   try:rc=p.wait(timeout=180)
   except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGTERM);p.wait();rc=124
  row=dict(head=head,pin=pin,module=m,phase=phase,command=cmd,cwd=str(r),pid=p.pid,pgid=p.pid,start=start,seconds=time.monotonic()-t,exit_code=rc,dependency_fingerprint=fingerprint_hash,source_sha256=sources[m],artifact=artifact(m),log=log.name,duplicate_prerequisite_cost=m!=mods[-1]);results.append(row)
  with (out/'results.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
  print(m,phase,rc,round(row['seconds'],3),flush=True)
  if rc:print(log.read_text(),flush=True);raise SystemExit(rc)
write('summary.json',dict(head=head,pin=pin,compile_pass=11,strict_pass=1,failed=0,additional_missing_dependencies=0,duplicate_prerequisite_compile_count=10,duplicate_prerequisite_seconds=sum(x['seconds'] for x in results if x['duplicate_prerequisite_cost']),snake_seconds=sum(x['seconds'] for x in results if not x['duplicate_prerequisite_cost']),free_bytes=shutil.disk_usage(r).free,finished=datetime.datetime.now(datetime.timezone.utc).isoformat()))
print('COMPLETE',flush=True)
