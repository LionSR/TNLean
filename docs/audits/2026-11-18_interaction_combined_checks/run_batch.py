import pathlib,json,subprocess,os,time,datetime,fcntl,signal,shutil,sys,hashlib
r=pathlib.Path('/workspace/tn-interaction-integration');warm=pathlib.Path('/workspace/tn-pin729-other');out=pathlib.Path('/workspace/reviews/interaction-shared-validation');overlay=out/'olean';q=warm/'.lake/packages/qiclean'
lock=(out/'validation.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
plan=json.loads((out/sys.argv[1]).read_text());targets=sys.argv[2:];order=list(dict.fromkeys(m for t in targets for m in plan[t]))
paths=[overlay,warm/'.lake/build/lib/lean',q/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (warm/'.lake/packages').iterdir() if p.name!='qiclean'];env=os.environ.copy();env.update(LEAN_PATH=':'.join(map(str,paths)),LEAN_NUM_THREADS='2')
lean='/workspace/elan/toolchains/leanprover--lean4---v4.36.0-rc1/bin/lean';head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip();pin='729428582b78ab7529b3796099193649f947354a';assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=q,text=True).strip()==pin
flags=['-DautoImplicit=false','-DrelaxedAutoImplicit=false','-Dpp.unicode.fun=true','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true'];records=[json.loads(x) for x in (out/'results.jsonl').read_text().splitlines()]
changed=set((r/'docs/audits/2026-11-18_interaction_integration/peps-all.txt').read_text().splitlines())|set((r/'docs/audits/2026-11-18_interaction_integration/mps-all.txt').read_text().splitlines())
commands=[]
for m in order:
 p=m.replace('.','/')+'.lean';root=q if m.startswith('QICLean.') else r;ole=overlay/(m.replace('.','/')+'.olean')
 commands.append(('compile',m,root,[lean,*flags,'-o',str(ole),p]))
 if m in targets or p in changed:commands.append(('strict',m,root,[lean,*flags,'-DwarningAsError=true',p]))
for phase,m,cwd,cmd in commands:
 p=cmd[-1];src=(cwd/p).read_bytes();valid=False
 for row in reversed(records):
  if row['module']!=m or row['phase']!=phase or row['exit_code']!=0:continue
  old=pin if cwd==q else row['head']
  if subprocess.check_output(['git','show',old+':'+p],cwd=cwd,stderr=subprocess.DEVNULL)==src:valid=True
  break
 if valid:continue
 if shutil.disk_usage(r).free<2**30:raise SystemExit('disk guard')
 if phase=='compile':
  dest=pathlib.Path(cmd[cmd.index('-o')+1]);dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.is_symlink():dest.unlink()
 t=time.monotonic();start=datetime.datetime.now(datetime.timezone.utc).isoformat();log=out/f'run-{time.time_ns()}.log'
 with log.open('w') as f:
  proc=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
  try:rc=proc.wait(timeout=180)
  except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGTERM);proc.wait();rc=124
 row=dict(head=head,pin=pin,module=m,phase=phase,source_sha256=hashlib.sha256(src).hexdigest(),method='direct Lean overlay; not Lake build',command=cmd,cwd=str(cwd),pid=proc.pid,pgid=proc.pid,start=start,seconds=time.monotonic()-t,exit_code=rc,log=log.name)
 with (out/'results.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(m,phase,rc,round(row['seconds'],3),flush=True)
 if rc:print(log.read_text(),flush=True);raise SystemExit(rc)
