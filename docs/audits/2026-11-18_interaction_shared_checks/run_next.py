import pathlib,json,subprocess,os,time,datetime,fcntl,signal,shutil
r=pathlib.Path('/workspace/tn-interaction-integration');warm=pathlib.Path('/workspace/tn-pin729-other');out=pathlib.Path('/workspace/reviews/interaction-shared-validation');overlay=out/'olean';overlay.mkdir(exist_ok=True);q=warm/'.lake/packages/qiclean';lock=(out/'validation.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
plan=json.loads((out/'preflight.json').read_text());targets=['TNLean.Lattice.MarginalTails','TNLean.Lattice.ProductForm','TNLean.PEPS.AreaLaw.RectangularHamiltonian'];order=list(dict.fromkeys(m for t in targets for m in plan[t]));paths=[overlay,warm/'.lake/build/lib/lean',q/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in (warm/'.lake/packages').iterdir() if p.name!='qiclean'];env=os.environ.copy();env.update(LEAN_PATH=':'.join(map(str,paths)),LEAN_NUM_THREADS='2');lean='/workspace/elan/toolchains/leanprover--lean4---v4.36.0-rc1/bin/lean';head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=r,text=True).strip();assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=q,text=True).strip()=='729428582b78ab7529b3796099193649f947354a'
flags=['-DautoImplicit=false','-DrelaxedAutoImplicit=false','-Dpp.unicode.fun=true','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true']
cmds=[]
for m in order:
 p=m.replace('.','/')+'.lean';root=q if m.startswith('QICLean.') else r;ole=overlay/(m.replace('.','/')+'.olean');ole.parent.mkdir(parents=True,exist_ok=True)
 cmds.append(('compile',m,root,[lean,*flags,'-o',str(ole),p]))
 if m in targets:cmds.append(('strict',m,root,[lean,*flags,'-DwarningAsError=true',p]))
done={(x['module'],x['phase']) for x in map(json.loads,(out/'results.jsonl').read_text().splitlines()) if x['exit_code']==0}
for i,(phase,m,cwd,cmd) in enumerate(cmds):
 if (m,phase) in done:continue
 if phase=='compile':
  target=pathlib.Path(cmd[cmd.index('-o')+1])
  if target.is_symlink():target.unlink()
 if shutil.disk_usage(r).free<2**30:raise SystemExit('disk guard')
 t=time.monotonic();start=datetime.datetime.now(datetime.timezone.utc).isoformat();log=out/f'shared-next-{i:02d}.log'
 with log.open('w') as f:
  p=subprocess.Popen(cmd,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
  try:rc=p.wait(timeout=180)
  except subprocess.TimeoutExpired:
   os.killpg(p.pid,signal.SIGTERM);p.wait();rc=124
 row=dict(head=head,pin='729428582b78ab7529b3796099193649f947354a',module=m,phase=phase,method='direct Lean; no Lake cache mutations',command=cmd,cwd=str(cwd),pid=p.pid,pgid=p.pid,start=start,seconds=time.monotonic()-t,exit_code=rc,log=log.name)
 with (out/'results.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
 print(json.dumps(row),flush=True)
 if rc:raise SystemExit(rc)
