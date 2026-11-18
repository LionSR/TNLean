import pathlib,subprocess,os,time,json,datetime,shutil,re
root=pathlib.Path('/workspace/tn-pin729-other'); out=pathlib.Path('/workspace/reviews/pin729-other');env=os.environ.copy();env.update(PATH='/workspace/elan/bin:'+env['PATH'],ELAN_HOME='/workspace/elan',XDG_CACHE_HOME='/workspace/cache',LEAN_NUM_THREADS='2')
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip();pin='729428582b78ab7529b3796099193649f947354a'
flags=['-DautoImplicit=false','-DrelaxedAutoImplicit=false','-Dpp.unicode.fun=true','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true','-DwarningAsError=true']
paths=(out/'topological.txt').read_text().splitlines();done=set()
if (out/'results.jsonl').exists():done={json.loads(l)['path'] for l in (out/'results.jsonl').read_text().splitlines() if json.loads(l).get('phase') in ['strict','blocked']}
def record(d):
 d.update(head=head,pin=pin)
 with (out/'results.jsonl').open('a') as f:f.write(json.dumps(d)+'\n')
 print(json.dumps(d),flush=True)
for i,p in enumerate(paths):
 if p in done:continue
 if p in ['TNLean/MPS.lean','TNLean/PEPS.lean']:
  record(dict(path=p,phase='blocked',reason='Root aggregator requires missing MPS/PEPS closure; no cold full library build authorized'));continue
 if shutil.disk_usage(root).free<1.5*1024**3:
  record(dict(path=p,phase='blocked',reason='Disk guard <1.5 GiB'));break
 module=p[:-5].replace('/','.');success=True
 for phase,cmd in [('build',['lake','build',module]),('strict',['lake','env','lean',*flags,p])]:
  if not success:break
  start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic();log=out/f'{i:03d}-{phase}.log'
  with log.open('w') as f:
   try:status=subprocess.run(cmd,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=600).returncode
   except subprocess.TimeoutExpired:status=124
  record(dict(path=p,phase=phase,command=cmd,start=start,end=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-t,exit_code=status,log=log.name))
  success=status==0
  if not success:
   record(dict(path=p,phase='blocked',reason=f'{phase} failed; inspect log; no source changes'))
