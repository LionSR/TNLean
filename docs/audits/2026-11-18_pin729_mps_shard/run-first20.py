import json,os,re,subprocess,time,datetime,shutil
from pathlib import Path
root=Path('/tmp/pin729-mps');out=root/'docs/audits/2026-11-18_pin729_mps_shard'; cache=Path('/tmp/pin729-mps-olean');qic=Path('/tmp/qic729-mps');lean='/workspace/elan/toolchains/leanprover--lean4---v4.36.0-rc1/bin/lean'
closures=json.load(open('/tmp/mps-closures.json')); targets=[p[:-5].replace('/','.') for p in sorted(closures,key=lambda p:(len(closures[p]),p))[:20]];order=[];seen=set()
def source(m):return (qic if m.startswith('QICLean.') else root)/Path(m.replace('.','/')).with_suffix('.lean')
def visit(m):
 if m in seen:return
 seen.add(m)
 for line in source(m).read_text().splitlines():
  if re.match(r'^(?:public |private )?import ',line):
   for d in line.split('import ',1)[1].split():
    if d.startswith(('QICLean.','TNLean.')):visit(d)
 order.append(m)
for m in targets:visit(m)
(out/'first20-order.txt').write_text('\n'.join(order)+'\n'); print('narrow project closure',len(order),flush=True)
env=os.environ.copy();env['LEAN_PATH']=json.load(open(out/'cache-paths.json'))['LEAN_PATH'];opts=['-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true']
completed={(r['file'],r['phase']) for r in map(json.loads,(out/'results.jsonl').read_text().splitlines()) if r['exit_code']==0}
for m in order:
 if shutil.disk_usage(root).free<5*1024**3: print('STOP disk guard',flush=True);break
 p=source(m);relative=str(p.relative_to(qic if m.startswith('QICLean.') else root));dest=cache/Path(m.replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 phases=[('build',['-o',str(dest)])]+([('strict',['-DautoImplicit=false','-DwarningAsError=true'])] if m in targets else [])
 for phase,args in phases:
  if (relative,phase) in completed and (phase!='build' or dest.exists()):continue
  cmd=[lean]+opts+args+[relative];start=time.monotonic();now=datetime.datetime.now(datetime.timezone.utc).isoformat();log=out/(m+'.'+phase+'.log')
  with log.open('w') as f:r=subprocess.run(cmd,cwd=qic if m.startswith('QICLean.') else root,env=env,stdout=f,stderr=subprocess.STDOUT)
  record={'source_head':'729428582b78ab7529b3796099193649f947354a' if m.startswith('QICLean.') else '6b7fb2e27dbc6856091e593e4226d350403beb8a','qic_pin':'729428582b78ab7529b3796099193649f947354a','file':relative,'phase':phase,'command':cmd,'started_utc':now,'seconds':time.monotonic()-start,'exit_code':r.returncode,'method':'direct Lean (not lake build)','role':'shard_target' if m in targets else 'dependency_only'}
  with (out/'results.jsonl').open('a') as f:f.write(json.dumps(record)+'\n')
  print(m,phase,r.returncode,round(record['seconds'],2),flush=True)
  if r.returncode:print(log.read_text()[-3000:],flush=True);raise SystemExit(r.returncode)
