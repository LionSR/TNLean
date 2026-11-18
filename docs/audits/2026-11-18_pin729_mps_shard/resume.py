import concurrent.futures as cf
import datetime,hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path
root=Path('/tmp/pin729-mps'); qic=Path('/tmp/qic729-mps'); out=root/'docs/audits/2026-11-18_pin729_mps_shard'; cache=Path('/tmp/pin729-mps-olean')
head='ef098ad32a728e847957320f9cf79ddcfce5245a';pin='729428582b78ab7529b3796099193649f947354a'
lean='/workspace/elan/toolchains/leanprover--lean4---v4.36.0-rc1/bin/lean'
files=(out/'manifest.txt').read_text().splitlines(); targets={p[:-5].replace('/','.') for p in files}
assert hashlib.sha256((out/'manifest.txt').read_bytes()).hexdigest()=='6154be849927457d11a0e1666a778d3d68383e5884e16c08ec1252c5694cf7f5'
rows=[json.loads(s) for s in (out/'results.jsonl').read_text().splitlines()]
built={r['file'][:-5].replace('/','.') for r in rows if r['phase']=='build' and r['exit_code']==0}; passed={r['file'][:-5].replace('/','.') for r in rows if r['phase']=='strict' and r['exit_code']==0}
for m in built:assert (cache/Path(m.replace('.','/')).with_suffix('.olean')).exists()
roots={'TNLean':root,'QICLean':qic};graph={};closures={}
def src(m):return roots[m.split('.')[0]]/Path(m.replace('.','/')).with_suffix('.lean')
def visit(m):
 if m in graph:return
 p=src(m); ds=set()
 for line in p.read_text().splitlines():
  if re.match(r'^(?:public |private )?import ',line):
   ds|={d for d in line.split('import ',1)[1].split() if d.split('.')[0] in roots}
 graph[m]=ds
 for d in ds:visit(d)
def closure(m):
 if m not in closures:closures[m]={m}|set().union(*(closure(d) for d in graph[m]))
 return closures[m]
for m in targets:visit(m)
exclusive={p[:-5].replace('/','.') for p in (root/'docs/audits/2026-11-18_pin729_integration/overlap11.txt').read_text().splitlines() if p.endswith('.lean')}
env=os.environ.copy();env['LEAN_PATH']=json.load(open(out/'cache-paths.json'))['LEAN_PATH']
opts=['-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true']
def run(m,phase):
 p=src(m); rel=str(p.relative_to(roots[m.split('.')[0]]));dest=cache/Path(m.replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 cmd=[lean]+opts+(['-o',str(dest)] if phase=='build' else ['-DautoImplicit=false','-DwarningAsError=true'])+[rel]
 start=time.monotonic(); now=datetime.datetime.now(datetime.timezone.utc).isoformat();log=out/(m+'.'+phase+'.log')
 with log.open('w') as f:r=subprocess.run(cmd,cwd=roots[m.split('.')[0]],env=env,stdout=f,stderr=subprocess.STDOUT)
 row={'source_head':pin if m.startswith('QICLean.') else head,'qic_pin':pin,'file':rel,'phase':phase,'command':cmd,'started_utc':now,'seconds':time.monotonic()-start,'exit_code':r.returncode,'method':'direct Lean (not lake build)','role':'shard_target' if m in targets else 'dependency_only','source_sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
 if phase=='build' and not r.returncode:row['olean_sha256']=hashlib.sha256(dest.read_bytes()).hexdigest()
 return row
stop=None;checkpoint=0
with cf.ThreadPoolExecutor(max_workers=2) as pool:
 while targets-passed and not stop:
  batch=sorted(targets-passed,key=lambda m:(len(closure(m)-built),m))[:30]
  need=set().union(*(closure(m) for m in batch));pending=need-built
  forbidden=pending&exclusive
  if forbidden:stop='Exclusive dependency requires coordinator cache: '+str(sorted(forbidden));break
  active={}; launched=set(); strict_started=set()
  while (pending or set(batch)-passed or active) and not stop:
   if shutil.disk_usage(root).free<5*1024**3:stop='Disk guard: less than 5 GiB free';break
   ready_strict=[m for m in batch if m in built and m not in passed and m not in strict_started]
   ready_build=sorted(m for m in pending if m not in launched and graph[m]<=built)
   for m,phase in [(m,'strict') for m in ready_strict]+[(m,'build') for m in ready_build]:
    if len(active)>=2:break
    if phase=='build':launched.add(m)
    else:strict_started.add(m)
    active[pool.submit(run,m,phase)]=(m,phase)
   if not active:stop='No dependency-ready task; graph blocked';break
   finished,_=cf.wait(active,timeout=20,return_when=cf.FIRST_COMPLETED)
   for f in finished:
    m,phase=active.pop(f);r=f.result();rows.append(r)
    with (out/'results.jsonl').open('a') as log:log.write(json.dumps(r)+'\n')
    if r['exit_code']:stop=f"{m} {phase} failed ({r['exit_code']})";print(stop,flush=True)
    elif phase=='build':built.add(m);pending.remove(m)
    else:passed.add(m);print('PASS',len(passed&targets),m,flush=True)
  # Drain already-running writers even on failure, retaining their evidence.
  for f,(m,phase) in active.items():
   r=f.result();rows.append(r)
   with (out/'results.jsonl').open('a') as log:log.write(json.dumps(r)+'\n')
   if not r['exit_code']:
    if phase=='build':built.add(m)
    else:passed.add(m)
  checkpoint+=1
  state={'checkpoint':checkpoint,'passed':len(passed&targets),'remaining':len(targets-passed),'failed_commands':sum(r['exit_code']!=0 for r in rows),'build_seconds':sum(r['seconds'] for r in rows if r['phase']=='build'),'strict_seconds':sum(r['seconds'] for r in rows if r['phase']=='strict'),'stop':stop,'free_bytes':shutil.disk_usage(root).free}
  (out/'resume-status.json').write_text(json.dumps(state,indent=2)+'\n');print('CHECKPOINT',json.dumps(state),flush=True)
print('FINISHED',stop or 'all targets passed',flush=True)
