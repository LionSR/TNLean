import os,json,hashlib,re,subprocess,time,fcntl,shutil,datetime
from pathlib import Path
from functools import lru_cache
ROOT=Path('/tmp/main16b-mps');OUT=ROOT/'docs/audits/2026-11-18_main16b_mps_validation';CACHE=Path('/tmp/main16b-mps-olean');HEAD='f94193009343ee767ddc96a3dacee80e659ec5a9';PIN='729428582b78ab7529b3796099193649f947354a';OLD=Path('/tmp/pin729-mps/docs/audits/2026-11-18_pin729_mps_shard');PREV=Path('/tmp/interaction-mps78/docs/audits/2026-11-18_interaction_combined_checks/mps78');LEAN='/workspace/elan/toolchains/leanprover--lean4---v4.36.0-rc1/bin/lean'
roots={'TNLean':ROOT,'verification':ROOT,'QICLean':Path('/tmp/qic729-mps'),'Cslib':Path('/tmp/pin729-cslib')};graph={};hashes={};records={};reuse={};options=['-j1','-M12288','-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def read(p):return [json.loads(x) for x in p.read_text().splitlines()] if p.exists() else []
def write(n,d):(OUT/n).write_text(json.dumps(d,indent=2)+'\n')
def append(n,d):
 with (OUT/n).open('a') as f:f.write(json.dumps(d)+'\n');f.flush();os.fsync(f.fileno())
def src(m):return roots[m.split('.')[0]]/(m.replace('.','/')+'.lean')
def visit(m):
 if m in graph:return
 p=src(m);assert p.exists(),p;hashes[m]=sha(p);deps=set()
 for line in p.read_text().splitlines():
  if re.match(r'^(?:public |private )?import ',line):deps|={x for x in line.split('import ',1)[1].split() if x.split('.')[0] in roots}
 graph[m]=deps
 for d in deps:visit(d)
@lru_cache(None)
def closure(m):return {m}|set().union(*(closure(d) for d in graph[m]))
def add(m,r,cache):records.setdefault(m,[]).append((r,cache))
def valid(m):
 if m in reuse:return reuse[m] is not None
 deps=all([valid(d) for d in graph[m]])
 reuse[m]=None
 if deps:
  for r,c in reversed(records.get(m,[])):
   p=c/(m.replace('.','/')+'.olean')
   if r.get('source_sha256')==hashes[m] and p.exists() and r.get('olean_sha256')==sha(p):reuse[m]=(r,c);break
 return reuse[m] is not None
def publish(msg):
 subprocess.run(['git','add','-f',str(OUT.relative_to(ROOT))],cwd=ROOT,check=True)
 if subprocess.run(['git','diff','--cached','--quiet'],cwd=ROOT).returncode:subprocess.run(['git','commit','-qm',msg],cwd=ROOT,check=True)
 r=subprocess.run(['git','push','-u','origin','evidence/main16b-mps-validation'],cwd=ROOT);append('publication.jsonl',{'time':now(),'exit':r.returncode})
def main():
 lock=Path('/tmp/interaction-mps77-coordinator.lock').open('w');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 for p in Path('/proc').glob('[0-9]*/cmdline'):
  try:a=p.read_bytes().split(b'\0')
  except (FileNotFoundError,PermissionError):continue
  if a and os.path.basename(a[0].decode())=='lean':raise RuntimeError('another compiler active')
 assert (ROOT/'lake-manifest.json').read_bytes()==(Path('/tmp/interaction-mps78')/'lake-manifest.json').read_bytes()
 assert (ROOT/'lean-toolchain').read_bytes()==(Path('/tmp/interaction-mps78')/'lean-toolchain').read_bytes()
 for pkg in json.loads((ROOT/'lake-manifest.json').read_text())['packages']:
  p=roots['QICLean'] if pkg['name']=='qiclean' else roots['Cslib'] if pkg['name']=='cslib' else Path('/workspace/QICLean/.lake/packages')/pkg['name'];assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=p,text=True).strip()==pkg['rev']
 targets=set((OUT/'manifest.txt').read_text().splitlines());affected=set((OUT/'affected13.txt').read_text().splitlines());large={'TNLean','TNLean.MPS','TNLean.MPS.AreaLaw'}
 for m in targets:visit(m)
 snapshot={r['file']:r for r in json.loads((OLD/'cache-artifacts.json').read_text())}
 for r in read(OLD/'results.jsonl'):
  if r['phase']=='build' and r['exit_code']==0:add(r['file'][:-5].replace('/','.'),{**snapshot.get(r['file'],{}),**r},Path('/tmp/pin729-mps-olean'))
 for r in read(OLD/'cslib-results.jsonl'):
  if r['exit_code']==0:add(r['file'][:-5].replace('/','.'),r,Path('/tmp/pin729-mps-olean'))
 for r in read(PREV/'results77.jsonl'):
  if r['phase']=='build' and r['exit_code']==0:add(r['module'],r,Path('/tmp/interaction-mps77-olean'))
 for m in graph:valid(m)
 write('reuse-plan.json',[{'module':m,'source_sha256':hashes[m],'dependencies':sorted(graph[m]),'eligible':reuse[m] is not None,'origin':str(reuse[m][1]) if reuse[m] else None} for m in sorted(graph)])
 # Copy verified records only. Never reference old writable project caches.
 CACHE.mkdir(exist_ok=True);built=set();artifactlog=[]
 for m in sorted(graph):
  if not reuse[m]:continue
  r,c=reuse[m];stem=c/m.replace('.','/');dest=CACHE/m.replace('.','/');dest.parent.mkdir(parents=True,exist_ok=True)
  for p in stem.parent.glob(stem.name+'.*'):
   if p.is_file():
    q=dest.parent/p.name;h=sha(p);shutil.copy2(p,q);assert sha(q)==h==sha(p);artifactlog.append({'module':m,'path':str(q.relative_to(CACHE)),'sha256':h,'origin':str(p)})
  built.add(m)
 write('reused-artifacts.json',artifactlog)
 previous=read(OUT/'results.jsonl');passed={r['module'] for r in previous if r['phase']=='strict' and r['exit_code']==0}
 for r in previous:
  if r['exit_code']==0:
   assert hashes[r['module']]==r['source_sha256']
   if r['phase']=='build':assert sha(CACHE/(r['module'].replace('.','/')+'.olean'))==r['olean_sha256'];built.add(r['module'])
 # Only two prior final-42c4 strict targets may be reused, with explicit provenance.
 prior_strict=[]
 for r in read(PREV/'results77.jsonl'):
  if r['phase']=='strict' and r['exit_code']==0 and r['module'] in targets and reuse.get(r['module']):
   passed.add(r['module']);prior_strict.append({'module':r['module'],'original_head':r['head'],'original_record':r,'reuse_for_head':HEAD,'reason':'unchanged complete project source/import closure and artifact hash validated'})
 write('prior-strict-reuse.json',prior_strict)
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(CACHE),*json.loads((OLD/'cache-paths.json').read_text())['LEAN_PATH'].split(':')[1:]])
 write('environment.json',{'head':HEAD,'pin':PIN,'options':options,'LEAN_PATH':env['LEAN_PATH'],'lean_binary_sha256':sha(Path(LEAN)),'initial_reused':len(built),'closure':len(graph),'targets':len(targets),'memory_available':Path('/proc/meminfo').read_text(),'original_memory_failure_preserved':str(PREV/'TNLean.MPS.AreaLaw.Hastings.BoundaryFactorization.build.log')})
 def run(m,phase):
  assert shutil.disk_usage(ROOT).free>1024**3
  available=int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:')))
  assert available>8*1024**2,'less than 8 GiB available; stopping safely'
  p=src(m);dest=CACHE/(m.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);log=OUT/(m+'.'+phase+'.log');cmd=[LEAN,*options]+(['-o',str(dest)] if phase=='build' else ['-DautoImplicit=false','-DwarningAsError=true'])+[str(p.relative_to(roots[m.split('.')[0]]))];t=time.monotonic();stamp=now()
  with log.open('w') as f:
   child=subprocess.Popen(cmd,cwd=roots[m.split('.')[0]],env=env,stdout=f,stderr=subprocess.STDOUT);write('status.json',{'state':phase,'module':m,'pid':child.pid,'runner_pid':os.getpid(),'time':stamp,'passed':len(passed),'head':HEAD});code=child.wait()
  r={'module':m,'phase':phase,'head':HEAD,'pin':PIN,'source_sha256':hashes[m],'command':cmd,'started':stamp,'seconds':time.monotonic()-t,'exit_code':code,'role':'target' if m in targets else 'dependency','method':'direct Lean compilation/strict, not Lake'}
  if phase=='build' and code==0:r['olean_sha256']=sha(dest)
  append('results.jsonl',r)
  if code:raise RuntimeError(f'{m} {phase} exit {code}')
  if phase=='build':built.add(m)
  else:passed.add(m)
 def build(m):
  if m in built:return
  for d in sorted(graph[m]):build(d)
  run(m,'build')
 pending=targets-passed-large;done=0
 while pending:
  m=min(pending,key=lambda n:(0 if n=='TNLean.MPS.AreaLaw.Hastings.BoundaryFactorization' else 1 if n in affected else 2,len(closure(n)-built),n));build(m);run(m,'strict');pending.remove(m);done+=1;write('summary.json',{'head':HEAD,'passed_or_provenance_reused':sorted(passed),'remaining':sorted(targets-passed),'state':'running'})
  if done%10==0:publish('audit: checkpoint exact main16b MPS validation')
 # Aggregate checks only when closure is warm: do not launch a cold full-library closure.
 deferred={}
 for m in ['TNLean.MPS.AreaLaw','TNLean.MPS','TNLean']:
  missing=closure(m)-built
  if missing-{m}:deferred[m]=sorted(missing);continue
  build(m);run(m,'strict')
 write('aggregate-not-run.json',deferred);write('summary.json',{'head':HEAD,'passed_or_provenance_reused':sorted(passed),'remaining':sorted(targets-passed),'state':'finished narrow checks; aggregate gaps recorded'})
 write('status.json',{'state':'finished','head':HEAD,'passed':len(passed),'not_run':sorted(targets-passed),'axiom_audit':'not-run; compilation/strict only'})
 publish('audit: complete available exact main16b MPS narrow checks')
if __name__=='__main__':
 try:main()
 except Exception as e:
  write('status.json',{'state':'blocked','error':repr(e),'time':now(),'head':HEAD});publish('audit: preserve exact main16b validation blocker');raise
