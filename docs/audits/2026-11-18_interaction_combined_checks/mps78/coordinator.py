"""Resume-safe serial handoff: old pin729 queue, then isolated Interaction MPS77."""
import collections, datetime, fcntl, hashlib, json, os, shutil, subprocess, sys, time
from pathlib import Path
ROOT=Path('/tmp/interaction-mps78'); OLD=Path('/tmp/pin729-mps'); OUT=ROOT/'docs/audits/2026-11-18_interaction_combined_checks/mps78'; AUD=OLD/'docs/audits/2026-11-18_pin729_mps_shard'; CACHE=Path('/tmp/interaction-mps77-olean'); OLD_CACHE=Path('/tmp/pin729-mps-olean')
HEAD='dccc85e5607077b51822664e9d475287d300d607'; PIN='729428582b78ab7529b3796099193649f947354a'; LEAN='/workspace/elan/toolchains/leanprover--lean4---v4.36.0-rc1/bin/lean'
ROOTS={'TNLean':ROOT,'QICLean':Path('/tmp/qic729-mps'),'Cslib':Path('/tmp/pin729-cslib')}
OPTS=['-j2','-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def write(name,data):
 p=OUT/name;tmp=p.with_suffix(p.suffix+'.tmp');tmp.write_text(json.dumps(data,indent=2)+'\n');tmp.replace(p)
def event(state,**kw):
 d={'time':now(),'coordinator_pid':os.getpid(),'state':state,**kw};write('coordinator-status.json',d);print(json.dumps(d),flush=True)
def rows(path):return [json.loads(x) for x in path.read_text().splitlines()] if path.exists() else []
def append(path,data):
 with path.open('a') as f:f.write(json.dumps(data)+'\n');f.flush();os.fsync(f.fileno())
def old_processes():
 # cmdline is readable here; cwd/exe symlinks can be denied by sandbox.
 # Conservatively wait for any existing Lean writer before a new serial command.
 found=[]
 for p in Path('/proc').iterdir():
  if not p.name.isdigit() or int(p.name)==os.getpid():continue
  try:
   raw=(p/'cmdline').read_bytes();args=[x.decode() for x in raw.split(b'\0') if x]
   if not args:continue
   exe=os.path.basename(args[0]);cmd=' '.join(args)
   if ('python' in exe and '2026-11-18_pin729_mps_shard/resume.py' in cmd) or exe=='lean':found.append({'pid':int(p.name),'cmd':cmd})
  except (FileNotFoundError,ProcessLookupError):pass
  except PermissionError:
   if p.name=='412863':found.append({'pid':412863,'cmd':'known old runner unreadable; fail closed'})
 return found
def publish(repo,paths,message):
 log=OUT/'publication.log'
 with log.open('a') as f:
  for cmd in [['git','add','-f',*paths],['git','diff','--cached','--quiet']]:
   r=subprocess.run(cmd,cwd=repo,stdout=f,stderr=subprocess.STDOUT)
   if cmd[1]=='add' and r.returncode:raise RuntimeError('git add failed')
  if r.returncode==1:
   r=subprocess.run(['git','commit','-m',message],cwd=repo,stdout=f,stderr=subprocess.STDOUT)
   if r.returncode:raise RuntimeError('git commit failed')
  r=subprocess.run(['git','push'],cwd=repo,stdout=f,stderr=subprocess.STDOUT)
  append(OUT/'publication-results.jsonl',{'time':now(),'repo':str(repo),'push_exit':r.returncode,'head':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()})
  if r.returncode:print('Push failed; evidence retained locally',flush=True)
def source(m):return ROOTS[m.split('.')[0]]/(m.replace('.','/')+'.lean')
def target_status(rs,targets):return {r['module'] for r in rs if r['phase']=='strict' and r['exit_code']==0}&targets

def main():
 lock=Path('/tmp/interaction-mps77-coordinator.lock').open('w');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 while True:
  active=old_processes()
  if not active:break
  rs=rows(AUD/'results.jsonl');passed=len({r['file'] for r in rs if r['phase']=='strict' and r['exit_code']==0});event('waiting_for_old_writers',old_passed=passed,old_processes=active);time.sleep(20)
 # Double-check quiescence, preserving failures rather than treating every exit as success.
 time.sleep(2);assert not old_processes()
 if not (OUT/'old-final.json').exists():
  subprocess.run([sys.executable,'/tmp/snapshot-mps.py'],cwd=OLD,check=True)
  rs=rows(AUD/'results.jsonl');passed={r['file'] for r in rs if r['phase']=='strict' and r['exit_code']==0};summary=json.loads((AUD/'summary.json').read_text());summary['state']='old writers exited; final handoff snapshot';(AUD/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
  log=Path('/tmp/pin729-mps-resume4.log');shutil.copy2(log,AUD/'resume-final.log')
  final={'time':now(),'passed':len(passed),'remaining':865-len(passed),'historical_failures':[r for r in rs if r['exit_code']],'results_sha256':sha(AUD/'results.jsonl'),'old_processes':old_processes(),'runner_tail':log.read_text().splitlines()[-8:]};write('old-final.json',final)
  publish(OLD,['docs/audits/2026-11-18_pin729_mps_shard'],'audit: preserve final old MPS queue ledger before Interaction handoff')
 assert not old_processes()
 # Read-only source/closure comparison against the completed old cache.
 subprocess.run([sys.executable,str(OUT/'prepare_plan.py')],cwd=ROOT,check=True)
 manifest=(OUT/'manifest77.txt').read_text().splitlines();assert len(manifest)==77 and all('SnakeGridAreaLaw' not in x for x in manifest)
 targets={p[:-5].replace('/','.') for p in manifest};allgraph={x['module']:x for x in json.loads((OUT/'dependency-plan.json').read_text())};need=set()
 def visit(m):
  if m in need:return
  need.add(m)
  for d in allgraph[m]['dependencies']:visit(d)
 for m in targets:visit(m)
 exclusive=set(json.loads((OUT/'peps-overlap.json').read_text())['paths']);assert not need&exclusive
 assert (ROOT/'lake-manifest.json').read_bytes()==(OLD/'lake-manifest.json').read_bytes()
 assert (ROOT/'lean-toolchain').read_bytes()==(OLD/'lean-toolchain').read_bytes()
 packages=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
 for p in packages:
  if p['name'].lower()=='qiclean':path=ROOTS['QICLean']
  elif p['name'].lower()=='cslib':path=ROOTS['Cslib']
  else:path=Path('/workspace/QICLean/.lake/packages')/p['name']
  actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=path,text=True).strip();assert actual==p['rev'],(p['name'],actual,p['rev'])
 CACHE.mkdir(exist_ok=True);rs=rows(OUT/'results77.jsonl');built={r['module'] for r in rs if r['phase']=='build' and r['exit_code']==0}
 for r in rs:
  if not r['exit_code']:
   assert sha(source(r['module']))==r['source_sha256']
   if r['phase']=='build':assert sha(CACHE/(r['module'].replace('.','/')+'.olean'))==r['olean_sha256']
 reused=[]
 for m in sorted(need):
  if not allgraph[m]['reusable'] or m in built:continue
  assert sha(source(m))==allgraph[m]['source_sha256']
  stem=OLD_CACHE/(m.replace('.','/'));dest=CACHE/(m.replace('.','/'));dest.parent.mkdir(parents=True,exist_ok=True)
  artifacts=[]
  for p in sorted(stem.parent.glob(stem.name+'.*')):
   if not p.is_file():continue
   q=dest.parent/p.name;shutil.copy2(p,q);assert sha(q)==sha(p);artifacts.append({'path':str(q.relative_to(CACHE)),'sha256':sha(q)})
  assert (CACHE/(m.replace('.','/')+'.olean')).exists();built.add(m);reused.append({'module':m,'source_sha256':allgraph[m]['source_sha256'],'artifacts':artifacts})
 write('reused77.json',reused);write('run-plan77.json',{'head':HEAD,'pin':PIN,'manifest_sha256':sha(OUT/'manifest77.txt'),'targets':77,'project_closure':len(need),'reused_or_previously_built':len(built),'pending_build':len(need-built),'cache':str(CACHE),'old_cache_not_in_LEAN_PATH':True,'workers':1,'lean_threads':2,'disk_stop_bytes':1024**3})
 env=os.environ.copy();external=json.loads((AUD/'cache-paths.json').read_text())['LEAN_PATH'].split(':')[1:];env['LEAN_PATH']=':'.join([str(CACHE),*external]);write('environment77.json',{'LEAN_PATH':env['LEAN_PATH'],'toolchain':(ROOT/'lean-toolchain').read_text().strip()})
 passed=target_status(rs,targets);last_publish=len(passed)
 def execute(m,phase):
  assert shutil.disk_usage(ROOT).free>=1024**3,'disk guard below 1 GiB'
  assert not old_processes(),'old writer resumed; refusing cache handoff'
  p=source(m);dest=CACHE/(m.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);log=OUT/(m+'.'+phase+'.log');cmd=[LEAN,*OPTS]+(['-o',str(dest)] if phase=='build' else ['-DautoImplicit=false','-DwarningAsError=true'])+[str(p.relative_to(ROOTS[m.split('.')[0]]))]
  start=time.monotonic();stamp=now()
  with log.open('w') as f:
   child=subprocess.Popen(cmd,cwd=ROOTS[m.split('.')[0]],env=env,stdout=f,stderr=subprocess.STDOUT);event('compiling' if phase=='build' else 'strict',module=m,compiler_pid=child.pid,passed=len(passed),remaining=77-len(passed));code=child.wait()
  r={'head':HEAD,'qic_pin':PIN,'module':m,'phase':phase,'role':'target77' if m in targets else 'dependency_only','command':cmd,'source_sha256':sha(p),'started_utc':stamp,'seconds':time.monotonic()-start,'exit_code':code,'log':log.name,'method':'direct Lean overlay compilation + strict; not Lake build'}
  if not code and phase=='build':r['olean_sha256']=sha(dest)
  append(OUT/'results77.jsonl',r)
  if code:raise RuntimeError(f'{m} {phase} failed exit {code}; original log retained')
  if phase=='build':built.add(m)
  else:passed.add(m)
 def compile_closure(m):
  if m in built:return
  for d in sorted(allgraph[m]['dependencies']):compile_closure(d)
  execute(m,'build')
 def missing(m):
  s=set()
  def collect(n):
   if n in built or n in s:return
   s.add(n)
   for d in allgraph[n]['dependencies']:collect(d)
  collect(m);return len(s)
 # Smallest closure first; first 3 targets form the initial cluster, then groups of 10.
 while targets-passed:
  m=min(targets-passed,key=lambda n:(missing(n),n));compile_closure(m);execute(m,'strict')
  write('summary77.json',{'time':now(),'passed':len(passed),'remaining':77-len(passed),'state':'running','head':HEAD,'pin':PIN})
  if len(passed)==3 or len(passed)-last_publish>=10:
   publish(ROOT,['docs/audits/2026-11-18_interaction_combined_checks/mps78'],'audit: checkpoint isolated Interaction MPS77 validation');last_publish=len(passed)
 event('complete',passed=77,remaining=0);publish(ROOT,['docs/audits/2026-11-18_interaction_combined_checks/mps78'],'audit: finish isolated Interaction MPS77 validation')

if __name__=='__main__':
 try:main()
 except Exception as e:
  event('blocked',error=repr(e))
  try:publish(ROOT,['docs/audits/2026-11-18_interaction_combined_checks/mps78'],'audit: preserve Interaction MPS77 handoff or validation blocker')
  except Exception as secondary:print(repr(secondary),flush=True)
  raise
