from pathlib import Path
import os,sys,time,subprocess,json,hashlib,datetime,shutil,re
B=Path('/workspace/scratch/7637e06d0fc2');D=B/'nested-cylinder-validation';R=B/'TNLean-nested-cylinder-orthogonalization'
assert subprocess.run(['pgrep','-x','lean'],stdout=subprocess.DEVNULL).returncode==1
m=sys.argv[1]; source=R/Path(m.replace('.','/')).with_suffix('.lean')
extra=[x for x in sys.argv[2:] if not x.startswith('--')]
if extra:source=Path(extra[0]).resolve()
dependency='--dependency' in sys.argv
source_root=source.parents[len(m.split('.'))-1]
P=D/'lib'/Path(m.replace('.','/'));P.parent.mkdir(parents=True,exist_ok=True)
T=D/'tmp'/str(time.monotonic_ns())/Path(m.replace('.','/'));T.parent.mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env['LEAN_PATH']=(D/'lean-path.txt').read_text().strip()
assert (B/'TNLean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean').exists()
flags=['-j1','-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true','-DwarningAsError=true']
if dependency:flags.remove('-DwarningAsError=true')
if m.startswith(('TNLeanTest.','QICLeanTest.','scripts.')):flags.append('-DautoImplicit=false')
def source_snapshot():
 seen={}
 def visit(path):
  name=str(path.resolve())
  if name in seen:return
  data=path.read_bytes();seen[name]=hashlib.sha256(data).hexdigest()
  for mod in re.findall(r'^(?:public )?import ([^\s]+)',data.decode(),re.M):
   if mod.startswith('TNLean.'):
    child=R/Path(mod.replace('.','/')).with_suffix('.lean')
   elif mod.startswith('QICLean.'):
    child=B/'TNLean/.lake/packages/qiclean'/Path(mod.replace('.','/')).with_suffix('.lean')
   else:continue
   visit(child)
 visit(source)
 return seen
pre_sources=source_snapshot()
cmd=['timeout','--signal=INT','--kill-after=5s','90s','lean',*flags,'-o',str(T.with_suffix('.olean')),'-i',str(T.with_suffix('.ilean')),str(source)]
log=D/'logs'/(m+'.'+str(time.monotonic_ns())+'.log');start=datetime.datetime.now(datetime.timezone.utc).isoformat();t=time.monotonic()
with log.open('w') as f:proc=subprocess.run(cmd,cwd=source_root,env=env,stdout=f,stderr=subprocess.STDOUT)
post_sources=source_snapshot()
source_unchanged=pre_sources==post_sources
r={'source_closure_sha256_before':pre_sources,'source_closure_sha256_after':post_sources,'source_closure_unchanged':source_unchanged,'module':m,'source':str(source),'cwd':str(source_root),'unchanged_dependency':dependency,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'command':cmd,'lean_path':env['LEAN_PATH'],'start':start,'elapsed_seconds':time.monotonic()-t,'exit_code':proc.returncode,'log':str(log)}
if proc.returncode==0 and source_unchanged:
 for ext in ['.olean','.ilean']:
  if P.with_suffix(ext).is_symlink():P.with_suffix(ext).unlink()
  shutil.copy2(T.with_suffix(ext),P.with_suffix(ext))
 r['artifact_sha256']=hashlib.sha256(P.with_suffix('.olean').read_bytes()).hexdigest()
a=D/'actual-runs.json';runs=json.loads(a.read_text()) if a.exists() else [];runs.append(r);a.write_text(json.dumps(runs,indent=2)+'\n')
print(json.dumps(r,indent=2));print(log.read_text());sys.exit(proc.returncode if proc.returncode else (0 if source_unchanged else 99))
