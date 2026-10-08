from pathlib import Path
import ctypes,hashlib,json,os,re,subprocess
base=Path('/private/tmp/tnlean-source-resource-integration');root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-resource-integration')
old=Path('/private/tmp/tnlean-source-physical/artifacts');art=base/'artifacts';art.mkdir(exist_ok=True)
libc=ctypes.CDLL('/usr/lib/libSystem.B.dylib',use_errno=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[];links=0
for package in ['TNLean','QICLean']:
 for p in [*(old/package).rglob('*'),*old.glob(package+'.*')]:
  if not p.is_file():continue
  q=art/p.relative_to(old);q.parent.mkdir(parents=True,exist_ok=True)
  assert not q.exists() and not q.is_symlink()
  if p.is_symlink():q.symlink_to(p.resolve())
  else:
   frozen=base/'dependencies'/p.relative_to(old);frozen.parent.mkdir(parents=True,exist_ok=True)
   assert libc.clonefile(os.fsencode(p),os.fsencode(frozen),0)==0
   frozen.chmod(0o444);assert sha(p)==sha(frozen)
   rows.append({'original':str(p),'frozen':str(frozen),'sha256':sha(frozen)})
   q.symlink_to(frozen)
  links+=1
cfg=json.loads(Path('/private/tmp/tnlean-source-physical/env.json').read_text())
cfg.update(source_root=str(root),output_root=str(art),LEAN_PATH=str(Path(cfg['lean']).parent.parent/'lib/lean')+':'+str(art)+':/private/tmp/tnlean-artifact-recovery-20261008/gaussian/artifacts')
(base/'env.json').write_text(json.dumps(cfg,indent=2)+'\n')
(base/'environment-preparation.json').write_text(json.dumps({'source_parent':'456204230ab8548568dbbccdac39b894d1539ff5','physical_source_commit':'5547d32efa79b3b18150eb07be2bfcda4a68f79a','preserved_artifacts':rows,'readonly_links':links},indent=2)+'\n')
subprocess.run(['python3','scripts/generate_import_aggregators.py'],cwd=root,check=True)
modules={p['path'][:-5].replace('/','.') for p in json.loads((base/'declarations.json').read_text())}
for p in subprocess.check_output(['git','diff','--name-only'],cwd=root,text=True).splitlines():
 if p.endswith('.lean'):modules.add(p[:-5].replace('/','.'))
imports={m:[x for x in re.findall(r'^import (\S+)',(root/(m.replace('.','/')+'.lean')).read_text(),re.M) if x in modules] for m in modules}
ordered=[]
def visit(m):
 if m in ordered:return
 for d in imports[m]:visit(d)
 ordered.append(m)
for m in sorted(modules):visit(m)
(base/'build-plan.json').write_text(json.dumps({'selected_modules':ordered},indent=2)+'\n')
print('ENVIRONMENT',links,'cloned',len(rows),'BUILD',len(ordered),flush=True)
