#!/usr/bin/env python3
"""Strict direct Lean checks for the source-correction contribution, with outputs only in /tmp."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys,time
root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-corrections')
base=Path('/private/tmp/tnlean-source-corrections')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
if sys.argv[1]=='setup':
 sys.path.insert(0,str(root/'scripts'))
 from lean_import_syntax import strip_lean_comments
 old=json.loads(Path('/private/tmp/tnlean-source-main-integration/env.json').read_text())
 out=base/'artifacts';out.mkdir(exist_ok=True)
 first=Path(old['LEAN_PATH'].split(':')[0])
 count=0
 for p in first.rglob('*'):
  if p.is_file():
   q=out/p.relative_to(first);q.parent.mkdir(parents=True,exist_ok=True)
   if not q.exists():q.symlink_to(p.resolve());count+=1
 cfg={**old,'LEAN_PATH':str(out)+':'+':'.join(old['LEAN_PATH'].split(':')[1:]),'source_root':str(root),'output_root':str(out)}
 (base/'env.json').write_text(json.dumps(cfg,indent=2)+'\n')
 paths=[root/'TNLean.lean',*(root/'TNLean').rglob('*.lean')]
 files={str(p.relative_to(root)).removesuffix('.lean').replace('/','.'):p for p in paths if 'Archive' not in p.parts}
 changed=set(subprocess.check_output(['git','diff','--name-only','--','TNLean','TNLean.lean'],cwd=root,text=True).splitlines())
 changed.update(x['path'] for x in json.loads((base/'declarations.json').read_text()))
 selected={p.removesuffix('.lean').replace('/','.') for p in changed if p.endswith('.lean')}
 deps={}
 for m,p in files.items():
  text,err=strip_lean_comments(p.read_text());assert err is None
  deps[m]={x for line in text.splitlines() if line.startswith('import ') for x in line.split()[1:]}
 while True:
  extended=selected|{m for m,d in deps.items() if d&selected}
  if extended==selected:break
  selected=extended
 todo={m:deps[m]&selected for m in selected};order=[]
 while todo:
  ready=sorted(m for m,d in todo.items() if not d);assert ready,'cyclic imports'
  order.extend(ready)
  for m in ready:del todo[m]
  for d in todo.values():d.difference_update(ready)
 (base/'build-plan.json').write_text(json.dumps({'base_revision':'cbdcf495faa5d77becb6c8930f54e4860177d60e','changed_paths':sorted(changed),'selected_modules':order,'read_only_file_links':count},indent=2)+'\n')
 print('Selected',len(order),'modules; read-only predecessor links',count)
elif sys.argv[1]=='build':
 cfg=json.loads((base/'env.json').read_text());plan=json.loads((base/'build-plan.json').read_text())
 env=os.environ.copy();env['LEAN_PATH']=cfg['LEAN_PATH']
 record={'base_revision':plan['base_revision'],'scope':'Strict direct Lean elaboration of the complete affected TNLean import closure; no Lake/cache mutation. Final source commit is pending.','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'LEAN_PATH':cfg['LEAN_PATH'],'builds':[]}
 folder=base/'strict-checks';folder.mkdir(exist_ok=True)
 for mod in plan['selected_modules']:
  rel=Path(mod.replace('.','/')+'.lean');source=root/rel;output=Path(cfg['output_root'])/rel.with_suffix('.olean')
  output.parent.mkdir(parents=True,exist_ok=True)
  # Remove only our output-directory links before replacing these targets.
  for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
   target=output.with_suffix(suffix)
   if target.is_symlink():target.unlink()
  snapshot=folder/'sources'/rel;snapshot.parent.mkdir(parents=True,exist_ok=True);snapshot.write_bytes(source.read_bytes())
  cmd=[cfg['lean'],*cfg['options'],'-DwarningAsError=true','-o',str(output),str(rel)]
  print('START',mod,flush=True);start=time.monotonic()
  p=subprocess.run(cmd,cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  log=folder/(mod+'.log');log.write_text(p.stdout)
  row={'module':mod,'source_path':str(rel),'source_sha256':sha(snapshot),'command':cmd,'cwd':str(root),'returncode':p.returncode,'seconds':round(time.monotonic()-start,3),'log_sha256':sha(log),'artifact':str(output)}
  if output.is_file():row['artifact_sha256']=sha(output)
  record['builds'].append(row);(folder/'build-commands.json').write_text(json.dumps(record,indent=2)+'\n')
  print('FINISH',mod,p.returncode,row['seconds'],flush=True)
  if p.stdout:print(p.stdout,flush=True)
  assert p.returncode==0 and source.read_bytes()==snapshot.read_bytes(),mod
 record['completed_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();(folder/'build-commands.json').write_text(json.dumps(record,indent=2)+'\n')
 print('COMPLETE',len(record['builds']),flush=True)
else:raise ValueError(sys.argv[1])
