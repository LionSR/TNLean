from pathlib import Path
import datetime,hashlib,json,os,subprocess,sys,time
base=Path('/private/tmp/tnlean-source-main-integration');repo=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-integration');hot=repo.parent/'hot-main';qic=Path('/Users/siruilu/Local/agentFormalization/QICLean/worktrees/area-law-pure-tensor-power')
plan=json.loads((base/'verification-plan.json').read_text());out=base/'strict-artifacts';records=base/'strict-checks';records.mkdir(exist_ok=True);out.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
old=json.loads(Path('/private/tmp/tnlean-fixed-chronological-sources/env.json').read_text())
roots=[str(out)]
for path in old['LEAN_PATH'].split(':'):
 if '/.lake/packages/' in path and '/qiclean/' not in path:roots.append(path)
roots += [str(qic/'.lake/build/lib/lean'), str(Path(old['lean']).parent.parent/'lib/lean')]
leanpath=':'.join(roots);cfg={**old,'LEAN_PATH':leanpath,'source_root':str(repo),'output_root':str(out)};(base/'env.json').write_text(json.dumps(cfg,indent=2)+'\n')
env=os.environ.copy();env['LEAN_PATH']=leanpath
if sys.argv[1]=='setup':
 assert subprocess.check_output(['git','-C',str(hot),'rev-parse','HEAD'],text=True).strip()=='80bc49d17e833795fba00bfeaf1bd053649c4070'
 selected=set(plan['selected_tn']);count=0;inherited=[]
 for p in [repo/'TNLean.lean',*(repo/'TNLean').rglob('*.lean')]:
  if 'Archive' in p.parts:continue
  rel=p.relative_to(repo);mod=str(rel).removesuffix('.lean').replace('/','.')
  if mod in selected:continue
  hp=hot/rel;assert hp.exists() and p.read_bytes()==hp.read_bytes(),('Unselected source differs',rel)
  artifact=hot/'.lake/build/lib/lean'/rel.with_suffix('.olean');assert artifact.exists(),('Missing baseline artifact',mod)
  inherited.append({'module':mod,'source_sha256':sha(p),'artifact':str(artifact),'artifact_sha256':sha(artifact)})
  for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
   src=hot/'.lake/build/lib/lean'/rel.with_suffix(suffix)
   if not src.is_file():continue
   dest=out/rel.with_suffix(suffix);dest.parent.mkdir(parents=True,exist_ok=True)
   assert not dest.exists() and not dest.is_symlink(),dest
   dest.symlink_to(src);count+=1
 (records/'unchanged-predecessors.json').write_text(json.dumps(inherited,indent=2)+'\n')
 print('UNCHANGED_SOURCE_MODULES',len(inherited),'READ_ONLY_LINKS',count,flush=True)
elif sys.argv[1]=='build':
 record={'scope':'Strict direct elaboration of the affected TNLean dependency closure, with QIC integration candidate artifacts; dependency pin not yet changed.','tn_source_revision':plan['tn_head'],'qic_source_revision':plan['qic_candidate'],'command_options':cfg['options']+['-DwarningAsError=true'],'LEAN_PATH':leanpath,'started_utc':now(),'builds':[]}
 for module in plan['selected_tn']:
  rel=Path(module.replace('.','/')+'.lean');src=repo/rel;target=out/rel.with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True);assert not target.is_symlink()
  archive=records/'sources'/rel;archive.parent.mkdir(parents=True,exist_ok=True);archive.write_bytes(src.read_bytes())
  command=[cfg['lean'],*record['command_options'],'-o',str(target),str(rel)]
  print('START',module,flush=True);t=time.monotonic();r=subprocess.run(command,cwd=repo,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  log=records/(module+'.log');log.write_text(r.stdout)
  item={'module':module,'source_path':str(rel),'source_sha256':sha(archive),'command':command,'cwd':str(repo),'returncode':r.returncode,'seconds':round(time.monotonic()-t,3),'log_sha256':sha(log),'artifact':str(target)}
  if target.is_file():item['artifact_sha256']=sha(target)
  record['builds'].append(item);(records/'build-commands.json').write_text(json.dumps(record,indent=2)+'\n')
  print('FINISH',module,'EXIT',r.returncode,'SECONDS',item['seconds'],flush=True)
  if r.stdout:print(r.stdout,flush=True)
  assert r.returncode==0 and src.read_bytes()==archive.read_bytes(),module
 record['completed_utc']=now();(records/'build-commands.json').write_text(json.dumps(record,indent=2)+'\n');print('ALL_AFFECTED_SOURCE_MODULES_PASSED',len(record['builds']),flush=True)
else:raise ValueError(sys.argv[1])
