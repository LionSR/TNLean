import os,json,subprocess,time,datetime
from pathlib import Path
root=Path.cwd();out=root/'docs/audits/2026-11-18_pin729_mps_shard'; build=Path('/tmp/pin729-mps-olean'); p='TNLean/MPS/AreaLaw/ALVV/MergeRounds.lean';dest=build/Path(p).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
packages=Path('/workspace/QICLean/.lake/packages');spec=json.load(open('lake-manifest.json')); warm=json.load(open('/workspace/QICLean/lake-manifest.json'));revs={x['name']:x.get('rev') for x in warm['packages']}
paths=[]
for x in spec['packages']:
 d=packages/x['name']/'.lake/build/lib/lean'
 if d.exists() and revs.get(x['name'])==x.get('rev') and x['name']!='qiclean':paths.append(str(d))
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(build)]+paths)
(out/'cache-paths.json').write_text(json.dumps({'LEAN_PATH':env['LEAN_PATH'],'excluded':'All old QICLean and TNLean oleans'},indent=2)+'\n')
lean='/workspace/elan/toolchains/leanprover--lean4---v4.36.0-rc1/bin/lean'; opts=['-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true']
for phase,args in [('build',['-o',str(dest)]),('strict',['-DautoImplicit=false','-DwarningAsError=true'])]:
 cmd=[lean]+opts+args+[p];start=time.monotonic();timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
 with open(out/(phase+'-MergeRounds.log'),'w') as f:r=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT)
 record={'source_head':'6b7fb2e27dbc6856091e593e4226d350403beb8a','qic_pin':'729428582b78ab7529b3796099193649f947354a','file':p,'phase':phase,'command':cmd,'started_utc':timestamp,'seconds':time.monotonic()-start,'exit_code':r.returncode,'method':'direct Lean (not lake build)','qic_dependency':False}
 with open(out/'results.jsonl','a') as f:f.write(json.dumps(record)+'\n')
 print(json.dumps(record),flush=True)
