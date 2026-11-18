import os,json,time,subprocess,datetime,hashlib
from pathlib import Path
root=Path('/tmp/pin729-mps');out=root/'docs/audits/2026-11-18_pin729_mps_shard';src=Path('/tmp/pin729-cslib');cache=Path('/tmp/pin729-mps-olean');plan=json.load(open(out/'cslib-query-plan.json'));env=os.environ.copy();env['LEAN_PATH']=json.load(open(out/'cache-paths.json'))['LEAN_PATH'];lean='/workspace/elan/toolchains/leanprover--lean4---v4.36.0-rc1/bin/lean'
for m in plan['order']:
 f=Path(m.replace('.','/')).with_suffix('.lean');dest=cache/f.with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);cmd=[lean,'-o',str(dest),str(f)];start=time.monotonic();now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 with (out/(m+'.dependency-build.log')).open('w') as log:r=subprocess.run(cmd,cwd=src,env=env,stdout=log,stderr=subprocess.STDOUT)
 row={'source_head':plan['source_pin'],'file':str(f),'phase':'dependency_build','command':cmd,'started_utc':now,'seconds':time.monotonic()-start,'exit_code':r.returncode,'source_sha256':plan['source_hashes'][m],'method':'direct Lean; not Lake; no external strict check'}
 if not r.returncode:row['olean_sha256']=hashlib.sha256(dest.read_bytes()).hexdigest()
 with (out/'cslib-results.jsonl').open('a') as log:log.write(json.dumps(row)+'\n')
 print(m,r.returncode,round(row['seconds'],2),flush=True)
 if r.returncode:raise SystemExit(r.returncode)
