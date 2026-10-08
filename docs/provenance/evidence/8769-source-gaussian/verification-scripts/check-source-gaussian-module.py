from pathlib import Path
import hashlib,json,os,subprocess,sys,time
b=Path('/private/tmp/tnlean-source-gaussian');cfg=json.loads((b/'env.json').read_text());root=Path(cfg['source_root']);mod=sys.argv[1];rel=Path(mod.replace('.','/')+'.lean');src=root/rel;dst=Path(cfg['output_root'])/rel.with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
 p=dst.with_suffix(suffix)
 if p.is_symlink():p.unlink()
folder=b/'strict-checks';folder.mkdir(exist_ok=True);snapshot=folder/'sources'/rel;snapshot.parent.mkdir(parents=True,exist_ok=True);snapshot.write_bytes(src.read_bytes());cfgpath=folder/'env.json';cfgpath.write_text(json.dumps(cfg,indent=2)+'\n')
cmd=[cfg['lean'],*cfg['options'],'-DwarningAsError=true','-o',str(dst),str(rel)];env=os.environ.copy();env['LEAN_PATH']=cfg['LEAN_PATH'];t=time.monotonic();r=subprocess.run(cmd,cwd=root,env=env,capture_output=True,text=True);log=folder/(mod+'.log');log.write_text(r.stdout+r.stderr);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();record={'module':mod,'source_path':str(rel),'source_sha256':sha(snapshot),'command':cmd,'cwd':str(root),'LEAN_PATH':cfg['LEAN_PATH'],'returncode':r.returncode,'seconds':round(time.monotonic()-t,3),'log_sha256':sha(log),'artifact':str(dst),'artifact_sha256':sha(dst) if dst.exists() else None};(folder/(mod+'.json')).write_text(json.dumps(record,indent=2)+'\n');print(mod,r.returncode,record['seconds']);print(r.stdout+r.stderr);assert r.returncode==0
