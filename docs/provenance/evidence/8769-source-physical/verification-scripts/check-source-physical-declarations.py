from pathlib import Path
import hashlib,json,os,shutil,subprocess,time
b=Path('/private/tmp/tnlean-source-physical');cfg=json.loads((b/'env.json').read_text());out=b/'declaration-check';out.mkdir(exist_ok=True)
bp=Path((b/'blueprint-dir').read_text().strip());shutil.copy2(bp/'full-lean-decls.txt',out/'lean_declarations.txt')
shutil.copy2('/private/tmp/tnlean-source-main-integration/declaration-check/Declarations.lean',out/'Declarations.lean')
env=os.environ.copy();env['LEAN_PATH']=cfg['LEAN_PATH'];cmd=[cfg['lean'],*cfg['options'],'-DwarningAsError=true','Declarations.lean']
t=time.monotonic();r=subprocess.run(cmd,cwd=out,env=env,capture_output=True,text=True);(out/'declarations.log').write_text(r.stdout+r.stderr)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
record={'source_revision':'pending','command':cmd,'cwd':str(out),'LEAN_PATH':cfg['LEAN_PATH'],'returncode':r.returncode,'seconds':round(time.monotonic()-t,3),'source_sha256':sha(out/'Declarations.lean'),'log_sha256':sha(out/'declarations.log'),'scope':'Direct Lean full-root environment check of the synchronized blueprint declaration names; not a Lake checkdecls invocation.'}
if r.returncode==0:record['checked_count']=int((out/'checked-count.txt').read_text())
(out/'command.json').write_text(json.dumps(record,indent=2)+'\n');print(record);assert r.returncode==0,r.stdout+r.stderr
