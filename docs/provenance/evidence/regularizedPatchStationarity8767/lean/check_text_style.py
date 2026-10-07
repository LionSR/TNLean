from pathlib import Path
import os,subprocess,json,hashlib,time
B=Path('/workspace/scratch/7637e06d0fc2');D=B/'patch-coordinate-validation';T=B/'TNLean-patch-coordinate-stationarity';P=D/'TextStyle.lean'
assert subprocess.run(['pgrep','-x','lean'],stdout=subprocess.DEVNULL).returncode==1
files=['TNLean/PEPS/AreaLaw.lean', 'TNLean/PEPS/AreaLaw/RegularizedPatchCoordinate.lean', 'TNLean/PEPS/AreaLaw/RegularizedPatchStationarity.lean', 'TNLean/PEPS/AreaLaw/RegularizedPatchMarginal.lean', 'TNLeanTest/RegularizedPatchStationarity.lean', 'TNLeanTest/RegularizedPatchMarginal.lean', 'TNLeanTest/RegularizedPatchZeroWeight.lean']
snap=lambda:{p:hashlib.sha256((T/p).read_bytes()).hexdigest() for p in files}
pre=snap();env=os.environ.copy();env['LEAN_PATH']=(D/'lean-path.txt').read_text().strip();cmd=['timeout','--signal=INT','--kill-after=5s','90s','lean','-j1','-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true','-DwarningAsError=true','--run',str(P)]
t=time.monotonic();r=subprocess.run(cmd,cwd=T,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(D/'tn-text-style.log').write_text(r.stdout);post=snap();assert pre==post
(D/'tn-text-style-check.json').write_text(json.dumps({'command':cmd,'cwd':str(T),'exit_code':r.returncode,'elapsed_seconds':time.monotonic()-t,'source_sha256_before':pre,'source_sha256_after':post,'source_unchanged':True,'probe_sha256':hashlib.sha256(P.read_bytes()).hexdigest(),'log':'tn-text-style.log'},indent=2)+'\n');print(r.stdout);assert r.returncode==0
