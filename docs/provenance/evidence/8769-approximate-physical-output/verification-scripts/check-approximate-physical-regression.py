from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
b=Path('/private/tmp/tnlean-approximate-physical-output');cfg=json.loads((b/'env.json').read_text());out=b/'regression';out.mkdir(exist_ok=True);sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=Path('/tmp/ApproximateGateRegression.lean');assert sha(src)=='148e04f25e522caa137fadcf4aa285e59c6bdedb91557991b9150d049fbaf59b';shutil.copy2(src,out/src.name)
rows=json.loads(Path('/private/tmp/tnlean-approximate-gates/regression-verification-20261008/declarations.json').read_text());(out/'declarations.json').write_text(json.dumps(rows,indent=2)+'\n');env=os.environ.copy();env['LEAN_PATH']=str(out)+':'+cfg['LEAN_PATH']
def run(name,cmd,source):
 t=time.monotonic();r=subprocess.run(cmd,cwd=out,env=env,capture_output=True,text=True);log=out/(name+'.log');log.write_text(r.stdout+r.stderr);record={'command':cmd,'cwd':str(out),'LEAN_PATH':env['LEAN_PATH'],'returncode':r.returncode,'seconds':round(time.monotonic()-t,3),'source_sha256':sha(source),'log_sha256':sha(log)};(out/(name+'-command.json')).write_text(json.dumps(record,indent=2)+'\n');assert r.returncode==0,r.stdout+r.stderr;return record
cmd=[cfg['lean'],*cfg['options'],'-DwarningAsError=true','-o','ApproximateGateRegression.olean','ApproximateGateRegression.lean'];r=run('build',cmd,out/src.name);r['artifact_sha256']=sha(out/'ApproximateGateRegression.olean');(out/'build-command.json').write_text(json.dumps(r,indent=2)+'\n')
s='import ApproximateGateRegression\nset_option linter.hashCommand false\n'
for row in rows:
 ns,n=row['declaration'].rsplit('.',1);s+=f'\nnamespace {ns}\n#print axioms {n}\nend {ns}\n'
s+='\nrun_cmd do\n  let e ← Lean.getEnv\n  let ns := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)\n  IO.FS.writeFile "imported-modules.json" (Lean.Json.compress (Lean.Json.arr ns))\n'
(out/'Audit.lean').write_text(s);run('audit',[cfg['lean'],*cfg['options'],'-DwarningAsError=true','Audit.lean'],out/'Audit.lean')
found={}
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",(out/'audit.log').read_text(),re.S):
 n,a=m.groups();found[n]=[] if a is None else [v.strip() for v in a.split(',')]
assert set(found)=={r['declaration'] for r in rows};assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in found.values());(out/'axiom-dependencies.json').write_text(json.dumps(found,indent=2)+'\n')
roots=[Path(p) for p in env['LEAN_PATH'].split(':')];deps=[]
for mod in json.loads((out/'imported-modules.json').read_text()):
 rel=mod.replace('.','/')+'.olean';f=next(p/rel for p in roots if (p/rel).is_file());deps.append({'module':mod,'artifact':str(f),'sha256':sha(f)})
(out/'imported-dependencies.json').write_text(json.dumps(deps,indent=2)+'\n');print('REGRESSIONS_PASS',len(found),'IMPORTED',len(deps))
