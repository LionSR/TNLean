from pathlib import Path
import hashlib,json,os,re,subprocess,time
base=Path('/private/tmp/tnlean-original-compression-sampling');cfg=json.loads((base/'env.json').read_text());out=base/'imported-audit';out.mkdir(exist_ok=True)
rows=json.loads((base/'declarations.json').read_text())+json.loads((base/'inherited-provenance-refresh.json').read_text())
names=[x['declaration'] for x in rows];assert len(names)==15==len(set(names))
s='import TNLean\n\n/-! Imported axiom check of the original-circuit sampling declarations. -/\nset_option linter.hashCommand false\n'
for name in names:
 ns,leaf=name.rsplit('.',1);s+=f'\nnamespace {ns}\n#print axioms {leaf}\nend {ns}\n'
s+='\nrun_cmd do\n  let e ← Lean.getEnv\n  let ns := e.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)\n  IO.FS.writeFile "imported-modules.json" (Lean.Json.compress (Lean.Json.arr ns))\n'
f=out/'Axioms.lean';f.write_text(s)
env=os.environ.copy();env['LEAN_PATH']=cfg['LEAN_PATH'];cmd=[cfg['lean'],*cfg['options'],'-DwarningAsError=true','Axioms.lean']
t=time.monotonic();p=subprocess.run(cmd,cwd=out,env=env,capture_output=True,text=True);log=p.stdout+p.stderr;(out/'axioms.log').write_text(log)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r={'command':cmd,'cwd':str(out),'LEAN_PATH':cfg['LEAN_PATH'],'returncode':p.returncode,'seconds':round(time.monotonic()-t,3),'source_sha256':sha(f),'log_sha256':sha(out/'axioms.log')};(out/'audit-command.json').write_text(json.dumps(r,indent=2)+'\n');assert p.returncode==0,log
found={}
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",log,re.S):
 n,a=m.groups();found[n]=[] if a is None else [v.strip() for v in a.split(',')]
assert set(found)==set(names)
assert all(set(a)<={'propext','Classical.choice','Quot.sound'} for a in found.values())
(out/'axiom-dependencies.json').write_text(json.dumps(found,indent=2)+'\n')
roots=[Path(p) for p in cfg['LEAN_PATH'].split(':')];dependencies=[]
for mod in json.loads((out/'imported-modules.json').read_text()):
 rel=Path(mod.replace('.','/')+'.olean');artifact=next((root/rel for root in roots if (root/rel).is_file()),None);assert artifact,mod
 dependencies.append({'module':mod,'artifact':str(artifact),'resolved_artifact':str(artifact.resolve()),'sha256':sha(artifact),'bytes':artifact.stat().st_size})
(out/'imported-dependencies.json').write_text(json.dumps(dependencies,indent=2)+'\n')
r.update({'audited_declarations':len(found),'new_declarations':15,'refactored_declarations':0,'imported_artifacts':len(dependencies),'imported_dependencies_sha256':sha(out/'imported-dependencies.json')});(out/'audit-command.json').write_text(json.dumps(r,indent=2)+'\n')
print('STANDARD_AXIOMS_ONLY',len(found),'ARTIFACTS',len(dependencies),flush=True)
