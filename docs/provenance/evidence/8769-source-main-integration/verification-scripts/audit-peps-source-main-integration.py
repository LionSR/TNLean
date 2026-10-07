from pathlib import Path
import datetime,hashlib,json,os,re,subprocess,time
base=Path('/private/tmp/tnlean-source-main-integration');repo=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-integration');cfg=json.loads((base/'env.json').read_text());out=base/'imported-audit';out.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
shards=['8768-source-preparation','8769-party-factorization','8769-unused-pair-sources','8769-common-source-spaces','8769-source-gate-density','8769-source-block-contraction','8769-party-coarsening','8769-selective-source-preparation','8769-chronological-source-expansion','8769-fixed-chronological-sources']
entries=[e for s in shards for e in json.loads((repo/'docs/provenance/openai-math.d'/f'{s}.json').read_text())['entries']]
names=[e['downstream']['declaration'] for e in entries];assert len(names)==342==len(set(names))
text='import TNLean\n\n/-! Kernel axiom audit of the integrated source constructions. -/\nset_option linter.hashCommand false\n'
for n in names:
 ns,leaf=n.rsplit('.',1);text+=f'\nnamespace {ns}\n#print axioms {leaf}\nend {ns}\n'
text+='\nrun_cmd do\n  let environment ← Lean.getEnv\n  let names := environment.header.moduleNames.map (fun n ↦ Lean.Json.str n.toString)\n  IO.FS.writeFile\n    '+json.dumps(str(out/'imported-modules.json'))+'\n    (Lean.Json.compress (Lean.Json.arr names))\n'
f=out/'Axioms.lean';f.write_text(text)
env=os.environ.copy();env['LEAN_PATH']=cfg['LEAN_PATH'];cmd=[cfg['lean'],*cfg['options'],'-DwarningAsError=true',str(f)]
t=time.monotonic();p=subprocess.run(cmd,cwd=repo,env=env,capture_output=True,text=True);log=p.stdout+p.stderr;(out/'axioms.log').write_text(log)
record={'command':cmd,'cwd':str(repo),'LEAN_PATH':cfg['LEAN_PATH'],'seconds':round(time.monotonic()-t,3),'returncode':p.returncode,'source_sha256':sha(f),'log_sha256':sha(out/'axioms.log')};(out/'audit-command.json').write_text(json.dumps(record,indent=2)+'\n')
assert p.returncode==0,log
found={}
for m in re.finditer(r"'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",log,re.S):
 name,atoms=m.groups();found[name]=[] if atoms is None else [s.strip() for s in atoms.split(',')]
assert set(found)==set(names),(set(names)-set(found),set(found)-set(names))
assert all(set(a)<= {'propext','Classical.choice','Quot.sound'} for a in found.values())
(out/'axiom-dependencies.json').write_text(json.dumps(found,indent=2)+'\n')
roots=[Path(x) for x in cfg['LEAN_PATH'].split(':')];deps=[]
for m in json.loads((out/'imported-modules.json').read_text()):
 rel=Path(m.replace('.','/')+'.olean');p=next((r/rel for r in roots if (r/rel).is_file()),None);assert p,m
 deps.append({'module':m,'artifact':str(p),'resolved_artifact':str(p.resolve()),'sha256':sha(p),'bytes':p.stat().st_size})
(out/'imported-dependencies.json').write_text(json.dumps(deps,indent=2)+'\n')
record.update({'audited_declarations':len(found),'imported_artifacts':len(deps),'imported_dependencies_sha256':sha(out/'imported-dependencies.json')});(out/'audit-command.json').write_text(json.dumps(record,indent=2)+'\n')
print('STANDARD_AXIOMS_ONLY',len(found),'IMPORTED_ARTIFACTS_HASHED',len(deps),flush=True)
