from pathlib import Path
import hashlib,json,re,subprocess
B=Path('/workspace/scratch/7637e06d0fc2');D=B/'patch-coordinate-validation';R=B/'TNLean-patch-coordinate-stationarity';Q=D/'qic-source'
PIN='378bef486fc0241dee8ad875ccaf659d51d33ac9';BASE='e9311cbbaf55517308f416b008df5ddafcc047c9'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(n,v):(D/n).write_text(json.dumps(v,indent=2)+'\n')
runs=json.loads((D/'actual-runs.json').read_text());seed=json.loads((D/'seed-audit.json').read_text())
mods=['TNLean.PEPS.AreaLaw.RegularizedPatchCoordinate','TNLean.PEPS.AreaLaw.RegularizedPatchStationarity','TNLean.PEPS.AreaLaw.RegularizedPatchMarginal','TNLean.PEPS.AreaLaw','TNLeanTest.RegularizedPatchStationarity','TNLeanTest.RegularizedPatchMarginal','TNLeanTest.RegularizedPatchZeroWeight','PatchCoordinateAxioms']
final=[];closure={}
for m in mods:
 r=next(r for r in reversed(runs) if r['module']==m)
 assert r['exit_code']==0 and r['source_closure_unchanged'],m
 assert r['source_closure_sha256_before']==r['source_closure_sha256_after']
 assert all(sha(Path(p))==h for p,h in r['source_closure_sha256_before'].items()),m
 assert sha(Path(r['source']))==r['source_sha256']
 assert sha(D/'lib'/Path(m.replace('.','/')).with_suffix('.olean'))==r['artifact_sha256']
 for f in ['90s','-j1','-Dpp.unicode.fun=true','-DrelaxedAutoImplicit=false','-DmaxSynthPendingDepth=3','-Dlinter.mathlibStandardSet=true','-DwarningAsError=true']:assert f in r['command']
 if m.startswith('TNLeanTest.'):assert '-DautoImplicit=false' in r['command']
 if m!='PatchCoordinateAxioms':assert not Path(r['log']).read_text(),m
 final.append(r);closure.update(r['source_closure_sha256_before'])
dump('final-runs.json',final)
rows=[]
for src,h in closure.items():
 p=Path(src)
 if p.is_relative_to(Q):root=Q
 elif p.is_relative_to(R):root=R
 else:continue
 m='.'.join(p.relative_to(root).with_suffix('').parts);a=D/'lib'/p.relative_to(root).with_suffix('.olean');ha=sha(a)
 matching=[r for r in runs if r['module']==m and r['exit_code']==0 and r['source_sha256']==h and r.get('artifact_sha256')==ha]
 if matching:
  r=matching[-1];origin={'kind':'compiled','record':str(D/'actual-runs.json'),'command':r['command'],'original_artifact':r['command'][r['command'].index('-o')+1]}
 else:
  r=next(r for r in seed if r['module']==m and r['source_sha256']==h and r['artifact_sha256']==ha)
  original_records=json.loads(Path(r['record']).read_text())
  assert any(o['module']==m and o['exit_code']==0 and o['source_sha256']==h and o.get('artifact_sha256')==ha for o in original_records)
  assert sha(Path(r['original_artifact']))==ha
  origin={'kind':'audited-copy','record':r['record'],'command':r['original_command'],'original_artifact':r['original_artifact']}
 if root==Q:
  data=subprocess.check_output(['git','-C',str(B/'QICLean'),'show',PIN+':'+p.relative_to(Q).as_posix()])
  assert hashlib.sha256(data).hexdigest()==h
 rows.append({'module':m,'source':src,'source_sha256':h,'artifact':str(a),'artifact_sha256':ha,**origin})
dump('source-artifact-audit.json',rows)
raw=Path(final[-1]['log']).read_text();names=json.loads((D/'public-declarations.json').read_text());found=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",raw,re.S)
assert len(found)==len(names)==18 and {n for n,_ in found}==set(names)
assert all(set(a.strip() for a in axs.split(','))<={'propext','Classical.choice','Quot.sound'} for _,axs in found)
(D/'public-axioms.raw.txt').write_text(raw)
for f in ['lake-manifest.json','docbuild/lake-manifest.json']:
 p=next(x for x in json.loads((R/f).read_text())['packages'] if x['name']=='qiclean');assert p['rev']==p['inputRev']==PIN
assert (R/'lakefile.toml').read_text().count(PIN)==1
assert subprocess.run(['git','-C',str(R),'merge-base','--is-ancestor',BASE,'HEAD']).returncode==0
source_freeze={str(Path(r['source']).relative_to(R)):r['source_sha256'] for r in final if Path(r['source']).is_relative_to(R)}
dump('source-freeze.json',source_freeze)
summary={'base':BASE,'base_status':'published-unmerged-TN8822','accepted_qic':PIN,'qic_pins_verified':True,'public_declarations':18,'axiom_reports_complete':True,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'audited_source_artifact_pairs':len(rows),'source_closure_unchanged':True,'strict_runs':[{'module':r['module'],'elapsed_seconds':r['elapsed_seconds'],'source_sha256':r['source_sha256'],'log':r['log']} for r in final], 'mathlib_commit':subprocess.check_output(['git','-C',str(B/'TNLean/.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip(),'mathlib_olean_sha256':sha(B/'TNLean/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean'),'full_lake_build':'not run locally; exact source-audited overlay and strict targeted checks only','mathlib_cold_build':False,'fabricated_lake_traces':False,'remote_mutations':'none','regressions':['actual feasible nonminimizer has real pairing3/8 and fails IsMinOn','actual zero-weight feasible minimizer fails to commute with canonical actual marginal','Fin2 repeated region update leaves unselected occurrence unchanged','Fin2 insertion0=L1K and insertion1=KL0 preserve reverse product order','heterogeneous dimensions2/3','empty region and empty filter family','complex(1,i) PauliY expectation and trace equal2']}
dump('validation-summary.json',summary)
print(json.dumps(summary,indent=2))
