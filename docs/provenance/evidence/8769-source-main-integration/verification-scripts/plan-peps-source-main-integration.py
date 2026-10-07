from pathlib import Path
import json,subprocess,sys
root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-integration')
qic=Path('/Users/siruilu/Local/agentFormalization/QICLean/worktrees/area-law-pure-tensor-power')
sys.path.insert(0,str(root/'scripts'));from lean_import_syntax import strip_lean_comments
out=Path('/private/tmp/tnlean-source-main-integration');out.mkdir(exist_ok=True)
def git(r,*a):return subprocess.check_output(['git','-C',str(r),*a],text=True).strip()
def module(path):return str(path).removesuffix('.lean').replace('/','.')
def imports(p):
 s,err=strip_lean_comments(p.read_text());assert err is None,(p,err)
 return [x for line in s.splitlines() if line.startswith('import ') for x in line.split()[1:]]
def files(r,package):return {module(p.relative_to(r)):p for p in [r/(package+'.lean'),*(r/package).rglob('*.lean')] if 'Archive' not in p.parts}
tnf=files(root,'TNLean');qf=files(qic,'QICLean')
old='8f05f840cfffd50d4f2870f59ade606639d34869';new=git(qic,'rev-parse','HEAD')
changedQ={module(p) for p in git(qic,'diff','--name-only',old,new,'--','QICLean','QICLean.lean').splitlines() if p.endswith('.lean')}
changedTN={module(p) for p in git(root,'diff','--name-only','80bc49d17e833795fba00bfeaf1bd053649c4070','HEAD','--','TNLean','TNLean.lean').splitlines() if p.endswith('.lean')}
deps={m:imports(p) for m,p in (tnf|qf).items()}
affected=changedQ|changedTN
while True:
 newA=affected|{m for m,d in deps.items() if affected.intersection(d)}
 if newA==affected:break
 affected=newA
sel=set(tnf).intersection(affected);todo={m:set(deps[m])&sel for m in sel};order=[]
while todo:
 ready=sorted(m for m,d in todo.items() if not d);assert ready,'Cycle'
 order+=ready
 for m in ready:del todo[m]
 for d in todo.values():d.difference_update(ready)
r={'tn_head':git(root,'rev-parse','HEAD'),'qic_old':old,'qic_candidate':new,'changed_qic':sorted(changedQ),'changed_tn':sorted(changedTN),'affected_qic':sorted(set(qf)&affected),'selected_tn':order,'unaffected_tn_count':len(set(tnf)-sel),'dependencies':{m:deps[m] for m in order}}
(out/'verification-plan.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:len(v) if isinstance(v,list) else v for k,v in r.items() if k!='dependencies'},indent=2))
