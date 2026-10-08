from pathlib import Path
import hashlib,json,re,shutil,subprocess
b=Path('/private/tmp/tnlean-source-resource-integration');root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-resource-integration');folder=root/'TNLean/PEPS/Approximation'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
historical=b/'initial-checks/before-transport-promotion';historical.mkdir(parents=True,exist_ok=True)
shutil.copytree(b/'imported-audit',historical/'imported-audit')
shutil.copy2(b/'build-commands.json',historical/'build-commands.json')
names=['SourceRegisterPermutation','SourceSlotMaps','SelectiveSourcePreparation','EffectCircuitPreparation']
before={n:(folder/(n+'.lean')).read_text() for n in names}
for n,t in before.items():(historical/(n+'.lean')).write_text(t)
t=before['SourceRegisterPermutation'];start=t.index('/-- Evaluation under equal register lists');end=t.index('\nend TNLean.PEPS.PairEffect.Word',start);theorem=t[start:end].rstrip()+'\n'
name='TNLean.PEPS.PairEffect.Word.eval_castLayouts_apply_heq';ident='8769-source-resource-sourceregisterpermutation-13'
leaf='''/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordRestriction

/-!
# Evaluation after identifying register lists

The evaluation of an actual word is compatible with the canonical identification
of equal input and output lists. This shared result is used by source-slot maps,
selective preparation, source-position permutations, and effect replacement.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–251 and 409–434.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-exterior-input.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
Provenance-ID: '''+ident+'\n'+name+'''
-/

namespace TNLean.PEPS.PairEffect.Word

'''+theorem+'\nend TNLean.PEPS.PairEffect.Word\n'
(folder/'WordEvaluationTransport.lean').write_text(leaf)
for n,t in before.items():
 if n=='SourceRegisterPermutation':
  t=t[:start]+t[end:];t=t.replace('Provenance-ID: '+ident+'\n'+name+'\n','')
 else:
  pos=t.index('private theorem eval_castLayouts_apply_heq');a=pos if n=='EffectCircuitPreparation' else t.rfind('/--',0,pos);e=t.index('\n\n',pos);t=t[:a]+t[e+2:]
  if n in ['SourceSlotMaps','SelectiveSourcePreparation']:
   t=t.replace('eval_castLayouts_apply_heq','Word.eval_castLayouts_apply_heq')
 p=list(re.finditer(r'^import .+$',t,re.M))[-1].end();t=t[:p]+'\nimport TNLean.PEPS.Approximation.WordEvaluationTransport'+t[p:]
 (folder/(n+'.lean')).write_text(t)

ds=json.loads((b/'declarations.json').read_text())
for r in ds:
 if r['declaration']==name:r['path']='TNLean/PEPS/Approximation/WordEvaluationTransport.lean'
(b/'declarations.json').write_text(json.dumps(ds,indent=2)+'\n')
refresh=json.loads((b/'inherited-provenance-refresh.json').read_text());targets={f'TNLean/PEPS/Approximation/{n}.lean' for n in ['SourceSlotMaps','SelectiveSourcePreparation']}
for shard in (root/'docs/provenance/openai-math.d').glob('*.json'):
 for e in json.loads(shard.read_text())['entries']:
  if e.get('downstream',{}).get('path') in targets:refresh.append({'id':e['id'],'declaration':e['downstream']['declaration'],'path':e['downstream']['path'],'shard':str(shard.relative_to(root))})
(b/'inherited-provenance-refresh.json').write_text(json.dumps(refresh,indent=2)+'\n')
pres=json.loads((b/'source-preservation.json').read_text())
for r in pres:
 if r['original_module'] in names:
  r['prior_source_preservation']=r.pop('proof_tokens_preserved',True)
  r['refactor']='Reuse one unchanged public evaluation-transport theorem; remove the local duplicate.'
 for v in r['production']:v['sha256']=sha(root/v['path'])
(b/'source-preservation.json').write_text(json.dumps(pres,indent=2)+'\n')
(b/'transport-promotion.json').write_text(json.dumps({'public_declaration':name,'new_path':'TNLean/PEPS/Approximation/WordEvaluationTransport.lean','original_proof_path':'SourceRegisterPermutation.lean','original_proof_sha256':hashlib.sha256(theorem.encode()).hexdigest(),'call_sites':names,'changed_public_statements':False},indent=2)+'\n')
ledger=root/'docs/tactic_patterns.md';s=ledger.read_text();s+='''

### Evaluation under equal register lists — promoted (2026-10-08)

- **Pattern:** Apply a word whose input and output register lists have been
  identified to a vector identified with the original input.
- **Reuse:** `Word.eval_castLayouts_apply_heq` in
  `TNLean/PEPS/Approximation/WordEvaluationTransport.lean` is the existing checked
  public proof from `SourceRegisterPermutation`. Its lower import position makes
  it available to `SourceSlotMaps`, `SelectiveSourcePreparation`,
  `SourceRegisterPermutation`, and `EffectCircuitPreparation`.
- **Refactor:** Remove the three identical private copies and move the public
  proof unchanged. Every call now uses the same declaration. Source inventories,
  prepared vectors, public hypotheses, and conclusions are unchanged.
- **Scouting:** `Word.eval_castLayouts_heq` already identifies the two maps;
  the value statement additionally identifies their dependent input vectors.
  Its proof uses core `congrArg`, `eq_of_heq`, and `heq_of_eq`; no custom tactic
  or new generic congruence theorem is introduced.

### Physical projection coordinates — promoted (2026-10-08)

- **Pattern:** Taking a physical basis component and then a discarded coordinate
  is the same as taking the tensor-product coordinate.
- **Reuse:** The existing proof `Word.repr_effectMap` in
  `PhysicalOutputContraction.lean` is public. Its original physical-output matrix
  consumer and the new `SeparatedOutputCoordinates` consumer use that one proof.
  The proposed duplicate in the latter module is removed.
''';ledger.write_text(s)
subprocess.run(['python3','scripts/generate_import_aggregators.py'],cwd=root,check=True)
imports={}
for f in [*root.joinpath('TNLean').rglob('*.lean'),root/'TNLean.lean']:
 if '/Archive/' not in str(f):imports[str(f.relative_to(root))[:-5].replace('/','.')]=re.findall(r'^import (\S+)',f.read_text(),re.M)
changed={x['path'][:-5].replace('/','.') for x in ds+refresh};selected=set(changed)
while True:
 old=len(selected);selected.update(m for m,deps in imports.items() if any(x in selected for x in deps))
 if old==len(selected):break
ordered=[]
def visit(m):
 if m in ordered:return
 for x in imports[m]:
  if x in selected:visit(x)
 ordered.append(m)
for m in sorted(selected):visit(m)
(b/'build-plan.json').write_text(json.dumps({'selected_modules':ordered,'changed_modules':sorted(changed)},indent=2)+'\n')
# Only the reverse closure of this new refactor is invalidated; prior exact
# checks outside that closure stay valid.
affected={f'TNLean.PEPS.Approximation.{n}' for n in names+['WordEvaluationTransport']}
while True:
 old=len(affected);affected.update(m for m,deps in imports.items() if any(x in affected for x in deps))
 if old==len(affected):break
records=json.loads((b/'build-commands.json').read_text());kept=[r for r in records if r['module'] not in affected]
(b/'build-commands.json').write_text(json.dumps(kept,indent=2)+'\n')
print('REFRESH',len(refresh),'BUILD',len(ordered),'PRESERVED',len(kept),'RECHECK',len(selected-set(r['module'] for r in kept)),flush=True)
