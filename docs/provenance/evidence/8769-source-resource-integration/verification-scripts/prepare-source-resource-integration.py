from pathlib import Path
import hashlib, importlib.util, json, re, shutil, subprocess, sys

sys.dont_write_bytecode = True
root = Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-resource-integration')
base = Path('/private/tmp/tnlean-source-resource-integration')
rev = '8b4483ccad9b1fe9467205cb7173e2da61a13383'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip() == '456204230ab8548568dbbccdac39b894d1539ff5'
assert not (root/'.lake').exists()
spec=importlib.util.spec_from_file_location('policy',root/'scripts/check_openai_provenance.py')
policy=importlib.util.module_from_spec(spec);spec.loader.exec_module(policy)
inventory=json.loads((base/'relay-inventory.json').read_text())
originals=base/'original-sources';originals.mkdir(exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
texts={};preservation=[];declarations=[]
for row in inventory:
 name=row['module'];rel=f'TNLean/PEPS/Approximation/{name}.lean'
 data=subprocess.check_output(['git','show',rev+':'+rel],cwd=root)
 (originals/(name+'.lean')).write_bytes(data);texts[name]=data.decode().rstrip()+'\n'
 preservation.append({'original_module':name,'original_revision':rev,'original_path':rel,'original_sha256':sha(data),'original_lines':len(data.decode().splitlines())})
data=Path('/tmp/SourceCircuitResourceBounds.lean').read_bytes()
(originals/'SourceCircuitResourceBounds.lean').write_bytes(data)
texts['SourceCircuitResourceBounds']=data.decode().rstrip()+'\n'
preservation.append({'original_module':'SourceCircuitResourceBounds','original_path':'/tmp/SourceCircuitResourceBounds.lean','original_sha256':sha(data),'original_lines':len(data.decode().splitlines())})

# Split only at the namespace boundary; every declaration retains its name and text.
t=texts['EffectCircuitReplacement'];point=t.index('namespace EffectCircuit\n/-- The actual auxiliary register occurrences')
texts['EffectCircuitPreparation']=t[:point]+'end TNLean.PEPS.PairEffect\n'
header=t[:t.index('import ')]
texts['EffectCircuitPreparation']=texts['EffectCircuitPreparation'].replace(
 '# Elimination of pair effects in distributed circuits', '# Preparation and private inputs for distributed circuits')
texts['EffectCircuitReplacement']=(header+'import TNLean.PEPS.Approximation.EffectCircuitPreparation\n\n'
 '/-!\n# Source-only replacement with retained auxiliary registers\n\n'
 'Each original nonprivate occurrence is replaced by a prepared-source expansion.\n'
 'The auxiliary registers of preceding occurrences remain spectators.\n'
 'Source: polynomial-PEPS, `04-compression.tex`, lines 199–229.\n-/\n'
 'noncomputable section\nopen scoped TensorProduct\nopen ContinuousLinearMap\n'
 'namespace TNLean.PEPS.PairEffect\nvariable {P : Type}\n\n'+t[point:])

for name,t in texts.items():
 private=set(re.findall(r'^\s*private\s+(?:theorem|lemma|def|abbrev|instance)\s+([^\s:(]+)',policy.lean_parts(t)[0],re.M))
 names=sorted(n for n in policy.declarations(t) if n.rsplit('.',1)[-1] not in private)
 rel=f'TNLean/PEPS/Approximation/{name}.lean'
 notice=['/-!','Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,',
 'eq:compression-effect-circuit-error; Theorem 5.2, lines 137–151 and 199–251.',
 'Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.',
 'Independently formalized; no upstream Lean proof text reused.','']
 for i,n in enumerate(names,1):
  identifier=f'8769-source-resource-{name.lower()}-{i:02d}'
  declaration=n if len(n)<=100 else f'https://lionsr.github.io/TNLean/docs/{rel[:-5]}.html#{n}'
  notice += ['Provenance-ID: '+identifier,declaration]
  declarations.append({'id':identifier,'path':rel,'declaration':n,'paper_label':'eq:compression-effect-circuit-error'})
 notice+=['-/','']
 end=t.index('-/',t.index('/-!'))+2
 t=t[:end]+'\n\n'+'\n'.join(notice)+t[end:]
 (root/rel).write_text(t)
 assert len(t.splitlines())<=1000,(name,len(t.splitlines()))
 print(name,len(names),len(t.splitlines()),flush=True)

# Byte-level decomposition record plus token preservation after removing only imports,
# scope wrappers, and comments. This includes the module split but no proof rewriting.
def semantic_tokens(t):
 c=policy.lean_parts(t)[0]
 return re.sub(r'^(?:import |namespace |end(?:\s|$)|noncomputable section|open |variable \{P : Type\}).*$', '',c,flags=re.M).split()
for row in preservation:
 n=row['original_module'];dest=['EffectCircuitPreparation','EffectCircuitReplacement'] if n=='EffectCircuitReplacement' else [n]
 before=semantic_tokens((originals/(n+'.lean')).read_text())
 after=sum((semantic_tokens((root/f'TNLean/PEPS/Approximation/{m}.lean').read_text()) for m in dest),[])
 assert before==after,n
 row.update(proof_tokens_preserved=True,production=[{'path':f'TNLean/PEPS/Approximation/{m}.lean','sha256':sha((root/f'TNLean/PEPS/Approximation/{m}.lean').read_bytes())} for m in dest])
(base/'source-preservation.json').write_text(json.dumps(preservation,indent=2)+'\n')
(base/'declarations.json').write_text(json.dumps(declarations,indent=2)+'\n')

chapter='blueprint/src/chapter/ch24_peps_source_only_reduction.tex'
(root/chapter).write_bytes(subprocess.check_output(['git','show',rev+':'+chapter],cwd=root))
content=root/'blueprint/src/content.tex';s=content.read_text();entry='\\input{chapter/ch24_peps_source_only_reduction}'
assert entry not in s
anchor='\\input{chapter/ch24_peps_source_physical}'
assert anchor in s
content.write_text(s.replace(anchor,anchor+'\n'+entry))
ledger=root/'docs/tactic_patterns.md';s=ledger.read_text()
old=subprocess.check_output(['git','show',rev+':docs/tactic_patterns.md'],cwd=root,text=True)
addition=old[old.index('\n### Empty occurrence sets in circuit replacement'):]
assert '### Empty occurrence sets in circuit replacement' not in s
ledger.write_text(s.rstrip()+'\n'+addition)
print('READY',len(texts),len(declarations))
