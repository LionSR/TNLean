from pathlib import Path
import hashlib,importlib.util,json,re,subprocess,sys
sys.dont_write_bytecode=True
b=Path('/private/tmp/tnlean-source-resource-integration');root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-resource-integration')
sp=importlib.util.spec_from_file_location('p',root/'scripts/check_openai_provenance.py');p=importlib.util.module_from_spec(sp);sp.loader.exec_module(p)
sha=lambda t:hashlib.sha256(t).hexdigest();rows=json.loads((b/'input-output-original-manifest.json').read_text())
ds=json.loads((b/'declarations.json').read_text());pres=json.loads((b/'source-preservation.json').read_text())
originals=b/'original-sources';removed=None
for row in rows:
 n=row['module'];data=Path(row['source']).read_bytes();assert sha(data)==row['sha256'];(originals/(n+'.lean')).write_bytes(data);t=data.decode().rstrip()+'\n'
 if n=='SeparatedOutputCoordinates':
  start=t.index('/-- Physical basis projection');end=t.index('end TNLean.PEPS.PairEffect.Word',start)
  removed=t[start:end];t=t[:start]+t[end:]
 priv=set(re.findall(r'^\s*private\s+(?:theorem|lemma|def|abbrev|instance)\s+([^\s:(]+)',p.lean_parts(t)[0],re.M))
 names=sorted(x for x in p.declarations(t) if x.rsplit('.',1)[-1] not in priv)
 rel=f'TNLean/PEPS/Approximation/{n}.lean'
 notice=['/-!','Source: polynomial-PEPS Theorem 5.2, 04-compression.tex, lines 409–480.',
 'Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.',
 'Independently formalized; no upstream Lean proof text reused.','']
 for i,name in enumerate(names,1):
  ident=f'8769-source-resource-{n.lower()}-{i:02d}'
  notice+=['Provenance-ID: '+ident,name if len(name)<=100 else f'https://lionsr.github.io/TNLean/docs/{rel[:-5]}.html#{name}']
  ds.append({'id':ident,'path':rel,'declaration':name,'paper_label':'eq:compression-exterior-input'})
 notice+=['-/',''];e=t.index('-/',t.index('/-!'))+2;t=t[:e]+'\n\n'+'\n'.join(notice)+t[e:]
 (root/rel).write_text(t)
 before=data.decode().replace(removed,'') if n=='SeparatedOutputCoordinates' else data.decode()
 assert p.lean_parts(before)[0].split()==p.lean_parts(t)[0].split(),n
 pres.append({'original_module':n,'original_path':row['source'],'original_sha256':sha(data),'proof_tokens_preserved':True,'promotion':'repr_effectMap reused from PhysicalOutputContraction' if n=='SeparatedOutputCoordinates' else None,'production':[{'path':rel,'sha256':sha(t.encode())}]})
 print(n,len(names),len(t.splitlines()),flush=True)

# Promote the existing proof, preserving its original body and existing uses.
rel='TNLean/PEPS/Approximation/PhysicalOutputContraction.lean';f=root/rel;t=f.read_text();old=t
assert t.count('private theorem repr_effectMap')==1;t=t.replace('private theorem repr_effectMap','theorem repr_effectMap')
identifier='8769-source-resource-physicaloutputcontraction-repr';name='TNLean.PEPS.PairEffect.Word.repr_effectMap'
notice=('\n\n/-!\nSource: polynomial-PEPS Theorem 5.2, 04-compression.tex, lines 409–450.\n'
 'Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.\n'
 'Independently formalized; no upstream Lean proof text reused.\n'
 'Provenance-ID: '+identifier+'\n'+name+'\n-/')
e=t.index('-/',t.index('/-!'))+2;t=t[:e]+notice+t[e:];f.write_text(t)
ds.append({'id':identifier,'path':rel,'declaration':name,'paper_label':'eq:compression-exterior-contraction'})
(b/'repr-effectMap-promotion.patch').write_bytes(subprocess.check_output(['git','diff','--',rel],cwd=root))
pres.append({'original_module':'PhysicalOutputContraction','original_revision':'456204230ab8548568dbbccdac39b894d1539ff5','original_sha256':sha(old.encode()),'promotion':'private theorem repr_effectMap made public; mathematical statement, proof and existing call site unchanged','production':[{'path':rel,'sha256':sha(t.encode())}]})
refresh=[]
for shard in (root/'docs/provenance/openai-math.d').glob('*.json'):
 j=json.loads(shard.read_text());entries=j['entries'] if isinstance(j,dict) else j
 for x in entries:
  if x.get('downstream',{}).get('path')==rel:refresh.append({'id':x['id'],'declaration':x['downstream']['declaration'],'path':rel,'shard':str(shard.relative_to(root))})
(b/'inherited-provenance-refresh.json').write_text(json.dumps(refresh,indent=2)+'\n')
(b/'declarations.json').write_text(json.dumps(ds,indent=2)+'\n');(b/'source-preservation.json').write_text(json.dumps(pres,indent=2)+'\n')
subprocess.run(['python3','scripts/generate_import_aggregators.py'],cwd=root,check=True)
print('TOTAL',len(ds),'REFRESH',len(refresh))
