from pathlib import Path
import ctypes,hashlib,importlib.util,json,os,re,subprocess,sys
sys.dont_write_bytecode=True
root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-original-compression-sampling');b=Path('/private/tmp/tnlean-original-compression-sampling');b.mkdir(exist_ok=True);(b/'original-sources').mkdir(exist_ok=True)
base='a2cb859ca1ce60c154d58e9fdce20c2fec278fb8';assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==base
spec=importlib.util.spec_from_file_location('provenance',root/'scripts/check_openai_provenance.py');p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
sha=lambda x:hashlib.sha256(x).hexdigest();save=lambda path,x:path.write_text(json.dumps(x,indent=2)+'\n')
name,expected,evidence=sys.argv[1:]
x={'module':'TNLean.PEPS.Approximation.'+name,'source':'/tmp/'+name+'.lean','sha256':expected,'original_evidence':evidence}
assert not (root/(x['module'].replace('.','/')+'.lean')).exists()
sources=[x]
rows=json.loads((b/'declarations.json').read_text());pres=json.loads((b/'source-preservation.json').read_text())
for x in sources:
 original=Path(x['source']);data=original.read_bytes();assert sha(data)==x['sha256'],original
 name=original.stem;t=data.decode();code=p.lean_parts(t)[0];assert not re.search(r'\b(sorry|admit|native_decide|unsafeCast|axiom)\b',code)
 private=set(re.findall(r'^\s*private\s+(?:theorem|lemma|def|abbrev|instance)\s+([^\s:(]+)',code,re.M));names=sorted(n for n in p.declarations(t) if n.rsplit('.',1)[-1] not in private)
 rel=x['module'].replace('.','/')+'.lean';assert not (root/rel).exists();(b/'original-sources'/original.name).write_bytes(data)
 label='thm:compression';notice=['/-!','Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,',label+'; Theorem 5.2 and its proof.','Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.','Independently formalized; no upstream Lean proof text reused.','']
 for i,n in enumerate(names,1):
  ident=f'8769-original-sampling-{name.lower()}-{i:02d}';notice+=['Provenance-ID: '+ident,n];rows.append({'id':ident,'path':rel,'declaration':n,'paper_label':label})
 notice+=['-/',''];end=t.index('-/',t.index('/-!'))+2;t=t[:end]+'\n\n'+'\n'.join(notice)+t[end:];assert p.lean_parts(t)[0].split()==code.split();(root/rel).write_text(t)
 pres.append({'original_module':name,'original_path':str(original),'original_sha256':sha(data),'proof_tokens_preserved':True,'production':[{'path':rel,'sha256':sha(t.encode())}]})
handoff=json.loads((b/'handoff.json').read_text());handoff['sources'].append(x);sources=handoff['sources']
save(b/'declarations.json',rows);save(b/'source-preservation.json',pres);save(b/'handoff.json',handoff)
subprocess.run(['python3','scripts/generate_import_aggregators.py'],cwd=root,check=True)
imports={}
for f in [*(root/'TNLean').rglob('*.lean'),root/'TNLean.lean']:
 if '/Archive/' in str(f):continue
 imports[str(f.relative_to(root))[:-5].replace('/','.')]=re.findall(r'^import (\S+)',f.read_text(),re.M)
selected={x['module'] for x in sources};changed=sorted(selected)
while True:
 n=len(selected);selected.update(m for m,deps in imports.items() if any(x in selected for x in deps))
 if n==len(selected):break
ordered=[]
def visit(m):
 if m in ordered:return
 for d in imports[m]:
  if d in selected:visit(d)
 ordered.append(m)
for m in sorted(selected):visit(m)
save(b/'build-plan.json',{'selected_modules':ordered,'changed_modules':changed});print('ADOPTED',len(sources),'MODULES',len(rows),'PUBLIC; STRICT',len(ordered))
