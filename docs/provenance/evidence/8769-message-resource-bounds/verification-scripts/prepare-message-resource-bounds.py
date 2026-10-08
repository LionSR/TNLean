from pathlib import Path
import ctypes,hashlib,importlib.util,json,os,re,subprocess,sys
sys.dont_write_bytecode=True
root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-message-resource-bounds');b=Path('/private/tmp/tnlean-message-resource-bounds');b.mkdir(exist_ok=True);(b/'original-sources').mkdir(exist_ok=True)
base='a1be4cc9ba5a7e8f20bd24267b5c4cff77563a45';assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==base
spec=importlib.util.spec_from_file_location('provenance',root/'scripts/check_openai_provenance.py');p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
sha=lambda x:hashlib.sha256(x).hexdigest();save=lambda path,x:path.write_text(json.dumps(x,indent=2)+'\n')
plans=[('/private/tmp/tnlean-actual-corrected-bound/message-local-expansion-checks/checked-sources.json','sources'),('/private/tmp/tnlean-party-gate-composition/final-verification-20261008/checked-sources.json','modules'),('/private/tmp/tnlean-message-monomial/message-monomial-checks/source-manifest.json','sources'),('/private/tmp/tnlean-message-gate/final-verification-20261008/checked-sources.json','modules'),('/private/tmp/tnlean-source-alphabet-polynomial/source-alphabet-polynomial-checks/source-manifest.json','sources'),('/private/tmp/tnlean-finite-input-memory/final-verification-20261008/checked-sources.json','modules'),('/private/tmp/tnlean-uniform-compression/physical-first-polynomial-checks/checked-sources.json','sources'),('/private/tmp/tnlean-uniform-compression/physical-first-network-resource-checks/checked-sources.json','sources')]
sources=[]
for path,key in plans:
 for x in json.loads(Path(path).read_text())[key]:
  src=x.get('source_path',x.get('source'));name=Path(src).stem
  sources.append({'module':'TNLean.PEPS.Approximation.'+name,'source':'/tmp/'+name+'.lean','sha256':x.get('source_sha256',x.get('sha256')),'original_evidence':str(Path(path).parent)})
assert len(sources)==11
rows=[];pres=[]
for x in sources:
 original=Path(x['source']);data=original.read_bytes();assert sha(data)==x['sha256'],original
 name=original.stem;t=data.decode();code=p.lean_parts(t)[0];assert not re.search(r'\b(sorry|admit|native_decide|unsafeCast|axiom)\b',code)
 private=set(re.findall(r'^\s*private\s+(?:theorem|lemma|def|abbrev|instance)\s+([^\s:(]+)',code,re.M));names=sorted(n for n in p.declarations(t) if n.rsplit('.',1)[-1] not in private)
 rel=x['module'].replace('.','/')+'.lean';assert not (root/rel).exists();(b/'original-sources'/original.name).write_bytes(data)
 label='thm:compression';notice=['/-!','Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,',label+'; Theorem 5.2 and its proof.','Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.','Independently formalized; no upstream Lean proof text reused.','']
 for i,n in enumerate(names,1):
  ident=f'8769-message-resources-{name.lower()}-{i:02d}';notice+=['Provenance-ID: '+ident,n];rows.append({'id':ident,'path':rel,'declaration':n,'paper_label':label})
 notice+=['-/',''];end=t.index('-/',t.index('/-!'))+2;t=t[:end]+'\n\n'+'\n'.join(notice)+t[end:];assert p.lean_parts(t)[0].split()==code.split();(root/rel).write_text(t)
 pres.append({'original_module':name,'original_path':str(original),'original_sha256':sha(data),'proof_tokens_preserved':True,'production':[{'path':rel,'sha256':sha(t.encode())}]})
assert len(rows)==65,len(rows)
save(b/'declarations.json',rows);save(b/'source-preservation.json',pres);save(b/'handoff.json',{'source_parent':base,'sources':sources});save(b/'inherited-provenance-refresh.json',[])
old=Path('/private/tmp/tnlean-approximate-physical-output/artifacts');art=b/'artifacts';art.mkdir(exist_ok=True);libc=ctypes.CDLL('/usr/lib/libSystem.B.dylib',use_errno=True);clones=[];links=0
for package in ['TNLean','QICLean']:
 for f in [*(old/package).rglob('*'),*old.glob(package+'.*')]:
  if not f.is_file():continue
  target=art/f.relative_to(old);target.parent.mkdir(parents=True,exist_ok=True);assert not target.exists() and not target.is_symlink()
  if f.is_symlink():target.symlink_to(f.resolve())
  else:
   frozen=b/'dependencies'/f.relative_to(old);frozen.parent.mkdir(parents=True,exist_ok=True);assert libc.clonefile(os.fsencode(f),os.fsencode(frozen),0)==0;frozen.chmod(0o444);assert sha(f.read_bytes())==sha(frozen.read_bytes());clones.append({'original':str(f),'frozen':str(frozen),'sha256':sha(frozen.read_bytes())});target.symlink_to(frozen)
  links+=1
cfg=json.loads(Path('/private/tmp/tnlean-approximate-physical-output/env.json').read_text());cfg.update(source_root=str(root),output_root=str(art),LEAN_PATH=str(Path(cfg['lean']).parent.parent/'lib/lean')+':'+str(art)+':/private/tmp/tnlean-artifact-recovery-20261008/gaussian/artifacts');save(b/'env.json',cfg);save(b/'environment-preparation.json',{'source_parent':base,'parent_source_revision':'1213a68ed511bf20c357b72f4ac5a03078b7c677','preserved_artifacts':clones,'readonly_links':links})
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
save(b/'build-plan.json',{'selected_modules':ordered,'changed_modules':changed});print('ADOPTED',len(sources),'MODULES',len(rows),'PUBLIC; STRICT',len(ordered),'CLONES',len(clones),'LINKS',links)
