from pathlib import Path
import ctypes,hashlib,importlib.util,json,os,re,subprocess,sys
sys.dont_write_bytecode=True
root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-approximate-physical-output')
b=Path('/private/tmp/tnlean-approximate-physical-output');b.mkdir(exist_ok=True);(b/'original-sources').mkdir(exist_ok=True)
base='0fa31ddad11ab7a8f06a3a34f1381c3ff974e8bf';assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==base
spec=importlib.util.spec_from_file_location('provenance',root/'scripts/check_openai_provenance.py');p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
sha=lambda x:hashlib.sha256(x).hexdigest()
def save(path,x):path.write_text(json.dumps(x,indent=2)+'\n')
def names(t):
 code=p.lean_parts(t)[0];private=set(re.findall(r'^\s*private\s+(?:theorem|lemma|def|abbrev|instance)\s+([^\s:(]+)',code,re.M))
 return sorted(n for n in p.declarations(t) if n.rsplit('.',1)[-1] not in private)
mods=json.loads(Path('/private/tmp/tnlean-approximate-gates/final-verification-20261008/checked-sources.json').read_text())['modules']
sources=[{'module':x['module'],'source':x['source_path'],'sha256':x['source_sha256']} for x in mods]
sources += [{'module':'TNLean.PEPS.Approximation.'+n,'source':'/tmp/'+n+'.lean','sha256':h} for n,h in [('ApproximateCircuitRealAccuracy','76641c9cd539eb171f474f6488c030cd84e7d8cf4673d61c8b23f2da54d4e057'),('GateCoefficientBounds','183d23466b35df786cd531ab42f2c0fa10d51f8af8b14f4db08f7eba4cae2df9')]]
relay='f15416476c61b343f79d19602dffe8b5489a49f0'
for n in ['AuxiliaryRegisterFiniteness','PhysicalDensityPureInput','PhysicalFirstExchange','PhysicalFirstReadout']:
 data=subprocess.check_output(['git','show',relay+':TNLean/PEPS/Approximation/'+n+'.lean'],cwd=root)
 f=b/'original-sources'/(n+'.lean');f.write_bytes(data)
 sources.append({'module':'TNLean.PEPS.Approximation.'+n,'source':str(f),'sha256':sha(data),'source_revision':relay})
rows=[];pres=[]
helper='TNLean.PEPS.PairEffect.norm_comp_sub_comp_le_one'
oldrel='TNLean/PEPS/Approximation/EffectCircuitError.lean';old=(root/oldrel).read_text();(b/'original-sources'/'EffectCircuitError.lean').write_text(old)
newhelper=(Path('/tmp/ApproximateCircuitError.lean').read_text().split('/-- The elementary')[1].split('/-- Every original circuit')[0])
helperbody='theorem norm_comp_sub_comp_le_one'+newhelper.split('theorem norm_comp_sub_comp_le_one')[1]
assert helperbody.strip() == old.split('private theorem norm_comp_sub_comp_le_one')[1].split('private theorem memory_congr_of_heq')[0].join(['theorem norm_comp_sub_comp_le_one','']).strip()

def add_notice(t,ns,rel,label):
 notice=['/-!','Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,',label+'; Theorem 5.2 and its proof.','Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.','Independently formalized; no upstream Lean proof text reused.','']
 name=Path(rel).stem
 for i,n in enumerate(ns,1):
  ident=f'8769-approximate-physical-{name.lower()}-{i:02d}';notice+=['Provenance-ID: '+ident,n];rows.append({'id':ident,'path':rel,'declaration':n,'paper_label':label})
 notice+=['-/',''];end=t.index('-/',t.index('/-!'))+2
 return t[:end]+'\n\n'+'\n'.join(notice)+t[end:]
for x in sources:
 original=Path(x['source']);data=original.read_bytes();assert sha(data)==x['sha256'],original
 name=original.stem;t=data.decode();code=p.lean_parts(t)[0];assert not re.search(r'\b(sorry|admit|native_decide|unsafeCast|axiom)\b',code)
 rel=x['module'].replace('.','/')+'.lean';assert not (root/rel).exists();(b/'original-sources'/original.name).write_bytes(data)
 if name=='ApproximateCircuitError':
  start=t.index('/-- The elementary');end=t.index('/-- Every original circuit');t=t[:start]+t[end:]
 ns=names(t);label='thm:compression' if name.startswith('Approximate') or name=='GateCoefficientBounds' else 'eq:compression-effect-circuit-error'
 t=add_notice(t,ns,rel,label);(root/rel).write_text(t)
 preserved=p.lean_parts(t)[0].split()==code.split()
 if name=='ApproximateCircuitError':
  expected=data.decode();expected=expected[:expected.index('/-- The elementary')]+expected[expected.index('/-- Every original circuit'):];assert p.lean_parts(t)[0].split()==p.lean_parts(expected)[0].split()
 else:assert preserved
 pres.append({'original_module':name,'original_path':str(original),'original_sha256':sha(data),'proof_tokens_preserved':preserved,'transformation':'remove duplicate of the identical helper promoted in EffectCircuitError' if not preserved else 'provenance notice only','production':[{'path':rel,'sha256':sha(t.encode())}]})
oldnew=old.replace('private theorem norm_comp_sub_comp_le_one','/-- The two-factor telescoping inequality for contractions.\nSource: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 590–600. -/\ntheorem norm_comp_sub_comp_le_one',1)
oldnew=add_notice(oldnew,[helper],oldrel,'thm:compression');assert p.lean_parts(oldnew)[0].split()==p.lean_parts(old.replace('private theorem norm_comp_sub_comp_le_one','theorem norm_comp_sub_comp_le_one',1))[0].split();(root/oldrel).write_text(oldnew)
pres.append({'original_module':'EffectCircuitError','original_path':str(b/'original-sources'/'EffectCircuitError.lean'),'original_sha256':sha(old.encode()),'proof_tokens_preserved':False,'transformation':'promote existing private theorem in place; no signature or proof change','production':[{'path':oldrel,'sha256':sha(oldnew.encode())}]})
assert len(rows)==75,len(rows)
previous=json.loads((root/'docs/provenance/openai-math.d/8769-source-resource-integration.json').read_text())['entries'];refresh=[{'id':r['id'],'path':r['downstream']['path'],'declaration':r['downstream']['declaration'],'shard':'8769-source-resource-integration.json'} for r in previous if r['downstream']['path']==oldrel];assert len(refresh)==11
save(b/'declarations.json',rows);save(b/'source-preservation.json',pres);save(b/'handoff.json',{'source_parent':base,'relay_source':relay,'relay_evidence':'ce14f5d903d8e83f9c5bba3fe0ef32f0113b4994','sources':sources});save(b/'inherited-provenance-refresh.json',refresh)
oldart=Path('/private/tmp/tnlean-actual-source-sampling/artifacts');art=b/'artifacts';art.mkdir(exist_ok=True);libc=ctypes.CDLL('/usr/lib/libSystem.B.dylib',use_errno=True);clones=[];links=0
for package in ['TNLean','QICLean']:
 for f in [*(oldart/package).rglob('*'),*oldart.glob(package+'.*')]:
  if not f.is_file():continue
  target=art/f.relative_to(oldart);target.parent.mkdir(parents=True,exist_ok=True);assert not target.exists() and not target.is_symlink()
  if f.is_symlink():target.symlink_to(f.resolve())
  else:
   frozen=b/'dependencies'/f.relative_to(oldart);frozen.parent.mkdir(parents=True,exist_ok=True);assert libc.clonefile(os.fsencode(f),os.fsencode(frozen),0)==0;frozen.chmod(0o444);assert sha(f.read_bytes())==sha(frozen.read_bytes());clones.append({'original':str(f),'frozen':str(frozen),'sha256':sha(frozen.read_bytes())});target.symlink_to(frozen)
  links+=1
cfg=json.loads(Path('/private/tmp/tnlean-actual-source-sampling/env.json').read_text());cfg.update(source_root=str(root),output_root=str(art),LEAN_PATH=str(Path(cfg['lean']).parent.parent/'lib/lean')+':'+str(art)+':/private/tmp/tnlean-artifact-recovery-20261008/gaussian/artifacts');save(b/'env.json',cfg);save(b/'environment-preparation.json',{'source_parent':base,'parent_source_revision':'259f77aa9b246bb561684af69aa4c833aa3f1518','preserved_artifacts':clones,'readonly_links':links})
subprocess.run(['python3','scripts/generate_import_aggregators.py'],cwd=root,check=True)
imports={}
for f in [*(root/'TNLean').rglob('*.lean'),root/'TNLean.lean']:
 if '/Archive/' in str(f):continue
 imports[str(f.relative_to(root))[:-5].replace('/','.')]=re.findall(r'^import (\S+)',f.read_text(),re.M)
selected={x['module'] for x in sources}|{'TNLean.PEPS.Approximation.EffectCircuitError'};changed=sorted(selected)
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
save(b/'build-plan.json',{'selected_modules':ordered,'changed_modules':changed});print('ADOPTED',len(sources),'NEW MODULES',len(rows),'NEW PUBLIC; STRICT',len(ordered),'CLONES',len(clones),'LINKS',links)
