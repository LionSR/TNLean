import pathlib,subprocess,re,json,sys
r=pathlib.Path('/workspace/tn-interaction-integration');warm=pathlib.Path('/workspace/tn-pin729-other');q=warm/'.lake/packages/qiclean';sys.path.insert(0,str(r/'scripts'));from lean_import_syntax import strip_lean_comments
roots={'TNLean':r,'QICLean':q};caches={'TNLean':warm/'.lake/build/lib/lean','QICLean':q/'.lake/build/lib/lean'};memo={};order=[];deps={};need={}
def visit(m):
 if m in memo:return memo[m]
 if m.split('.')[0] not in roots:return set()
 p=roots[m.split('.')[0]]/(m.replace('.','/')+'.lean');t,e=strip_lean_comments(p.read_text());assert not e
 ds=[]
 for l in t.splitlines():
  z=re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$',l)
  if z:ds+=z.group(1).split()
 deps[m]=ds;cs={m};memo[m]=cs
 for d in ds:cs|=visit(d)
 missing=not (caches[m.split('.')[0]]/m.replace('.','/')).with_suffix('.olean').is_file()
 changed=False
 if m.startswith('TNLean.'):
  try:changed=p.read_bytes()!=subprocess.check_output(['git','show','6b7fb2e27dbc6856091e593e4226d350403beb8a:'+str(p.relative_to(r))],cwd=r,stderr=subprocess.DEVNULL)
  except subprocess.CalledProcessError:changed=True
 if m.startswith('QICLean.'):
  try:changed=p.read_bytes()!=subprocess.check_output(['git','show','1af32a2bf77670e4fc01a7727828bcbd49d35de3:'+str(p.relative_to(q))],cwd=q,stderr=subprocess.DEVNULL)
  except subprocess.CalledProcessError:changed=True
 if m.startswith('QICLean.') and changed:
  trace=(caches['QICLean']/m.replace('.','/')).with_suffix('.trace')
  if trace.exists() and str(q/(m.replace('.','/')+'.lean')) in trace.read_text():changed=False
 need[m]=missing or changed or any(need.get(d,False) for d in ds);order.append(m);return cs
out={}
for target in ['TNLean.Lattice.LocalHamiltonian','TNLean.MPS.AreaLaw.Hamiltonian','TNLean.PEPS.AreaLaw.RectangularHamiltonian','TNLean.Lattice.MarginalTails','TNLean.Lattice.ProductForm','TNLean.MPS.AreaLaw.ComponentReduction']:
 cs=visit(target);ns=[m for m in order if m in cs and need[m]];out[target]=ns;print(target,len(ns),ns[:12])
pathlib.Path('/workspace/reviews/interaction-shared-validation/preflight.json').write_text(json.dumps(out,indent=2)+'\n')
