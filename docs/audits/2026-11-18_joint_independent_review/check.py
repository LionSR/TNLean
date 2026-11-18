import subprocess,json,hashlib,re,sys
from pathlib import Path
out=Path('/tmp/joint-independent-dccc85e5'); root=Path.cwd()
def git(*args):return subprocess.check_output(['git',*args],text=True).strip()
def blob(ref,p):return subprocess.check_output(['git','show',ref+':'+p])
def pid(ref):return subprocess.check_output(['git','patch-id','--stable'],input=subprocess.check_output(['git','show',ref])).decode().split()[0]
head=git('rev-parse','HEAD')
pairs=[('54ab66ae0','c0be5284e'),('42229ed94','7fb674c7a'),('550b63ccb','e052cb83f'),('81e70a7d4','b992c791d')]
pairresults=[dict(original=a,integrated=b,original_patch=pid(a),integrated_patch=pid(b),equal=pid(a)==pid(b)) for a,b in pairs]
anc={r:subprocess.run(['git','merge-base','--is-ancestor',r,head]).returncode==0 for r in ['7376dab08421ab99afcc5373be11104c76cc8a50','b992c791d','81e70a7d4','f8e80bac','e740d046']}
paths=git('ls-tree','-r','--name-only','550b63ccb','TNLean/MPS','TNLean/Lattice').splitlines()
hashes=[dict(path=p,old=hashlib.sha256(blob('550b63ccb',p)).hexdigest(),new=hashlib.sha256(blob(head,p)).hexdigest()) for p in paths]
assert all(r['old']==r['new'] for r in hashes)
(out/'reused-source-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
docs=git('diff-tree','--no-commit-id','--name-only','-r','f8e80bac').splitlines()
docdiff=[p for p in docs if blob('e740d046',p)!=blob(head,p)]
pins={r:next(p['rev'] for p in json.loads(blob(r,'lake-manifest.json'))['packages'] if p['name']=='qiclean') for r in ['550b63ccb',head]}
# Strip nested Lean block comments and line comments, retaining line numbers.
def uncomment(s):
 return re.sub(r'/\-.*?\-/|--[^\n]*',lambda m:'\n'*m[0].count('\n'),s,flags=re.S)
files=sorted([*root.joinpath('TNLean').rglob('*.lean'),*root.joinpath('scripts').glob('*.lean')])
legacy=[]; adapters=[]
for p in files:
 s=uncomment(p.read_text())
 for i,l in enumerate(s.splitlines(),1):
  if l.strip().startswith('import '):continue
  if re.search(r'\b(?:ChainHamiltonian|LocalHamiltonian|DomainHamiltonian|IsGappedGroundState)\b|ManyBody\.ManyBody|Interaction\.Interaction',l):legacy.append([str(p.relative_to(root)),i,l])
  if re.search(r'\b(?:def|abbrev|structure|class)\s+\S*(?:[Ii]nteraction|[Hh]amiltonian)\b',l):adapters.append([str(p.relative_to(root)),i,l])
(out/'interaction-declaration-candidates.json').write_text(json.dumps(adapters,indent=2)+'\n')
res=dict(head=head,production=git('rev-parse','3a41ae4b'),patch_pairs=pairresults,ancestry=anc,pins=pins,reused_mps_lattice_paths=len(paths),documentation_paths=len(docs),documentation_differences_from_e740=docdiff,lean_scan_files=len(files),legacy_nonimport_hits=legacy)
(out/'composition.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2));print('declaration candidates',len(adapters))
