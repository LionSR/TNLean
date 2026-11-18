from pathlib import Path
import subprocess,json,re,hashlib
r=Path('/workspace/tn-interaction-main16b');q=Path('/workspace/tn-pin729-other/.lake/packages/qiclean');warm=q.parent.parent.parent;o=Path(__file__).parent
def g(*a):return subprocess.check_output(['git',*a],cwd=r,text=True)
changed=g('diff','--name-only','42c4ed17','HEAD','--','*.lean').splitlines();graph=json.loads(Path('/workspace/tn-peps-evidence/docs/audits/2026-11-18_interaction_main16b/union-imports.json').read_text());affected={p[:-5].replace('/','.') for p in changed}
while True:
 new={m for m,ds in graph.items() if set(ds)&affected}-affected
 if not new:break
 affected|=new
(o/'actual-reverse-closure.txt').write_text('\n'.join(sorted(affected))+'\n')
imports={};sources={}
def visit(m):
 if m in imports:return
 p=(q if m.startswith('QICLean.') else r)/(m.replace('.','/')+'.lean')
 if not p.exists():imports[m]=[];return
 b=p.read_bytes();sources[m]=hashlib.sha256(b).hexdigest();ds=[]
 for l in b.decode().splitlines():
  match=re.match(r'^(?:public )?import (.*)',l)
  if match:ds.extend(x for x in match[1].split('--')[0].split() if re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',x))
 imports[m]=ds
 for d in ds:visit(d)
visit('TNLean.MPS.AreaLaw.Hastings.AreaLaw')
paths=[Path('/workspace/reviews/interaction-final-validation/olean'),Path('/workspace/reviews/interaction-shared-validation/olean'),warm/'.lake/build/lib/lean',q/'.lake/build/lib/lean',Path('/workspace/elan/toolchains/leanprover--lean4---v4.36.0-rc1/lib/lean')]+[p/'.lake/build/lib/lean' for p in q.parent.iterdir() if p.name!='qiclean']
missing=[m for m in imports if not any((p/(m.replace('.','/')+'.olean')).is_file() for p in paths)]
(o/'arealaw-preflight.json').write_text(json.dumps(dict(head=g('rev-parse','HEAD').strip(),changed=changed,reverse_closure_count=len(affected),project_sources=len(sources),missing_artifact_count=len(missing),missing_artifacts=sorted(missing),note='Existence preflight only; existing artifacts require source/dependency fingerprint validation before reuse. No compile launched.'),indent=2)+'\n');(o/'arealaw-imports.json').write_text(json.dumps(imports,indent=2)+'\n');print('reverse',len(affected),'missing',len(missing));print('\n'.join(sorted(affected)))
