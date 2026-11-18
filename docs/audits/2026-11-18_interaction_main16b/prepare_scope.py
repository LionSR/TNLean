import pathlib,subprocess,json,re,hashlib
r=pathlib.Path('/workspace/tn-interaction-main16b');o=pathlib.Path('/workspace/tn-peps-evidence/docs/audits/2026-11-18_interaction_main16b');parents=['42c4ed17b53f06bc274dd2c70b1eb3ae607bce5d','16b1dfbd7e45f0e8fed7f2607e25313cf5a9f931'];graph={}
for h in parents:
 text=subprocess.check_output(['git','grep','-n','-E','^(public )?import ',h,'--','*.lean'],cwd=r,text=True)
 for line in text.splitlines():
  _,path,ln,body=line.split(':',3);node=path[:-5].replace('/','.');deps=body.removeprefix('public ').removeprefix('import ').split('--')[0].split();graph.setdefault(node,set()).update(x for x in deps if re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',x))
seedpaths=[]
for lane in ['MPS','PEPS']:seedpaths+=(o/(lane+'-conflicts.txt')).read_text().splitlines()
seeds={p[:-5].replace('/','.') for p in seedpaths};affected=set(seeds)
while True:
 new={m for m,ds in graph.items() if ds&affected}-affected
 if not new:break
 affected|=new
paths=sorted(m.replace('.','/')+'.lean' for m in affected);parts={k:[] for k in ['MPS','PEPS','shared','fixtures']}
for p in paths:
 k='MPS' if p.startswith('TNLean/MPS/') else 'PEPS' if p.startswith('TNLean/PEPS/') else 'fixtures' if p.startswith('scripts/') else 'shared';parts[k].append(p)
for k,ps in parts.items():(o/(k+'-potential-affected.txt')).write_text('\n'.join(ps)+'\n' if ps else '')
(o/'union-imports.json').write_text(json.dumps({k:sorted(v) for k,v in sorted(graph.items())},indent=2)+'\n')
metadata=dict(parents=parents,seeds=len(seeds),potential_affected=len(paths),groups={k:len(v) for k,v in parts.items()},method='Reverse transitive closure of 50 conflicted Lean paths on union of both parent import graphs. Conservative planning only; recompute actual changed blobs and transitive fingerprints after resolutions. No builds authorized by this manifest alone.')
(o/'affected-plan.json').write_text(json.dumps(metadata,indent=2)+'\n');print(json.dumps(metadata))
