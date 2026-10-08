from pathlib import Path
import hashlib,json,subprocess,sys
root=Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-gaussian');b=Path('/private/tmp/tnlean-source-gaussian');sys.dont_write_bytecode=True;sys.path.insert(0,str(root/'scripts'))
from lean_import_syntax import strip_lean_comments
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files={str(p.relative_to(root)).removesuffix('.lean').replace('/','.'):p for p in [root/'TNLean.lean',*(root/'TNLean').rglob('*.lean')] if 'Archive' not in p.parts}
changed=set(subprocess.check_output(['git','diff','--name-only','--','TNLean','TNLean.lean'],cwd=root,text=True).splitlines());changed.update(x['path'] for x in json.loads((b/'declarations.json').read_text()));changed.add('TNLean/QICLeanInterface.lean')
selected={p.removesuffix('.lean').replace('/','.') for p in changed if p.endswith('.lean')};deps={}
for m,p in files.items():
 text,err=strip_lean_comments(p.read_text());assert err is None;deps[m]={x for line in text.splitlines() if line.startswith('import ') for x in line.split()[1:]}
while True:
 extended=selected|{m for m,d in deps.items() if d&selected}
 if extended==selected:break
 selected=extended
todo={m:deps[m]&selected for m in selected};order=[]
while todo:
 ready=sorted(m for m,d in todo.items() if not d);assert ready;order.extend(ready)
 for m in ready:del todo[m]
 for d in todo.values():d.difference_update(ready)
(b/'build-plan.json').write_text(json.dumps({'base_revision':'329d192af8c46f7ff540610de918d5179d13d46e','changed_paths':sorted(changed),'selected_modules':order},indent=2)+'\n')
print('CLOSURE',len(order),flush=True)
rows=[]
for mod in order:
 record=b/'strict-checks'/(mod+'.json')
 if record.exists():
  r=json.loads(record.read_text())
  if r['returncode']==0 and r['source_sha256']==sha(files[mod]) and r['artifact_sha256']==sha(Path(r['artifact'])):
   rows.append(r);print('REUSE EXACT',mod,flush=True);continue
 p=subprocess.run(['python3','/tmp/check-source-gaussian-module.py',mod]);assert p.returncode==0,mod
 rows.append(json.loads(record.read_text()));(b/'build-commands.json').write_text(json.dumps(rows,indent=2)+'\n')
(b/'build-commands.json').write_text(json.dumps(rows,indent=2)+'\n');print('CLOSURE_PASS',len(rows))
