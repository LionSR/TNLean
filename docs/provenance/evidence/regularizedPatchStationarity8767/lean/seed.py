from pathlib import Path
import json,hashlib,re,shutil,sys
B=Path('/workspace/scratch/7637e06d0fc2');D=B/'patch-coordinate-validation';T=B/'TNLean-patch-coordinate-stationarity';Q=D/'qic-source'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
for f in B.glob('*/actual-runs.json'):
 for r in json.loads(f.read_text()):
  if r.get('exit_code')==0 and r.get('artifact_sha256') and r.get('command') and '-o' in r['command']:
   art=Path(r['command'][r['command'].index('-o')+1])
   if art.exists(): records.append((r,f,art))
seen={};missing=[];audit=[]
def visit(m):
 if m in seen:return
 source=(Q if m.startswith('QICLean.') else T)/Path(m.replace('.','/')).with_suffix('.lean'); seen[m]=True
 for mod in re.findall(r'^(?:public )?import ((?:QICLean|TNLean)\.[^\s]+)',source.read_text(),re.M):visit(mod)
 h=sha(source); p=D/'lib'/Path(m.replace('.','/')).with_suffix('.olean')
 for r,f,a in reversed(records):
  if r['module']==m and r['source_sha256']==h and sha(a)==r['artifact_sha256']:
   p.parent.mkdir(parents=True,exist_ok=True)
   for ext in ['.olean','.ilean']:
    if a.with_suffix(ext).exists():shutil.copy2(a.with_suffix(ext),p.with_suffix(ext))
   audit.append({'module':m,'source':str(source),'source_sha256':h,'artifact_sha256':sha(p),'record':str(f),'original_artifact':str(a),'original_command':r['command']});return
 missing.append(m)
for m in sys.argv[1:]:visit(m)
(D/'seed-audit.json').write_text(json.dumps(audit,indent=2)+'\n');(D/'missing-dependencies.json').write_text(json.dumps(missing,indent=2)+'\n');print('Seeded',len(audit),'missing',missing)
