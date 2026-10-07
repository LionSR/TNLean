"""Metadata-only validation; never execute recorded compiler commands."""
from pathlib import Path
import importlib.util,json,hashlib,subprocess
B=Path('/workspace/scratch/7637e06d0fc2');R=B/'TNLean-patch-coordinate-stationarity';D=B/'patch-coordinate-validation'
PUB='ac1fdd4c8a17b9811d15b8f2e9f05798a427c6fd';LEDGER='docs/provenance/openai-math.d/regularizedPatchStationarity8767.json'
def git(*a):return subprocess.check_output(['git','-C',str(R),*a])
ledger=json.loads((R/LEDGER).read_text())
for name,path,schema in [('f920',B/'regularized-patch-validation/docs/tn/f920_check_openai_provenance.py',B/'regularized-patch-validation/docs/tn/f920.schema.json'),('minimal',B/'TNLean-provenance-minimal/scripts/check_openai_provenance.py',B/'TNLean-provenance-minimal/docs/provenance/openai-math.schema.json')]:
 s=importlib.util.spec_from_file_location('p_'+name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
 assert len(ledger['entries'])==18
 assert all(e['status']=='ported' and e['downstream']['name_status']=='declared' and e['verification']['result']=='passed' and e['verification']['revision']==PUB for e in ledger['entries'])
 count=m.validate([ledger],json.loads(schema.read_text()),{'LionSR/TNLean':R,'openai/math':B/'openai-math-selected-objects.git'},scan=False)
 print(f'PASS {name}: {count} active original-proof rows, immutable source, exact notices, raw reports and stock axioms.')
paths=git('ls-tree','-r','--name-only',PUB,'docs/provenance/openai-math.d').decode().splitlines()
for p in paths:
 if p!=LEDGER:assert (R/p).read_bytes()==git('show',PUB+':'+p)
print('PASS: all other provenance shards unchanged.')
paths=git('ls-tree','-r','--name-only',PUB,'docs/provenance/evidence/regularizedPatchStationarity8767').decode().splitlines()
for p in paths:assert (R/p).read_bytes()==git('show',PUB+':'+p)
print(f'PASS: all {len(paths)} existing evidence files, including every raw log, unchanged.')
freeze=json.loads((D/'source-freeze.json').read_text())
for p,h in freeze.items():
 assert hashlib.sha256((R/p).read_bytes()).hexdigest()==h
 assert (R/p).read_bytes()==git('show',PUB+':'+p)
print('PASS: all seven frozen production/router/regression sources match published source; no recompilation.')
old=json.loads(git('show',PUB+':'+LEDGER))
for before,after in zip(old['entries'],ledger['entries'],strict=True):
 assert before['id']==after['id']
 clean=json.loads(json.dumps(after));clean['status']=before['status'];clean['downstream']['name_status']=before['downstream']['name_status'];clean['verification']=before['verification']
 assert clean==before
print('PASS: exactly18 existing rows activated; only status, name_status and verification changed.')
