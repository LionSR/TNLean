"""Run the pinned hardened validator on issue #8745 without installing policy files."""
from pathlib import Path
import argparse, hashlib, json, subprocess, types, sys

p=argparse.ArgumentParser()
p.add_argument('--root',type=Path,required=True)
a=p.parse_args();root=a.root.resolve()
revision='a05ef8f8db19f28e987bf3ce599c5f284f96921f'
def blob(path):return subprocess.check_output(['git','show',revision+':'+path],cwd=root)
source=blob('scripts/check_openai_provenance.py')
schema=blob('docs/provenance/openai-math.schema.json')
module=types.ModuleType('pinned_openai_provenance')
module.__file__='<pinned '+revision+':scripts/check_openai_provenance.py>'
exec(compile(source,module.__file__,'exec'),module.__dict__)
ledger=json.loads((root/'docs/provenance/openai-math.d/8745.json').read_text())
count=module.validate([ledger],json.loads(schema),{'LionSR/TNLean':root},scan=True)
assert count==50
assert {entry["verification"]["revision"] for entry in ledger["entries"]} == {"c369460bb80b17abb974108f843befeed40f48f5"}
assert len({e['downstream']['declaration'] for e in ledger['entries']})==50
sys.path.insert(0,str(root/'scripts'))
from blueprint_lean_sync import collect_file_lean_decls
private=[]
for path in {e['downstream']['path'] for e in ledger['entries']}:
    decls=collect_file_lean_decls(root/path,root/'TNLean')
    private.extend({'source_name':d.fqn,'kind':d.kind,'path':path,'line':d.line} for d in decls if d.is_private)
    actual={d.fqn for d in decls if not d.is_private}
    recorded={e['downstream']['declaration'] for e in ledger['entries'] if e['downstream']['path']==path}
    assert actual==recorded,(path,actual-recorded,recorded-actual)
assert len(private)==5
assert sum(d['path'].endswith('/GraphLatticeDiamond.lean') for d in private)==4
assert sum(d['path'].endswith('/GraphInteractionSeries.lean') for d in private)==1
print(json.dumps({'status':'passed','entries':count,'private_helpers':private,'private_helper_treatment':'The pinned exhaustive lexical-module rule applies to copied/adapted modules only. All rows here are original. Five private helpers remain private, are recorded separately and are compiled in the module; public axiom reports include their transitive dependencies.','scope':'Issue #8745 original graph/counting package; all 50 public ordinary declarations exactly covered.','validator_revision':revision,'validator_sha256':hashlib.sha256(source).hexdigest(),'schema_sha256':hashlib.sha256(schema).hexdigest(),'checks':['Draft 2020-12 schema','unique IDs and downstream names','exact source bytes at recorded revision','in-module notices','evidence log hashes','exact named standard-axiom output','all 50 public ordinary production declarations accounted for; five private helpers inventoried'],'limits':['No shared policy integration or full repository provenance command.','Pinned manuscript labels were checked separately through GitHub file reads; no upstream repository closure scan.','No Lean command executed by this validator. Full CI remains pending.']},indent=2))
