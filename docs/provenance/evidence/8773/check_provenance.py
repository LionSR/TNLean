"""Validate issue 8773 against pinned policy; does not run Lean or fetch remotes."""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, types

parser = argparse.ArgumentParser()
parser.add_argument('--root', type=Path, required=True)
args = parser.parse_args()
root = args.root.resolve()
policy = 'a05ef8f8db19f28e987bf3ce599c5f284f96921f'
def blob(path):
    return subprocess.check_output(['git', 'show', policy + ':' + path], cwd=root)
source = blob('scripts/check_openai_provenance.py')
schema = blob('docs/provenance/openai-math.schema.json')
checker = types.ModuleType('pinned_openai_provenance')
checker.__file__ = '<pinned provenance validator>'
exec(compile(source, checker.__file__, 'exec'), checker.__dict__)
ledger = json.loads((root/'docs/provenance/openai-math.d/8773.json').read_text())
manifest = json.loads((root/'docs/provenance/evidence/8773/validation.json').read_text())
assert {row['verification']['revision'] for row in ledger['entries']} == {manifest['verified_source_revision']}
assert checker.validate([ledger], json.loads(schema), {'LionSR/TNLean': root}, scan=True) == 40
sys.path.insert(0, str(root/'scripts'))
from blueprint_lean_sync import collect_file_lean_decls
fields = []
for path in {row['downstream']['path'] for row in ledger['entries']}:
    declarations = collect_file_lean_decls(root/path, root/'TNLean')
    assert not any(d.is_private for d in declarations)
    ordinary = {d.fqn for d in declarations if d.kind != 'field'}
    recorded = {row['downstream']['declaration'] for row in ledger['entries'] if row['downstream']['path'] == path}
    assert ordinary == recorded
    fields.extend(d.fqn for d in declarations if d.kind == 'field')
assert set(fields) == {'TNLean.PEPS.ExactTreeRepresentation.Ports.edge', 'TNLean.PEPS.ExactTreeRepresentation.Ports.active'}
print(json.dumps({'status': 'passed', 'verified_source_revision': manifest['verified_source_revision'], 'source_publication': manifest['source_publication'], 'ordinary_named_declarations': 40, 'generated_structure_projections': sorted(fields), 'private_helpers': 0, 'policy_revision': policy, 'policy_sha256': hashlib.sha256(source).hexdigest(), 'schema_sha256': hashlib.sha256(schema).hexdigest(), 'checks': ['schema', 'exact source bytes', 'declaration and notice identity', 'log hashes', 'exact named raw axiom reports', 'all ordinary authored declarations mapped'], 'limits': ['No upstream publication or full CI inferred from local validation.', 'No Lean command executed by this validator.', 'Generated structure projections are not invented as separately authored declarations.']}, indent=2))
