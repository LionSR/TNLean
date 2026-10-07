"""Check published exact-PEPS source evidence without running Lean or fetching refs."""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys

parser = argparse.ArgumentParser()
parser.add_argument('--root', type=Path, required=True)
args = parser.parse_args()
root = args.root.resolve()
spec = importlib.util.spec_from_file_location(
    'openai_provenance', root / 'scripts/check_openai_provenance.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)
ledger = json.loads((root / 'docs/provenance/openai-math.d/8773.json').read_text())
evidence = root / 'docs/provenance/evidence/8773/published-verification'
identity = json.loads((evidence / 'identity.json').read_text())
checks = json.loads((evidence / 'checks.json').read_text())
assert {row['verification']['revision'] for row in ledger['entries']} == {
    identity['published_revision']}
tree = subprocess.check_output([
    'git', 'rev-parse', identity['published_revision'] + '^{tree}'], cwd=root).decode().strip()
assert tree == identity['published_tree'] == identity['locally_checked_tree']
assert checker.validate([ledger], checker.read_json(
    root / 'docs/provenance/openai-math.schema.json'),
    {'LionSR/TNLean': root}, scan=False) == 40
for check in checks:
    assert check['head'] == identity['locally_checked_revision']
    assert check['exit_code'] == 0
    assert hashlib.sha256((evidence / check['log']).read_bytes()).hexdigest() == check['log_sha256']
    if check['sha256'] is not None:
        assert hashlib.sha256((root / check['file']).read_bytes()).hexdigest() == check['sha256']
sys.path.insert(0, str(root / 'scripts'))
from blueprint_lean_sync import collect_file_lean_decls
fields = []
for path in {row['downstream']['path'] for row in ledger['entries']}:
    declarations = collect_file_lean_decls(root / path, root / 'TNLean')
    assert not any(d.is_private for d in declarations)
    ordinary = {d.fqn for d in declarations if d.kind != 'field'}
    recorded = {row['downstream']['declaration'] for row in ledger['entries']
                if row['downstream']['path'] == path}
    assert ordinary == recorded
    fields.extend(d.fqn for d in declarations if d.kind == 'field')
assert set(fields) == {'TNLean.PEPS.ExactTreeRepresentation.Ports.edge',
                       'TNLean.PEPS.ExactTreeRepresentation.Ports.active'}
print(json.dumps({
    'status': 'passed', 'published_revision': identity['published_revision'],
    'published_tree': tree, 'ordinary_ledger_declarations': 40,
    'source_and_log_rows': len(checks),
    'limits': ['No Lean command executed.',
               'Full-repository provenance is checked by scripts/check_openai_provenance.py.',
               'Historical evidence remains separate; dependency-sync CI is not inferred.']
}, indent=2))
