#!/usr/bin/env python3
"""Independently compare the merged mathematical sources with both parent trees."""
import datetime, hashlib, json, re, subprocess
from pathlib import Path

ROOT = Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-integration')
RECORDS = Path('/private/tmp/tnlean-source-main-integration')
BASELINE = '80bc49d17e833795fba00bfeaf1bd053649c4070'

def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args])

def tree(revision):
    result = {}
    for row in git('ls-tree', '-r', '-z', revision).split(b'\0'):
        if not row:
            continue
        metadata, path = row.split(b'\t', 1)
        result[path.decode()] = metadata.split()[2].decode()
    return result

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(test, message):
    if not test:
        raise RuntimeError(message)

revision = git('rev-parse', 'HEAD').decode().strip()
manifest = json.loads((RECORDS / 'merge-preservation.json').read_text())
plan = json.loads((RECORDS / 'verification-plan.json').read_text())
predecessors = json.loads((RECORDS / 'strict-checks/unchanged-predecessors.json').read_text())
current = tree(revision)
trees = {parent: tree(parent) for parent in manifest['parents']}
base = tree(BASELINE)
rows = []
for row in manifest['changed_proof_files']:
    parent, path = row['parent'], row['path']
    require(current[path] == trees[parent][path], f'Parent blob differs: {path}')
    require(digest(ROOT / path) == row['sha256'], f'Recorded source SHA256 differs: {path}')
    rows.append({**row, 'git_blob': current[path], 'parent_and_integrated_blobs_equal': True})
require(len(rows) == 142, 'Unexpected changed-proof count')
require(len({r['path'] for r in rows}) == 142, 'Duplicate changed-proof path')
unaffected = []
for row in predecessors:
    path = row['module'].replace('.', '/') + '.lean'
    require(current[path] == base[path], f'Baseline source blob differs: {path}')
    require(digest(ROOT / path) == row['source_sha256'], f'Unchanged source SHA256 differs: {path}')
    require(Path(row['artifact']).is_file(), f'Missing recorded predecessor: {path}')
    unaffected.append({'module': row['module'], 'path': path,
                       'source_sha256': row['source_sha256'], 'git_blob': current[path]})
selected = set(plan['selected_tn'])
unchanged = {r['module'] for r in unaffected}
production = {p.removesuffix('.lean').replace('/', '.') for p in current
              if (p == 'TNLean.lean' or p.startswith('TNLean/'))
              and p.endswith('.lean') and 'Archive' not in Path(p).parts}
require(len(unaffected) == len(unchanged) == 2927, 'Unexpected unaffected count')
require(not selected & unchanged and selected | unchanged == production,
        'Selected and unaffected modules do not partition production source')
# Recompute the transitive affected closure from the recorded change sets.
import sys
sys.path.insert(0, str(ROOT / 'scripts'))
from lean_import_syntax import strip_lean_comments
imports = {}
for module in production:
    source, error = strip_lean_comments((ROOT / (module.replace('.', '/') + '.lean')).read_text())
    require(error is None, f'Comment parsing failed: {module}')
    imports[module] = {name for line in source.splitlines() if line.startswith('import ')
                       for name in line.split()[1:]}
affected = set(plan['affected_qic']) | set(plan['changed_tn'])
while True:
    expanded = affected | {m for m, dependencies in imports.items() if dependencies & affected}
    if expanded == affected:
        break
    affected = expanded
require(production & affected == selected, 'Affected TNLean closure differs from the plan')
summary = {
    'reviewed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'source_revision': revision,
    'comparison_baseline': BASELINE,
    'parents': {p: git('rev-parse', p + '^{commit}').decode().strip() for p in manifest['parents']},
    'merge_base': manifest['merge_base'],
    'preserved_changed_proof_files': len(rows),
    'unaffected_modules': len(unaffected),
    'strictly_selected_modules': len(selected),
    'production_modules_excluding_archive': len(production),
    'parent_source_blobs_and_recorded_sha256_match': True,
    'unaffected_source_blobs_and_recorded_sha256_match': True,
    'selected_unaffected_partition_complete': True,
    'recorded_change_set_affected_closure_recomputed': True,
    'scope': 'Independent Git-blob and source SHA256 comparison. Existing artifact paths were checked for existence, not rehashed here; their original hashes remain in unchanged-predecessors.json and the final imported audit.',
    'changed_proof_files': rows,
    'unaffected_sources': unaffected,
    'review_script_sha256': digest(Path(__file__)),
}
(RECORDS / 'independent-preservation-review.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k:v for k,v in summary.items() if k not in {'changed_proof_files','unaffected_sources'}}, indent=2))
