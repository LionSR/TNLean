#!/usr/bin/env python3
"""Prepare isolated outputs over the preserved Gaussian and published QIC artifacts."""
from pathlib import Path
import ctypes
import hashlib
import json
import os

base = Path('/private/tmp/tnlean-source-physical')
root = Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-physical')
old = Path('/private/tmp/tnlean-artifact-recovery-20261008/gaussian/artifacts')
artifacts = base / 'artifacts'
artifacts.mkdir(exist_ok=True)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
links = 0
for package in ['TNLean', 'QICLean']:
    files = [*(old / package).rglob('*'), *old.glob(package + '.*')]
    for source in files:
        if not source.is_file():
            continue
        target = artifacts / source.relative_to(old)
        target.parent.mkdir(parents=True, exist_ok=True)
        assert not target.exists() and not target.is_symlink(), target
        target.symlink_to(source)
        links += 1

qic = Path('/private/tmp/qic-physical-trace-helpers')
builds = json.loads((qic / 'build-commands.json').read_text())
old_rows = json.loads(Path('/private/tmp/tnlean-source-gaussian/imported-audit/imported-dependencies.json').read_text())
new_rows = json.loads((qic / 'imported-dependencies.json').read_text())
before = {r['module']: r['sha256'] for r in old_rows}
changed = {r['module'] for r in builds}
conflicts = [r['module'] for r in new_rows if r['module'] in before
             and r['sha256'] != before[r['module']] and r['module'] not in changed]
assert not conflicts, conflicts
libc = ctypes.CDLL('/usr/lib/libSystem.B.dylib', use_errno=True)
records = []
for row in builds:
    source = Path(row['artifact'])
    assert sha(source) == row['artifact_sha256']
    relative = Path(row['module'].replace('.', '/') + '.olean')
    target = base / 'qic-dependencies' / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    assert not target.exists()
    assert libc.clonefile(os.fsencode(source), os.fsencode(target), 0) == 0
    target.chmod(0o444)
    assert sha(target) == row['artifact_sha256']
    link = artifacts / relative
    link.parent.mkdir(parents=True, exist_ok=True)
    if link.is_symlink():
        link.unlink()
    assert not link.exists()
    link.symlink_to(target)
    records.append({**row, 'preserved_artifact': str(target)})
env = json.loads(Path('/private/tmp/tnlean-artifact-recovery-20261008/gaussian/env.json').read_text())
toolchain = str(Path(env['lean']).parent.parent / 'lib/lean')
env.update({'LEAN_PATH': toolchain + ':' + str(artifacts) + ':' + str(old),
            'source_root': str(root), 'output_root': str(artifacts)})
env.pop('warning', None)
env.pop('audited_artifact_root', None)
(base / 'env.json').write_text(json.dumps(env, indent=2) + '\n')
(base / 'environment-preparation.json').write_text(json.dumps({
    'base_source_revision': 'f96e06dc01118fd3778b58f197ac3dcb14c37e48',
    'base_artifact_audit': '/private/tmp/tnlean-source-gaussian/imported-audit/imported-dependencies.json',
    'qic_revision': 'caac4b549c1b5c14fcedbee647567f51e27b296d',
    'qic_source_revision': '92b6eea77da987d4d12236c3dd3fc06510cd98ac',
    'readonly_links': links, 'unchanged_qic_dependency_hashes': True,
    'changed_qic_artifacts': records,
}, indent=2) + '\n')
print('ENVIRONMENT_READY', links, len(records), flush=True)
