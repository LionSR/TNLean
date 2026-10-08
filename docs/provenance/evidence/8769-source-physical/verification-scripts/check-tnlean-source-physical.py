#!/usr/bin/env python3
"""Strictly check the changed physical-source modules and their import dependents."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import time

base = Path('/private/tmp/tnlean-source-physical')
env_data = json.loads((base / 'env.json').read_text())
root = Path(env_data['source_root'])
artifacts = Path(env_data['output_root'])
plan = json.loads((base / 'build-plan.json').read_text())
env = os.environ.copy()
env['LEAN_PATH'] = env_data['LEAN_PATH']
records = []
record_path = base / 'build-commands.json'
if record_path.exists():
    records = json.loads(record_path.read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for module in plan['selected_modules']:
    relative = module.replace('.', '/') + '.lean'
    source = root / relative
    artifact = artifacts / (module.replace('.', '/') + '.olean')
    earlier = next((r for r in reversed(records) if r['module'] == module), None)
    if earlier and earlier['returncode'] == 0 and earlier['source_sha256'] == sha(source):
        assert sha(artifact) == earlier['artifact_sha256']
        continue
    if artifact.is_symlink():
        artifact.unlink()
    artifact.parent.mkdir(parents=True, exist_ok=True)
    snapshot = base / 'strict-checks/sources' / relative
    snapshot.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, snapshot)
    command = [env_data['lean'], *env_data['options'], '-DwarningAsError=true',
               '-o', str(artifact), relative]
    started = time.monotonic()
    result = subprocess.run(command, cwd=root, env=env, capture_output=True, text=True)
    log = base / 'strict-checks' / (module + '.log')
    log.write_text(result.stdout + result.stderr)
    row = {'module': module, 'source_path': relative, 'source_sha256': sha(source),
           'command': command, 'cwd': str(root), 'LEAN_PATH': env['LEAN_PATH'],
           'returncode': result.returncode, 'seconds': round(time.monotonic() - started, 3),
           'log': str(log), 'log_sha256': sha(log), 'artifact': str(artifact)}
    if result.returncode == 0:
        row['artifact_sha256'] = sha(artifact)
    records.append(row)
    record_path.write_text(json.dumps(records, indent=2) + '\n')
    print(module, result.returncode, row['seconds'], flush=True)
    if result.returncode:
        print(result.stdout + result.stderr, flush=True)
        raise SystemExit(result.returncode)
print('ALL_STRICT_CHECKS_PASSED', len(plan['selected_modules']), flush=True)
