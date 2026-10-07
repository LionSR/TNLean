#!/usr/bin/env python3
"""Bind CI logs to source/toolchain pins and detect modified baseline bytes."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
from audit_openai_closure import PIN


def record(baseline, output):
    output.mkdir(parents=True, exist_ok=True)
    result = {'evidence_kind': 'original_pin_baseline_not_downstream_port',
              'source_commit': PIN, 'downstream_port_validation': 'not_performed',
              'workflow_revision': os.environ.get('GITHUB_SHA'),
              'run_id': os.environ.get('GITHUB_RUN_ID'),
              'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT'),
              'event': os.environ.get('GITHUB_EVENT_NAME'), 'modified_or_missing': [],
              'dependency_revisions': {}}
    source_manifest = baseline/'baseline-source-manifest.json'
    if not source_manifest.is_file():
        result['integrity'] = 'baseline_not_prepared'
    else:
        source = json.loads(source_manifest.read_text())
        for name, expected in source['files'].items():
            path = baseline/name
            if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
                result['modified_or_missing'].append(name)
        result['integrity'] = 'passed' if not result['modified_or_missing'] else 'failed'
        shutil.copy2(source_manifest, output/source_manifest.name)
        shutil.copy2(baseline/'LICENSE', output/'upstream-LICENSE')
        locked = json.loads((baseline/'lake-manifest.json').read_text())
        for package in locked['packages']:
            folder = baseline/'.lake/packages'/package['name']
            if not folder.exists(): continue
            actual = subprocess.check_output(['git', '-C', str(folder), 'rev-parse', 'HEAD']).decode().strip()
            result['dependency_revisions'][package['name']] = {'expected': package['rev'], 'actual': actual}
            if actual != package['rev']: result['integrity'] = 'failed'
    (output/'ci-provenance.json').write_text(json.dumps(result, indent=2)+'\n')
    if result['integrity'] != 'passed': raise SystemExit(1)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--baseline', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    record(a.baseline, a.output)
