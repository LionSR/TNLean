#!/usr/bin/env python3
"""Materialize unchanged audited sources outside TNLean for original-pin builds.

This is a disposable baseline, not a downstream proof port. No network or build
is performed. The Mathlib lockfile must come from its exact upstream revision;
its own dependency rows are checked against the pinned OAI manifest.
"""
import argparse
import json
from pathlib import Path
from audit_openai_closure import PIN, audit, blob, digest


def prepare(upstream, downstream, destination, mathlib_manifest):
    repo = downstream.resolve()
    target = destination.resolve()
    if target == repo or repo in target.parents:
        raise ValueError('baseline must be outside the production repository')
    if target.exists(): raise ValueError('destination already exists')
    manifest = audit(upstream, downstream)
    locked = manifest['source_configuration']['lake-manifest.json']['packages']
    mathlib = next(p for p in locked if p['name'] == 'mathlib')
    if digest(mathlib_manifest.read_bytes()) != '8f67b2cf24143ac091cdb425e886c2164b2fc2d6fbccd6db9454b697f9541a67':
        raise ValueError('not the pinned Mathlib lake-manifest.json bytes')
    dependencies = json.loads(mathlib_manifest.read_text())['packages']
    by_name = {p['name']: p for p in locked}
    for dep in dependencies:
        if dep['name'] not in by_name or dep['rev'] != by_name[dep['name']]['rev']:
            raise ValueError(f'Mathlib dependency differs from OAI lock: {dep["name"]}')
    target.mkdir(parents=True)
    for row in manifest['modules']:
        data = blob(upstream, PIN, row['path'])
        assert digest(data) == row['sha256']
        path = target / row['path'].removeprefix('lean/')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    (target / 'LICENSE').write_bytes(blob(upstream, PIN, 'lean/LICENSE'))
    (target / 'lean-toolchain').write_bytes(blob(upstream, PIN, 'lean/lean-toolchain'))
    (target / 'lakefile.toml').write_text(
        'name = "OAISelectedBaseline"\nversion = "0.1.0"\n'
        '[leanOptions]\nautoImplicit = false\nweak.linter.mathlibStandardSet = true\n'
        '[[require]]\nname = "mathlib"\ngit = "' + mathlib['url'] + '"\n'
        'rev = "' + mathlib['rev'] + '"\n[[lean_lib]]\nname = "OAI"\n')
    (target / 'lake-manifest.json').write_text(json.dumps({
        'version': '1.2.0', 'packagesDir': '.lake/packages',
        'packages': [mathlib] + [by_name[p['name']] for p in dependencies]}, indent=2)+'\n')
    (target / 'AuditAxioms.lean').write_text(
        '\n'.join('import ' + r['module'] for r in manifest['roots']) + '\n\n' +
        '\n'.join('#print axioms ' + r['declaration'] for r in manifest['roots']) + '\n')
    (target / 'baseline-source-manifest.json').write_text(json.dumps({
        'source_commit': PIN, 'adaptations': ['Lake configuration reduced to Mathlib closure',
        'Mathlib standard linter option added; source autoImplicit=false retained'],
        'files': {str(p.relative_to(target)): digest(p.read_bytes())
                  for p in sorted(target.rglob('*')) if p.is_file()}}, indent=2)+'\n')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--upstream', type=Path, required=True)
    p.add_argument('--downstream', type=Path, default=Path(__file__).resolve().parents[1])
    p.add_argument('--destination', type=Path, required=True)
    p.add_argument('--mathlib-manifest', type=Path, required=True)
    a = p.parse_args()
    prepare(a.upstream, a.downstream, a.destination, a.mathlib_manifest)


if __name__ == '__main__': main()
