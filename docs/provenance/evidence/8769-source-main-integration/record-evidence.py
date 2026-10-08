#!/usr/bin/env python3
"""Package existing integration checks without running Lean or changing source files."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

SLUG = '8769-source-main-integration'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text())

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--records', type=Path, default=Path('/private/tmp/tnlean-source-main-integration'))
    parser.add_argument('--source-revision', required=True)
    parser.add_argument('--qic-revision', required=True)
    parser.add_argument('--qic-root', type=Path, required=True)
    args = parser.parse_args()
    root, records = args.root.resolve(), args.records.resolve()
    blueprint = Path((records / 'blueprint-dir').read_text().strip())
    out = root / 'docs/provenance/evidence' / SLUG
    builds = read(records / 'strict-checks/build-commands.json')
    review = read(records / 'independent-preservation-review.json')
    refresh = read(records / 'final-refresh/commands.json')
    audit = read(records / 'imported-audit/audit-command.json')
    axioms = read(records / 'imported-audit/axiom-dependencies.json')
    require(review['source_revision'] == args.source_revision, 'Preservation review is not pinned')
    require(len(builds['builds']) == 66, 'Expected 66 original direct checks')
    for row in builds['builds']:
        require(row['returncode'] == 0, 'A direct check failed')
        require(sha(root / row['source_path']) == row['source_sha256'], 'Compiled source changed')
        log = records / 'strict-checks' / (row['module'] + '.log')
        require(sha(log) == row['log_sha256'] and not log.read_bytes(), 'Strict-check diagnostics differ')
    require({r['module'] for r in refresh} == {'TNLean', 'TNLean.QICLeanInterface'}, 'Unexpected final refresh')
    for row in refresh:
        require(row['returncode'] == 0, 'Final refresh failed')
        log = records / 'final-refresh' / (row['module'] + '.log')
        require(sha(log) == row['log_sha256'] and not log.read_bytes(), 'Final-refresh diagnostics differ')
    require(audit['returncode'] == 0 and audit['audited_declarations'] == len(axioms) == 342,
            'Final 342-declaration audit is incomplete')
    require(all(set(x) <= {'propext', 'Classical.choice', 'Quot.sound'} for x in axioms.values()),
            'Unexpected axiom dependency')
    require(sha(records / 'imported-audit/axioms.log') == audit['log_sha256'], 'Audit log changed')
    require(sha(records / 'imported-audit/imported-dependencies.json') == audit['imported_dependencies_sha256'],
            'Imported artifact manifest changed')
    pin = read(blueprint / 'final-source-pin-check.json')
    require(pin['tn_proof_revision'] == args.source_revision and pin['qic_source_revision'] == args.qic_revision,
            'Blueprint final source pin differs')
    require(read(blueprint / 'sync.json')['sync_ok'], 'Blueprint source sync failed')
    require(set(read(blueprint / 'tag-coverage.json').values()) == {1}, 'Declaration tags differ')
    require(read(blueprint / 'browser-command.json')['returncode'] == 0, 'Browser check failed')
    require(read(records / 'full-provenance-command.json')['returncode'] == 0, 'Full provenance check failed')
    out.mkdir(parents=True, exist_ok=True)
    compressed = {}
    def copy(source, relative, compress=False):
        destination = out / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        data = source.read_bytes()
        destination.write_bytes(gzip.compress(data, mtime=0) if compress else data)
        if compress:
            compressed[relative] = {'uncompressed_sha256': hashlib.sha256(data).hexdigest(),
                                    'uncompressed_bytes': len(data)}
    def bundle(source, relative=None):
        relative = relative or source.name
        copy(source, relative + '.gz' if source.suffix == '.log' else relative,
             compress=source.suffix == '.log')
    for name in ['verification-plan.json', 'merge-preservation.json', 'final-refresh-plan.json',
                 'full-provenance-command.json', 'full-provenance.log', 'canonical-replay-command.json',
                 'canonical-replay.log', 'blueprint-driver.log', 'env.json']:
        bundle(records / name)
    copy(records / 'independent-preservation-review.json', 'independent-preservation-review.json.gz', True)
    copy(Path('/private/tmp/review-peps-source-integration-preservation.py'), 'review-preservation.py')
    copy(records / 'strict-checks/build-commands.json', 'strict-checks/build-commands.json')
    copy(records / 'strict-checks/unchanged-predecessors.json', 'strict-checks/unchanged-predecessors.json.gz', True)
    for log in sorted((records / 'strict-checks').glob('*.log')):
        bundle(log, 'strict-checks/' + log.name)
    for file in sorted((records / 'final-refresh').iterdir()):
        if file.is_file():
            bundle(file, 'final-refresh/' + file.name)
    for file in sorted((records / 'imported-audit').iterdir()):
        if file.is_file():
            if file.name in ['imported-dependencies.json', 'imported-modules.json', 'Axioms.lean']:
                copy(file, 'imported-audit/' + file.name + '.gz', True)
            else:
                bundle(file, 'imported-audit/' + file.name)
    declaration = read(records / 'declaration-check/command.json')
    require(declaration['returncode'] == 0, 'Full declaration-presence check failed')
    for file in sorted((records / 'declaration-check').iterdir()):
        if file.is_file():
            if file.name == 'lean_declarations.txt':
                copy(file, 'declaration-check/' + file.name + '.gz', True)
            else:
                bundle(file, 'declaration-check/' + file.name)
    for name in ['plan-peps-source-main-integration.py', 'check-peps-source-main-integration.py',
                 'refresh-peps-source-main-integration.py', 'audit-peps-source-main-integration.py',
                 'check-peps-source-main-declarations.py']:
        copy(Path('/private/tmp') / name, 'verification-scripts/' + name)
    # These are source/rendering records, not another claimed rendering run.
    bp_plain = ['source-revision.json', 'source-revision.initial.json', 'final-source-pin-check.json',
                'commands.json', 'browser-command.json', 'browser.initial-command.json',
                'web-focused-command.json', 'focused-configuration.json', 'input-routing.json',
                'tag-coverage.json', 'scoped_web_check.py']
    bp_gzip = ['TNLean-source-sha256.json', 'QICLean-source-sha256.json', 'blueprint-source-sha256.json',
               'dependency-graph.json', 'sync.json', 'full-lean-decls.txt']
    for name in bp_plain:
        copy(blueprint / name, 'blueprint/' + name)
    for name in bp_gzip:
        copy(blueprint / name, 'blueprint/' + name + '.gz', True)
    for log in sorted(blueprint.glob('*.log')):
        bundle(log, 'blueprint/' + log.name)
    copy(blueprint / 'blueprint/src/focused.log', 'blueprint/final-tex.log.gz', True)
    copy(blueprint / 'blueprint/src/focused.pdf', 'blueprint/focused.pdf')
    for file in sorted(blueprint.glob('pdf-final-*.png')):
        copy(file, 'blueprint/' + file.name)
    for name in ['focused.tex', 'content-focused.tex', 'web.tex']:
        copy(blueprint / 'blueprint/src' / name, 'blueprint/render-inputs/' + name)
    for name in ['texra-blueprint.toml', 'texra-blueprint.full.toml']:
        copy(blueprint / name, 'blueprint/render-inputs/' + name)
    for name in ['setup-peps-source-main-blueprint.py', 'verify-peps-source-main-blueprint.py']:
        copy(Path('/private/tmp') / name, 'blueprint/' + name)
    # The dependency evidence is cited at its immutable published revision.
    qic_dir = 'docs/provenance/evidence/pepsSourceLatestMainIntegration'
    qic_reference = {'revision': args.qic_revision, 'mathematical_source_revision': '035e5cc6f208e7b069132ef8eff8c8afbfa012d9',
                     'url': f'https://github.com/LionSR/QICLean/tree/{args.qic_revision}/{qic_dir}', 'files': {}}
    for name in ['README.md', 'manifest.json', 'verification.json']:
        data = subprocess.check_output(['git', '-C', str(args.qic_root), 'show',
                                        args.qic_revision + ':' + qic_dir + '/' + name])
        qic_reference['files'][name] = hashlib.sha256(data).hexdigest()
        if name == 'verification.json':
            (out / 'qic-verification.json').write_bytes(data)
    (out / 'qic-evidence-reference.json').write_text(json.dumps(qic_reference, indent=2) + '\n')
    copy(Path(__file__), 'record-evidence.py')
    copy(Path('/private/tmp/validate-peps-source-integration-evidence.py'), 'validate-evidence.py')
    (out / 'compression.json').write_text(json.dumps(compressed, indent=2) + '\n')
    (out / 'source-revision.json').write_text(json.dumps({'tn_source_revision': args.source_revision,
        'qic_revision': args.qic_revision, 'initial_direct_check_tn_revision': builds['tn_source_revision'],
        'initial_direct_check_qic_revision': builds['qic_source_revision']}, indent=2) + '\n')
    # README is authored for this integration before this recorder runs.
    require((out / 'README.md').is_file(), 'Integration README is missing')
    manifest = {str(p.relative_to(out)): sha(p) for p in sorted(out.rglob('*'))
                if p.is_file() and p.name != 'manifest.json'}
    (out / 'manifest.json').write_text(json.dumps({'sha256': manifest}, indent=2) + '\n')
    print(f'Recorded {len(manifest)} evidence files in {out}')

if __name__ == '__main__':
    main()
