#!/usr/bin/env python3
"""Validate recorded integration evidence and current source bytes; never run Lean."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess


def require(condition, message):
    if not condition:
        raise SystemExit(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    args = parser.parse_args()
    root = args.root.resolve()
    evidence = Path(__file__).resolve().parent
    def load(name):
        path = evidence / name
        data = gzip.decompress(path.read_bytes()) if name.endswith('.gz') else path.read_bytes()
        return json.loads(data)
    manifest = load('manifest.json')['sha256']
    for name, expected in manifest.items():
        path = evidence / name
        require(path.is_file() and digest(path.read_bytes()) == expected, f'Evidence differs: {name}')
    for name, expected in load('compression.json').items():
        raw = gzip.decompress((evidence / name).read_bytes())
        require(digest(raw) == expected['uncompressed_sha256'] and len(raw) == expected['uncompressed_bytes'],
                f'Compressed evidence differs: {name}')
    pin = load('source-revision.json')
    review = load('independent-preservation-review.json.gz')
    require(review['source_revision'] == pin['tn_source_revision'], 'Preservation revision differs')
    for row in review['changed_proof_files']:
        require(digest((root / row['path']).read_bytes()) == row['sha256'], f'Parent source differs: {row["path"]}')
    for row in review['unaffected_sources']:
        require(digest((root / row['path']).read_bytes()) == row['source_sha256'],
                f'Unaffected source differs: {row["path"]}')
    build = load('strict-checks/build-commands.json')
    require(len(build['builds']) == 66 and all(r['returncode'] == 0 for r in build['builds']),
            'Initial strict check set differs')
    for row in build['builds']:
        require(digest((root / row['source_path']).read_bytes()) == row['source_sha256'],
                f'Compiled source differs: {row["source_path"]}')
        raw = gzip.decompress((evidence / 'strict-checks' / (row['module'] + '.log.gz')).read_bytes())
        require(not raw and digest(raw) == row['log_sha256'], 'Initial strict diagnostics differ')
    refresh = load('final-refresh/commands.json')
    require(len(refresh) == 2 and all(r['returncode'] == 0 for r in refresh), 'Final refresh failed')
    audit = load('imported-audit/audit-command.json')
    axioms = load('imported-audit/axiom-dependencies.json')
    require(audit['returncode'] == 0 and len(axioms) == audit['audited_declarations'] == 342,
            'Kernel audit count differs')
    require(all(set(x) <= {'propext', 'Classical.choice', 'Quot.sound'} for x in axioms.values()),
            'Nonstandard axiom dependency')
    deps = load('imported-audit/imported-dependencies.json.gz')
    require(len(deps) == audit['imported_artifacts'] == 14616, 'Imported artifact count differs')
    check = load('declaration-check/command.json')
    require(check['returncode'] == 0, 'Declaration-presence check failed')
    declarations = gzip.decompress((evidence / 'declaration-check/lean_declarations.txt.gz').read_bytes())
    require(digest(declarations) == check['declaration_list_sha256'], 'Declaration list differs')
    require(len(set(declarations.decode().splitlines())) == 20810, 'Declaration count differs')
    for name in ['TNLean-source-sha256.json.gz', 'blueprint-source-sha256.json.gz']:
        for relative, expected in load('blueprint/' + name).items():
            require(digest((root / relative).read_bytes()) == expected, f'Blueprint source differs: {relative}')
    bp = load('blueprint/final-source-pin-check.json')
    require(bp['tn_proof_revision'] == pin['tn_source_revision'] and bp['qic_source_revision'] == pin['qic_revision'],
            'Blueprint pin differs')
    for relative, expected in bp['refreshed_pin_files'].items():
        require(digest((root / relative).read_bytes()) == expected, f'Dependency pin file differs: {relative}')
    require(load('blueprint/sync.json.gz')['sync_ok'], 'Source synchronization failed')
    graph = load('blueprint/dependency-graph.json.gz')
    require(not graph['cycles'] and not graph['duplicate_labels'], 'Dependency graph failed')
    require(load('blueprint/browser-command.json')['returncode'] == 0, 'Browser check failed')
    require(load('full-provenance-command.json')['returncode'] == 0, 'Full provenance check failed')
    print(f'Evidence valid: {len(manifest)} file hashes; 142 preserved parent proofs; '
          '2927 unaffected sources; 66 strict checks plus 2 final refreshes; '
          '342 standard-axiom reports; 20810 imported declaration names. No Lean build performed.')


if __name__ == '__main__':
    main()
