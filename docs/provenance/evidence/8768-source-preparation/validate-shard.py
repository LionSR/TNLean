#!/usr/bin/env python3
"""Validate new original-proof shards with the unmodified, pinned canonical checker.

The branch under review need not contain the provenance framework. Checker and
schema are read from immutable Git objects, without changing the branch. The
canonical checker validates the new rows and scans every notice in this branch.
Existing canonical rows are inspected only for identifier/declaration collisions;
their historical source and evidence records are not revalidated here.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import types

POLICY_REVISION = '18a6dd4d2683cea18b585ffe0467910f76eb23ff'
CHECKER = 'scripts/check_openai_provenance.py'
SCHEMA = 'docs/provenance/openai-math.schema.json'
HASHES = {
    CHECKER: '8183e29f5a339bba37e28e9473aa7a6a42791282ed6877071dfd4096eda7cb65',
    SCHEMA: 'a691d8e95b668c968365f2c7e33f614d49635aade8fdd4c2f27cd64f0cd6b459',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--shard', required=True, action='append',
                        help='Repository-relative path of a new shard; repeat if needed.')
    parser.add_argument('--upstream-root', type=Path,
                        help='Optional openai/math checkout containing the pinned Git objects.')
    args = parser.parse_args()
    root = args.root.resolve()

    def git(*argv):
        return subprocess.check_output(['git', '-C', str(root), *argv])

    def policy_bytes(path):
        return git('show', f'{POLICY_REVISION}:{path}')

    source = policy_bytes(CHECKER)
    schema_bytes = policy_bytes(SCHEMA)
    for path, data in [(CHECKER, source), (SCHEMA, schema_bytes)]:
        if hashlib.sha256(data).hexdigest() != HASHES[path]:
            raise RuntimeError(f'Pinned policy bytes differ: {path}')
    policy = types.ModuleType('pinned_openai_provenance')
    policy.__file__ = f'git:{POLICY_REVISION}:{CHECKER}'
    exec(compile(source, policy.__file__, 'exec'), policy.__dict__)
    ledgers = [policy.read_json(policy.safe_file(root, path)) for path in args.shard]
    schema = json.loads(schema_bytes)
    roots = {'LionSR/TNLean': root}
    if args.upstream_root:
        roots['openai/math'] = args.upstream_root.resolve()
    count = policy.validate(ledgers, schema, roots, scan=True)

    paths = ['docs/provenance/openai-math.json'] + [
        path for path in git('ls-tree', '-r', '--name-only', POLICY_REVISION,
                            'docs/provenance/openai-math.d').decode().splitlines()
        if path.endswith('.json')]
    canonical = [entry for path in paths
                 for entry in json.loads(policy_bytes(path))['entries']]
    old_ids = {entry['id'] for entry in canonical}
    old_keys = {(entry['downstream']['repository'].casefold(),
                 entry['downstream']['declaration']) for entry in canonical}
    for ledger in ledgers:
        for entry in ledger['entries']:
            policy.require(entry['id'] not in old_ids,
                           f'ID collides with canonical ledger: {entry["id"]}')
            key = (entry['downstream']['repository'].casefold(),
                   entry['downstream']['declaration'])
            policy.require(key not in old_keys,
                           f'Declaration collides with canonical ledger: {key}')

    print(f'PASS: {count} new entries; canonical checker completed all entry checks and the full branch notice scan.')
    print(f'PASS: new IDs and declarations are disjoint from {len(canonical)} canonical entries.')
    print(f'Policy revision: {POLICY_REVISION}')
    for path, digest in HASHES.items():
        print(f'Policy SHA-256: {path}: {digest}')
    if not args.upstream_root:
        print('Manuscript labels were not rechecked against upstream Git objects; use --upstream-root for that check.')
    print('Scope: shard validation; the canonical CLI license/source-audit checks and historical canonical evidence were not rerun.')


if __name__ == '__main__':
    main()
