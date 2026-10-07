#!/usr/bin/env python3
"""Validate proof shards using the packaged, unmodified canonical checker.

The policy commit is recorded for attribution, but need not exist in the local
Git repository. Only the proof revisions named in the shards must be available.
"""
import argparse
import hashlib
import json
from pathlib import Path
import types

POLICY_REVISION = '18a6dd4d2683cea18b585ffe0467910f76eb23ff'
HASHES = {
    'check_openai_provenance.py':
        '8183e29f5a339bba37e28e9473aa7a6a42791282ed6877071dfd4096eda7cb65',
    'openai-math.schema.json':
        'a691d8e95b668c968365f2c7e33f614d49635aade8fdd4c2f27cd64f0cd6b459',
    'canonical-collisions.json':
        '16dd515cf8c38fe77536322c52f2b38dc56b8143d21f1f7abc9b0545f2a4a73b',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--shard', required=True, action='append',
                        help='Repository-relative shard path; repeat for stacked contributions.')
    parser.add_argument('--upstream-root', type=Path,
                        help='Optional openai/math checkout containing the pinned manuscript.')
    args = parser.parse_args()
    root = args.root.resolve()
    bundle = Path(__file__).resolve().parent
    contents = {}
    for name, digest in HASHES.items():
        data = (bundle / name).read_bytes()
        if hashlib.sha256(data).hexdigest() != digest:
            raise RuntimeError(f'Pinned policy bytes differ: {name}')
        contents[name] = data

    policy = types.ModuleType('pinned_openai_provenance')
    policy.__file__ = str(bundle / 'check_openai_provenance.py')
    exec(compile(contents['check_openai_provenance.py'], policy.__file__, 'exec'),
         policy.__dict__)
    ledgers = [policy.read_json(policy.safe_file(root, path)) for path in args.shard]
    roots = {'LionSR/TNLean': root}
    if args.upstream_root:
        roots['openai/math'] = args.upstream_root.resolve()
    count = policy.validate(ledgers, json.loads(contents['openai-math.schema.json']),
                            roots, scan=True)

    canonical = json.loads(contents['canonical-collisions.json'])
    policy.require(canonical['revision'] == POLICY_REVISION, 'Wrong collision baseline revision')
    old_ids = {entry['id'] for entry in canonical['entries']}
    old_keys = {(entry['repository'], entry['declaration']) for entry in canonical['entries']}
    for ledger in ledgers:
        for entry in ledger['entries']:
            policy.require(entry['id'] not in old_ids,
                           f'ID collides with canonical ledger: {entry["id"]}')
            key = (entry['downstream']['repository'].casefold(),
                   entry['downstream']['declaration'])
            policy.require(key not in old_keys,
                           f'Declaration collides with canonical ledger: {key}')

    print(f'PASS: {count} new entries; canonical entry checks and complete branch notice scan.')
    print(f'PASS: new IDs and declarations are disjoint from {len(canonical["entries"])} canonical entries.')
    print(f'Packaged policy revision: {POLICY_REVISION}')
    for name, digest in HASHES.items():
        print(f'Policy SHA-256: {name}: {digest}')
    if not args.upstream_root:
        print('Manuscript labels were not rechecked; use --upstream-root for that check.')
    print('Scope: shard validation; canonical CLI license/source-audit checks and historical evidence were not rerun.')


if __name__ == '__main__':
    main()
