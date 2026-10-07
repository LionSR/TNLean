#!/usr/bin/env python3
"""Validate all nine source-gate proof shards with the packaged canonical policy.

This checks recorded provenance and evidence; it does not recompile Lean.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--upstream-root', type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    validator = root / 'docs/provenance/evidence/canonical-policy-18a6dd4d/validate-shards.py'
    command = [sys.executable, str(validator), '--root', str(root)]
    for name in ['8768-source-preparation', '8769-party-factorization',
                 '8769-unused-pair-sources', '8769-common-source-spaces',
                 '8769-source-gate-density', '8769-source-block-contraction',
                 '8769-party-coarsening', '8769-selective-source-preparation',
                 '8769-chronological-source-expansion']:
        command.extend(['--shard', f'docs/provenance/openai-math.d/{name}.json'])
    shard_paths = [command[i + 1] for i, arg in enumerate(command) if arg == '--shard']
    total = sum(len(json.loads((root / p).read_text())['entries']) for p in shard_paths)
    if len(shard_paths) != 9 or total != 323:
        raise RuntimeError(f'Expected nine shards containing 323 declarations; got {len(shard_paths)} and {total}')
    if args.upstream_root is not None:
        command.extend(['--upstream-root', str(args.upstream_root.resolve())])
    return subprocess.run(command, cwd=root).returncode


if __name__ == '__main__':
    raise SystemExit(main())
