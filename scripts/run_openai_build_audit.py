#!/usr/bin/env python3
"""Record bounded cache-first Lean attempts; never build after a failed cache gate."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def run_audit(worktree, lake, output, targets, seconds=600, axioms=None):
    worktree, lake, output = worktree.resolve(), lake.resolve(), output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    report = {'worktree': str(worktree), 'lake': str(lake), 'attempts': [],
              'configuration_sha256': {p: hashlib.sha256((worktree/p).read_bytes()).hexdigest()
                  for p in ['lean-toolchain', 'lake-manifest.json']},
              'environment': {k: os.environ[k] for k in ['MATHLIB_CACHE_DIR', 'XDG_CACHE_HOME', 'MATHLIB_CACHE_DEBUG_USE_LEGACY'] if k in os.environ},
              'library_build_status': 'not_attempted', 'axiom_status': 'not_attempted'}
    def save():
        (output/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    def run(args, label):
        start = time.monotonic()
        log = output/(label+'.log')
        env = dict(os.environ, PATH=str(lake.parent)+os.pathsep+os.environ['PATH'])
        with log.open('w') as stream:
            result = subprocess.run(['timeout', '--kill-after=10s', str(seconds), *map(str, args)],
                                    cwd=worktree, env=env, stdout=stream, stderr=subprocess.STDOUT)
        report['attempts'].append({'command': list(map(str,args)), 'cwd': str(worktree),
            'timeout_seconds': seconds, 'exit_code': result.returncode,
            'elapsed_seconds': round(time.monotonic()-start, 3),
            'finished_at': datetime.now(timezone.utc).isoformat(),
            'log': log.name, 'log_sha256': hashlib.sha256(log.read_bytes()).hexdigest()})
        save()
        return result.returncode == 0
    run([lake, '--version'], 'lake-version')
    if not run([lake, 'exe', 'cache', 'get'], 'cache-get'):
        report['cache_gate'] = 'failed_cache_command'; save(); return report
    sentinel = worktree/'.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean'
    report['cache_sentinel'] = str(sentinel)
    if not sentinel.is_file():
        report['cache_gate'] = 'missing_Mathlib.olean'; save(); return report
    report['cache_gate'] = 'passed'
    successes = [run([lake, 'build', target], 'build-'+target) for target in targets]
    if targets:
        report['library_build_status'] = 'passed' if all(successes) else 'failed'
    if axioms and targets and all(successes):
        report['axiom_status'] = 'command_passed_requires_review' if run(
            [lake, 'env', 'lean', axioms], 'axioms') else 'failed'
    save()
    return report


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--worktree', type=Path, required=True)
    p.add_argument('--lake', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--target', action='append', default=[])
    p.add_argument('--timeout', type=int, default=600)
    p.add_argument('--axioms')
    a = p.parse_args()
    result = run_audit(a.worktree, a.lake, a.output, a.target, a.timeout, a.axioms)
    if result['cache_gate'] != 'passed' or result['library_build_status'] == 'failed' or result['axiom_status'] == 'failed':
        raise SystemExit(1)


if __name__ == '__main__': main()
