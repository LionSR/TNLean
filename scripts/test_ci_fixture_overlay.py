#!/usr/bin/env python3
"""Run the strict test overlay of ci_lean_checks.py against Lake/Lean stand-ins.

Never invokes Lean. A test may import another test (for example a
``TNLeanTest.Support`` fixture); its object must come from a fresh overlay that
precedes every Lake package path, never from a stale production build tree.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import yaml

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / 'scripts/ci_lean_checks.py'
WORKFLOW = yaml.safe_load((ROOT / '.github/workflows/pr-ci.yml').read_text())
STEP_NAME = 'Check changed Lean files and affected tests strictly'
FLAGS = ['-DautoImplicit=false', '-DrelaxedAutoImplicit=false', '-Dpp.unicode.fun=true',
         '-DmaxSynthPendingDepth=3', '-Dlinter.mathlibStandardSet=true', '-DwarningAsError=true']

# Lake prepends its package paths to the ambient LEAN_PATH.
LAKE = '''#!/bin/bash
set -eu
test "$1" = env
shift
if [ "$TEST_PACKAGE_PATH" = unset ]; then
  unset LEAN_PATH
elif [ -z "$TEST_PACKAGE_PATH" ]; then
  export LEAN_PATH=
else
  export LEAN_PATH="$TEST_PACKAGE_PATH${LEAN_PATH:+:$LEAN_PATH}"
fi
exec "$@"
'''
# Portable stand-in: drop the options and run the command.
TIMEOUT = '''#!/bin/bash
while [ "${1#-}" != "$1" ]; do shift; done
shift
exec "$@"
'''
LEAN = '''import json
import os
from pathlib import Path
import sys

args = sys.argv[1:]
with open(os.environ['TEST_CALLS'], 'a') as log:
    log.write(json.dumps({'args': args, 'path': os.environ.get('LEAN_PATH', '')}) + '\\n')
source = Path(args[-1])
if source.stem == os.environ.get('TEST_FAIL_AT'):
    sys.exit(23)
if source.stem == 'FixtureUser':
    # Lean selects the first root namespace directory, even if the requested
    # object is absent there; it does not fall through to later package roots.
    roots = (Path(root) / 'TNLeanTest'
             for root in os.environ.get('LEAN_PATH', '').split(':') if root)
    root = next((path for path in roots if path.is_dir()), None)
    fixture = root / 'Support/Fixture.olean' if root else None
    if fixture is None or not fixture.is_file() or fixture.read_text() != 'fresh fixture':
        sys.exit('fixture import did not resolve to the fresh overlay')
if '-o' in args:
    Path(args[args.index('-o') + 1]).write_text('fresh fixture')
'''
FILES = {
    'TNLean/Core.lean': 'import Mathlib\n',
    'TNLeanTest/Support/Fixture.lean': 'import TNLean.Core\n',
    'TNLeanTest/FixtureUser.lean': 'import TNLeanTest.Support.Fixture\n',
    'TNLeanTest/Plain.lean': 'import TNLean.Core\n',
}


class FixtureOverlayTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='tnlean-fixture-step-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.repo = self.root / 'repo'
        for path, text in FILES.items():
            p = self.repo / path
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(text)
        self.bin = self.root / 'bin'
        self.bin.mkdir()
        for name, source in [('lake', LAKE), ('timeout', TIMEOUT),
                             ('lean', f'#!{sys.executable}\n' + LEAN)]:
            path = self.bin / name
            path.write_text(source)
            path.chmod(0o755)
        # Spaces and shell metacharacters must survive bash -c argument passing.
        self.tmp = self.root / "overlay outputs ' $quoted"
        self.tmp.mkdir()
        self.calls = self.root / 'calls.jsonl'
        self.packages = [self.root / 'production build', self.root / 'dependency build']
        self.stale = self.packages[0] / 'TNLeanTest/Support/Fixture.olean'
        self.stale.parent.mkdir(parents=True)
        self.stale.write_text('stale production fixture')
        self.env = {**os.environ, 'PATH': f'{self.bin}:' + os.environ['PATH'],
                    'TMPDIR': str(self.tmp), 'TEST_CALLS': str(self.calls),
                    'LEAN_PATH': str(self.root / 'ambient path'),
                    'TEST_PACKAGE_PATH': ':'.join(map(str, self.packages)),
                    'TEST_FAIL_AT': '', 'BASE_SHA': ''}

    def run_strict(self):
        production_before = sorted(self.stale.parent.parent.rglob('*'))
        result = subprocess.run([sys.executable, str(SCRIPT), 'strict', '--root', str(self.repo),
                                 '--jobs', '2'], env=self.env,
                                capture_output=True, text=True, timeout=60)
        calls = [json.loads(line) for line in self.calls.read_text().splitlines()]
        # The overlay is removed on success and failure; production is untouched.
        self.assertEqual(list(self.tmp.iterdir()), [])
        self.assertEqual(sorted(self.stale.parent.parent.rglob('*')), production_before)
        if self.stale.exists():
            self.assertEqual(self.stale.read_text(), 'stale production fixture')
        return result, calls

    def check_calls(self, calls, package_path):
        by_source = {call['args'][-1]: call for call in calls}
        self.assertEqual(sorted(by_source), sorted(p for p in FILES if p.startswith('TNLeanTest/')))
        overlay = Path(by_source['TNLeanTest/Support/Fixture.lean']['args'][-2]).parents[2]
        self.assertEqual(overlay.parent, self.tmp)
        for source, call in by_source.items():
            self.assertEqual(call['args'], ['-j1', *FLAGS, '-o',
                                            str(overlay / (source[:-len('.lean')] + '.olean')),
                                            source])
            self.assertEqual(call['path'], str(overlay) +
                             (':' + package_path if package_path else ''))
        # The fixture is elaborated before its importer.
        order = [call['args'][-1] for call in calls]
        self.assertLess(order.index('TNLeanTest/Support/Fixture.lean'),
                        order.index('TNLeanTest/FixtureUser.lean'))

    def test_overlay_precedes_all_lake_paths_and_preserves_arguments(self):
        result, calls = self.run_strict()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.check_calls(calls, self.env['TEST_PACKAGE_PATH'] + ':' + self.env['LEAN_PATH'])

    def test_empty_production_namespace_does_not_hide_the_overlay(self):
        self.stale.unlink()
        result, calls = self.run_strict()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.check_calls(calls, self.env['TEST_PACKAGE_PATH'] + ':' + self.env['LEAN_PATH'])

    def test_empty_or_unset_ambient_path_preserves_lake_package_paths(self):
        for value in ('', None):
            with self.subTest(path=value):
                self.calls.unlink(missing_ok=True)
                if value is None:
                    self.env.pop('LEAN_PATH', None)
                else:
                    self.env['LEAN_PATH'] = value
                result, calls = self.run_strict()
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.check_calls(calls, self.env['TEST_PACKAGE_PATH'])

    def test_empty_or_unset_lake_path_has_no_empty_search_entry(self):
        for value in ('', 'unset'):
            with self.subTest(path=value):
                self.calls.unlink(missing_ok=True)
                self.env['TEST_PACKAGE_PATH'] = value
                result, calls = self.run_strict()
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.check_calls(calls, '')

    def test_failure_is_reported_and_cleans_overlay(self):
        self.env['TEST_FAIL_AT'] = 'Plain'
        result, calls = self.run_strict()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn('TNLeanTest/Plain.lean', result.stdout)
        self.assertIn('::error file=TNLeanTest/Plain.lean::', result.stdout)

    def test_ci_regression_wiring(self):
        build = WORKFLOW['jobs']['build']['steps']
        names = [step.get('name') for step in build]
        strict = build[names.index(STEP_NAME)]
        early = build[names.index('Build changed Lean modules early')]
        full = names.index('Build Lean project and capture timings')
        self.assertLess(names.index('Build changed Lean modules early'), full)
        self.assertLess(full, names.index(STEP_NAME))
        self.assertIn('python3 scripts/ci_lean_checks.py strict', strict['run'])
        self.assertIn('python3 scripts/ci_lean_checks.py early', early['run'])
        self.assertIn('"$RUNNER_TEMP/lake-build.log"', early['run'])
        self.assertNotIn('continue-on-error', strict)
        self.assertNotIn('continue-on-error', early)
        # No hand-written per-module test steps remain in the build job.
        self.assertEqual([n for n in names if n and n.startswith('Test ')], [])
        script = 'scripts/test_ci_fixture_overlay.py'
        # PyYAML treats the YAML 1.1 key "on" as True.
        for event in ('push', 'pull_request'):
            self.assertIn(script, WORKFLOW[True][event]['paths'])
            self.assertIn('scripts/ci_lean_checks.py', WORKFLOW[True][event]['paths'])
        filter_step = next(step for step in WORKFLOW['jobs']['changes']['steps']
                           if step.get('id') == 'filter')
        filters = yaml.safe_load(filter_step['with']['filters'])
        self.assertIn(script, filters['module_policy'])
        self.assertIn('scripts/ci_lean_checks.py', filters['lean'])
        job = WORKFLOW['jobs']['file-length']
        self.assertIn("needs.changes.outputs.module_policy == 'true'", job['if'])
        self.assertIn("needs.changes.outputs.workflow == 'true'", job['if'])
        check = next(step for step in job['steps']
                     if step.get('name') == 'Test CI fixture import overlay')
        self.assertEqual(check['run'], f'python3 {script}')
        self.assertNotIn('if', check)
        self.assertNotIn('continue-on-error', check)


if __name__ == '__main__':
    unittest.main()
