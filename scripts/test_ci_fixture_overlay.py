#!/usr/bin/env python3
"""Execute the CI fixture step against Lake/Lean stand-ins; never invokes Lean."""
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
WORKFLOW = yaml.safe_load((ROOT / '.github/workflows/pr-ci.yml').read_text())
STEP_NAME = 'Test PEPS dual flux paths and quantum-double local terms'
EXAMPLES = ('TorusDualFluxString', 'TorusDualFluxParent',
            'TorusDualRectangle', 'QuantumDoublePhysicalTerms')
FLAGS = ['-DautoImplicit=false', '-DrelaxedAutoImplicit=false', '-Dpp.unicode.fun=true',
         '-DmaxSynthPendingDepth=3', '-Dlinter.mathlibStandardSet=true', '-DwarningAsError=true']

# Lake prepends its package paths to the ambient LEAN_PATH. Execute the
# actual workflow command after constructing that environment.
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
LEAN = '''import json
import os
from pathlib import Path
import sys

args = sys.argv[1:]
with open(os.environ['TEST_CALLS'], 'a') as log:
    log.write(json.dumps({'args': args, 'path': os.environ.get('LEAN_PATH', '')}) + '\\n')
source = Path(args[-1])
output = Path(args[args.index('-o') + 1])
if source.stem == os.environ.get('TEST_FAIL_AT'):
    sys.exit(23)
if source.stem == 'TorusDualFluxParent':
    # Lean selects the first root namespace directory, even if the requested
    # object is absent there; it does not fall through to later package roots.
    roots = (Path(root) / 'TNLeanTest'
             for root in os.environ.get('LEAN_PATH', '').split(':') if root)
    root = next((path for path in roots if path.is_dir()), None)
    fixture = root / 'TorusDualFluxString.olean' if root else None
    if fixture is None or not fixture.is_file() or fixture.read_text() != 'fresh fixture':
        sys.exit('fixture import did not resolve to the fresh overlay')
output.write_text('fresh fixture')
'''


class FixtureOverlayTests(unittest.TestCase):
    def setUp(self):
        self.step = next(step for step in WORKFLOW['jobs']['build']['steps']
                         if step.get('name') == STEP_NAME)
        temporary = tempfile.TemporaryDirectory(prefix='tnlean-fixture-step-')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.bin = self.root / 'bin'
        self.bin.mkdir()
        for name, source in [('lake', LAKE), ('lean', f'#!{sys.executable}\n' + LEAN)]:
            path = self.bin / name
            path.write_text(source)
            path.chmod(0o755)
        # Spaces and shell metacharacters must survive bash -c argument passing.
        self.tmp = self.root / "overlay outputs ' $quoted"
        self.tmp.mkdir()
        self.calls = self.root / 'calls.jsonl'
        self.packages = [self.root / 'production build', self.root / 'dependency build']
        self.stale = self.packages[0] / 'TNLeanTest/TorusDualFluxString.olean'
        self.stale.parent.mkdir(parents=True)
        self.stale.write_text('stale production fixture')
        self.env = {**os.environ, 'PATH': f'{self.bin}:' + os.environ['PATH'],
                    'TMPDIR': str(self.tmp), 'TEST_CALLS': str(self.calls),
                    'LEAN_PATH': str(self.root / 'ambient path'),
                    'TEST_PACKAGE_PATH': ':'.join(map(str, self.packages)),
                    'TEST_FAIL_AT': ''}

    def run_step(self):
        production_before = list(self.stale.parent.iterdir())
        result = subprocess.run(['bash', '--noprofile', '--norc', '-e', '-o', 'pipefail',
                                 '-c', self.step['run']], cwd=self.root, env=self.env,
                                capture_output=True, text=True, timeout=15)
        calls = [json.loads(line) for line in self.calls.read_text().splitlines()]
        # The trap must remove all overlay artifacts on success and failure.
        self.assertEqual(list(self.tmp.iterdir()), [])
        self.assertEqual(list(self.stale.parent.iterdir()), production_before)
        if self.stale.exists():
            self.assertEqual(self.stale.read_text(), 'stale production fixture')
        return result, calls

    def check_calls(self, calls, examples, package_path):
        self.assertEqual(len(calls), len(examples))
        overlay = Path(calls[0]['args'][-2]).parents[1]
        self.assertEqual(overlay.parent, self.tmp)
        for call, example in zip(calls, examples):
            self.assertEqual(call['args'], FLAGS + [
                '-o', str(overlay / 'TNLeanTest' / (example + '.olean')),
                f'TNLeanTest/{example}.lean'])
            self.assertEqual(call['path'], str(overlay) +
                             (':' + package_path if package_path else ''))

    def test_overlay_precedes_all_lake_paths_and_preserves_arguments(self):
        result, calls = self.run_step()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.check_calls(calls, EXAMPLES, self.env['TEST_PACKAGE_PATH'] +
                         ':' + self.env['LEAN_PATH'])

    def test_empty_production_namespace_does_not_hide_the_overlay(self):
        self.stale.unlink()
        result, calls = self.run_step()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.check_calls(calls, EXAMPLES, self.env['TEST_PACKAGE_PATH'] +
                         ':' + self.env['LEAN_PATH'])

    def test_empty_or_unset_ambient_path_preserves_lake_package_paths(self):
        for value in ('', None):
            with self.subTest(path=value):
                self.calls.unlink(missing_ok=True)
                if value is None:
                    self.env.pop('LEAN_PATH', None)
                else:
                    self.env['LEAN_PATH'] = value
                result, calls = self.run_step()
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.check_calls(calls, EXAMPLES, self.env['TEST_PACKAGE_PATH'])

    def test_empty_or_unset_lake_path_has_no_empty_search_entry(self):
        for value in ('', 'unset'):
            with self.subTest(path=value):
                self.calls.unlink(missing_ok=True)
                self.env['TEST_PACKAGE_PATH'] = value
                result, calls = self.run_step()
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.check_calls(calls, EXAMPLES, '')

    def test_failure_propagates_stops_the_loop_and_cleans_overlay(self):
        self.env['TEST_FAIL_AT'] = 'TorusDualFluxParent'
        result, calls = self.run_step()
        self.assertEqual(result.returncode, 23, result.stdout + result.stderr)
        self.check_calls(calls, EXAMPLES[:2], self.env['TEST_PACKAGE_PATH'] +
                         ':' + self.env['LEAN_PATH'])

    def test_timeout_and_ci_regression_wiring(self):
        self.assertEqual(self.step['timeout-minutes'], 3)
        self.assertNotIn('continue-on-error', self.step)
        script = 'scripts/test_ci_fixture_overlay.py'
        # PyYAML treats the YAML 1.1 key "on" as True.
        for event in ('push', 'pull_request'):
            self.assertIn(script, WORKFLOW[True][event]['paths'])
        filter_step = next(step for step in WORKFLOW['jobs']['changes']['steps']
                           if step.get('id') == 'filter')
        filters = yaml.safe_load(filter_step['with']['filters'])
        self.assertIn(script, filters['module_policy'])
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
