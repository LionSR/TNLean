#!/usr/bin/env python3
"""Configuration, provenance, pruning, and workflow guards; never invokes Lean."""
from __future__ import annotations

import copy
import contextlib
import io
import subprocess
import json
import os
import re
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import yaml

import ci_compatible_cache as guard
from lean_import_syntax import strip_lean_comments

ROOT = Path(__file__).resolve().parents[1]
OLD = 'a' * 40
NEW = 'b' * 40
VERSION = 'f' * 64
QIC_LAYOUT = '''name = "QICLean"
defaultTargets = ["QICLean"]
[[lean_lib]]
name = "QICLean"
[[lean_exe]]
name = "lint_style"
srcDir = "scripts"
root = "LintStyle"
supportInterpreter = true
'''


# Only these two exact strict checks may precede the full root after their
# production import closure is built. Keep all commands and resource limits.
ACTUAL_ROUND_EARLY_STEPS = yaml.safe_load(r"""
      - name: Build actual finite-round transport prerequisites early
        env:
          LEAN_NUM_THREADS: '1'
        run: |
          set -eo pipefail
          test -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean
          lake --fail-fast build \
            +TNLean.PEPS.AreaLaw.Scan.ActualRoundTransport:olean \
            +TNLean.PEPS.AreaLaw.Scan.FillTransportEndpoints:olean \
            2>&1 | tee -a "$RUNNER_TEMP/lake-build.log"

      - name: Check actual finite-round transport production module strictly
        timeout-minutes: 2
        run: >
          LEAN_NUM_THREADS=1 timeout --signal=INT --kill-after=5s 90s lake env lean -j1
          -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true
          -DmaxSynthPendingDepth=3 -Dlinter.mathlibStandardSet=true -DwarningAsError=true
          TNLean/PEPS/AreaLaw/Scan/ActualRoundTransport.lean

      - name: Test actual finite-round transport signatures and axioms strictly
        timeout-minutes: 4
        run: |
          set -eo pipefail
          for source in TNLeanTest/ActualRoundTransport.lean \
              TNLeanTest/ActualRoundTransportAxioms.lean; do
            LEAN_NUM_THREADS=1 timeout --signal=INT --kill-after=5s 90s lake env lean -j1 \
              -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true \
              -DmaxSynthPendingDepth=3 -Dlinter.mathlibStandardSet=true -DwarningAsError=true \
              "$source"
          done

""")
ACTUAL_ROUND_BUILD_NAME = ACTUAL_ROUND_EARLY_STEPS[0]['name']
ACTUAL_ROUND_STRICT_NAMES = tuple(step['name'] for step in ACTUAL_ROUND_EARLY_STEPS[1:])
FULL_BUILD_NAME = 'Build Lean project and capture timings'
EXPECTED_FULL_BUILD = yaml.safe_load(r"""
      - name: Build Lean project and capture timings
        run: |
          set -eo pipefail
          # Check the String Order capstones before unrelated library targets.
          lake build TNLean.MPS.Symmetry.PhysicalStringBlockOrder \
            TNLean.MPS.Examples.StringOrderScalarPhase \
            2>&1 | tee -a "$RUNNER_TEMP/lake-build.log"
          {
            lake build
            lake build lint_style
          } 2>&1 | tee -a "$RUNNER_TEMP/lake-build.log"

""")[0]


def pinned_inputs():
    data = {p: (ROOT / p).read_bytes() for p in guard.INPUTS}
    manifest = json.loads(data['lake-manifest.json'])
    qic = next(p for p in manifest['packages'] if p['name'] == 'qiclean')
    original = qic['rev']
    qic['rev'] = qic['inputRev'] = OLD
    data['lake-manifest.json'] = json.dumps(manifest).encode()
    data['lakefile.toml'] = data['lakefile.toml'].replace(original.encode(), OLD.encode())
    return data


def updated(data):
    return {p: b.replace(OLD.encode(), NEW.encode()) for p, b in data.items()}


def mutate_manifest(data, change):
    parsed = json.loads(data['lake-manifest.json'])
    change(parsed)
    data['lake-manifest.json'] = json.dumps(parsed).encode()


def commit(repo):
    guard.git(repo, 'add', '.')
    # Detached maintenance can outlive commit and race TemporaryDirectory cleanup.
    guard.git(repo, '-c', 'maintenance.auto=false',
              '-c', 'user.name=Cache Guard Test', '-c', 'user.email=cache-test@example.invalid',
              'commit', '-qm', 'fixture')
    return guard.git(repo, 'rev-parse', 'HEAD').decode().strip()


def put(repo, path, data):
    p = repo / path
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(data)


class ConfigurationTests(unittest.TestCase):
    def setUp(self):
        self.old = pinned_inputs()
        self.new = updated(self.old)

    def test_revision_only_positive(self):
        self.assertEqual(guard.compatible_configs(self.old, self.new), (OLD, NEW))

    def test_toml_comments_and_formatting_are_not_options(self):
        self.new['lakefile.toml'] += b'\n# harmless comment\n'
        guard.compatible_configs(self.old, self.new)

    def test_missing_files(self):
        for path in guard.INPUTS:
            new = copy.deepcopy(self.new)
            del new[path]
            with self.subTest(path=path), self.assertRaises(guard.Refusal):
                guard.compatible_configs(self.old, new)

    def test_toolchain_bytes(self):
        self.new['lean-toolchain'] += b'\n'
        with self.assertRaises(guard.Refusal):
            guard.compatible_configs(self.old, self.new)

    def test_manifest_negative_matrix(self):
        changes = {
            'mathlib': lambda d: d['packages'][1].update(rev='c' * 40),
            'gametheory': lambda d: d['packages'][2].update(rev='d' * 40),
            'qic_url': lambda d: d['packages'][0].update(url='https://example.invalid/QICLean.git'),
            'qic_subdir': lambda d: d['packages'][0].update(subDir='src'),
            'qic_name': lambda d: d['packages'][0].update(name='other'),
            'qic_config': lambda d: d['packages'][0].update(configFile='lakefile.lean'),
            'qic_input_tag': lambda d: d['packages'][0].update(inputRev='main'),
            'qic_short_rev': lambda d: d['packages'][0].update(rev='deadbeef'),
            'other_subdir': lambda d: d['packages'][2].update(subDir='src'),
            'other_url': lambda d: d['packages'][2].update(url='https://example.invalid/Brouwer'),
            'other_mutable_pin': lambda d: d['packages'][2].update(rev='main'),
            'dependency_removed': lambda d: d['packages'].pop(),
            'duplicate_dependency': lambda d: d['packages'].append(copy.deepcopy(d['packages'][0])),
            'unknown_top_schema': lambda d: d.update(newField=True),
            'unknown_package_schema': lambda d: d['packages'][0].update(newField=True),
            'version': lambda d: d.update(version='2.0.0'),
            'packages_dir': lambda d: d.update(packagesDir='vendor'),
        }
        for name, change in changes.items():
            with self.subTest(name=name):
                new = copy.deepcopy(self.new)
                mutate_manifest(new, change)
                with self.assertRaises(guard.Refusal):
                    guard.compatible_configs(self.old, new)

    def test_toml_negative_matrix(self):
        for before, after in [
            (b'maxSynthPendingDepth = 3', b'maxSynthPendingDepth = 4'),
            (b'weak.linter.mathlibStandardSet = true', b'weak.linter.mathlibStandardSet = false'),
            (guard.QIC_URL.encode(), b'https://example.invalid/QICLean.git'),
            (b'defaultTargets = ["TNLean"]', b'defaultTargets = []'),
            (NEW.encode(), b'main'),
        ]:
            with self.subTest(after=after):
                new = copy.deepcopy(self.new)
                new['lakefile.toml'] = new['lakefile.toml'].replace(before, after)
                with self.assertRaises(guard.Refusal):
                    guard.compatible_configs(self.old, new)
        self.new['lakefile.toml'] += b'\n[unknownSchema]\nenabled = true\n'
        with self.assertRaises(guard.Refusal):
            guard.compatible_configs(self.old, self.new)


class BaselineTests(unittest.TestCase):
    def setUp(self):
        self.old = pinned_inputs()
        self.new = updated(self.old)

    def test_stacked_pr_uses_main_configuration_not_pr_base(self):
        with patch.object(guard, 'config_at', return_value=self.old) as read:
            selected, _, revisions = guard.select_baseline(Path('.'), self.new, [OLD])
            self.assertEqual((selected, revisions), (OLD, (OLD, NEW)))
            read.assert_called_once_with(Path('.'), OLD)

    def test_main_push_selects_previous_compatible_configuration(self):
        with patch.object(guard, 'config_at', side_effect=[self.new, self.old]):
            self.assertEqual(guard.select_baseline(Path('.'), self.new, [NEW, OLD])[0], OLD)

    def test_bounded_fail_closed_search(self):
        with patch.object(guard, 'config_at', return_value=self.new) as read:
            with self.assertRaises(guard.Refusal):
                guard.select_baseline(Path('.'), self.new, [NEW] * (guard.WINDOW + 1))
            self.assertEqual(read.call_count, guard.WINDOW)

    def test_duplicate_json_key_refused(self):
        raw = self.old['lake-manifest.json'].replace(b'"version": "1.3.0"',
             b'"version": "1.3.0", "version": "1.3.0"')
        with self.assertRaises(guard.Refusal):
            guard.manifest(raw)


class AdditiveTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        guard.git(self.repo, 'init', '-q')
        for path in guard.INPUTS:
            put(self.repo, path, 'metadata bytes')
        put(self.repo, 'lakefile.toml', QIC_LAYOUT)
        put(self.repo, 'QICLean.lean', 'import QICLean.Analysis\n')
        put(self.repo, 'QICLean/Analysis.lean', 'import QICLean.Analysis.Existing\n')
        put(self.repo, 'QICLean/Analysis/Existing.lean', 'def existing := 1\n')
        self.old = commit(self.repo)
        put(self.repo, 'QICLean/Analysis.lean', 'import QICLean.Analysis.Existing\nimport QICLean.Analysis.Added\n')
        put(self.repo, 'QICLean/Analysis/Added.lean', 'def added := 2\n')
        put(self.repo, 'docs/note.md', 'A proof note.\n')

    def test_additive_module_aggregator_docs(self):
        self.assertEqual(guard.additive_qic(self.repo, self.old, commit(self.repo)),
                         ['QICLean.Analysis'])

    def test_metadata_changed_or_missing(self):
        for path in guard.INPUTS:
            with self.subTest(path=path):
                before = (self.repo / path).read_text()
                put(self.repo, path, 'changed')
                with self.assertRaises(guard.Refusal):
                    guard.additive_qic(self.repo, self.old, commit(self.repo))
                put(self.repo, path, before)
                (self.repo / path).unlink()
                with self.assertRaises(guard.Refusal):
                    guard.additive_qic(self.repo, self.old, commit(self.repo))
                put(self.repo, path, before)

    def test_changed_existing_proof(self):
        put(self.repo, 'QICLean/Analysis/Existing.lean', 'def existing := 9\n')
        with self.assertRaises(guard.Refusal):
            guard.additive_qic(self.repo, self.old, commit(self.repo))

    def test_deleted_or_renamed_module(self):
        (self.repo / 'QICLean/Analysis/Existing.lean').rename(self.repo / 'QICLean/Analysis/Renamed.lean')
        with self.assertRaises(guard.Refusal):
            guard.additive_qic(self.repo, self.old, commit(self.repo))

    def test_nonadditive_aggregator(self):
        put(self.repo, 'QICLean/Analysis.lean', 'import QICLean.Analysis.Added\n')
        with self.assertRaises(guard.Refusal):
            guard.additive_qic(self.repo, self.old, commit(self.repo))

    def test_unknown_configuration(self):
        put(self.repo, 'lakefile.lean', 'import Lake\n')
        with self.assertRaises(guard.Refusal):
            guard.additive_qic(self.repo, self.old, commit(self.repo))


class NonBuildPathTests(unittest.TestCase):
    setUp = AdditiveTests.setUp

    def test_fixture_commit_disables_automatic_maintenance(self):
        with patch.object(guard, 'git', side_effect=[b'', b'', OLD.encode()]) as git:
            self.assertEqual(commit(self.repo), OLD)
            self.assertEqual(git.call_args_list[1].args[1:3],
                             ('-c', 'maintenance.auto=false'))

    def test_reviewed_evidence_tests_and_workflow(self):
        for path in (
            '.github/workflows/pr-ci.yml', 'QICLeanTest/ConditionalTwoFamilies.lean',
            'blueprint/src/references.bib',
            'docs/audits/2026-10-06_hermitian_intertwiner_paths_validation.json',
            'docs/provenance/openai-math.d/8765.json',
            'docs/provenance/evidence/8760/QICAxioms.lean',
            'docs/provenance/evidence/8760/QICLean.Entropy.TwoFamilies.log',
            'docs/provenance/evidence/shiftedDensityPowers8767/checks.json',
        ):
            put(self.repo, path, 'source-only evidence\n')
        self.assertEqual(guard.additive_qic(self.repo, self.old, commit(self.repo)),
                         ['QICLean.Analysis'])

    def test_not_a_blanket_docs_or_workflow_exception(self):
        for path in ('scripts/helper.lean', 'docs/provenance/evidence/8760/run.py',
                     'docs/provenance/evidence/8760/cached.olean',
                     'docs/provenance/config.toml', '.github/workflows/build.yml',
                     'QICLeanTest/nested/Example.lean'):
            with self.subTest(path=path):
                self.assertFalse(guard.non_build_qic_path(path))

    def test_ignored_path_cannot_be_symlink_executable_or_deleted(self):
        path = self.repo / 'docs/provenance/evidence/8760/QICAxioms.lean'
        path.parent.mkdir(parents=True)
        path.symlink_to('../../../QICLean/Analysis/Existing.lean')
        with self.assertRaisesRegex(guard.Refusal, 'non-build change is not a regular file'):
            guard.additive_qic(self.repo, self.old, commit(self.repo))
        path.unlink()
        path.write_text('collector\n')
        path.chmod(0o755)
        with self.assertRaisesRegex(guard.Refusal, 'non-build change is not a regular file'):
            guard.additive_qic(self.repo, self.old, commit(self.repo))
        path.chmod(0o644)
        before = commit(self.repo)
        path.unlink()
        put(self.repo, 'QICLean/Analysis/Another.lean', 'def another := 3\n')
        with self.assertRaisesRegex(guard.Refusal, 'non-build change is not a regular file'):
            guard.additive_qic(self.repo, before, commit(self.repo))

    def test_non_build_layout_even_when_identical_between_revisions(self):
        original = guard.tomllib.loads(QIC_LAYOUT)
        changes = (
            lambda c: c.update(srcDir='docs'),
            lambda c: c.update(extraDepTargets=['evidence']),
            lambda c: c.update(defaultTargets=['QICLean', 'lint_style']),
            lambda c: c['lean_lib'][0].update(roots=['QICLean', 'docs']),
            lambda c: c['lean_lib'][0].update(globs=['**']),
            lambda c: c['lean_lib'].append({'name': 'QICLeanTest'}),
            lambda c: c['lean_exe'][0].update(srcDir='docs/provenance/evidence'),
        )
        for change in changes:
            config = copy.deepcopy(original)
            change(config)
            with self.subTest(config=config), \
                    patch.object(guard, 'file_at', return_value=QIC_LAYOUT.encode()), \
                    patch.object(guard.tomllib, 'loads', return_value=config), \
                    self.assertRaisesRegex(guard.Refusal, 'non-build path scope'):
                guard.require_non_build_qic_scope(self.repo, OLD, NEW, ({}, {}))

    def test_library_cannot_reference_ignored_inputs(self):
        for source in (
            'import QICLeanTest.ConditionalTwoFamilies\ndef added := 2\n',
            'public import docs.provenance.evidence.checks\ndef added := 2\n',
            'import\n  docs.provenance.evidence.checks\ndef added := 2\n',
            'def evidence := "docs/provenance/evidence/8760/checks.json"\n',
            'run_cmd IO.FS.readFile ("do" ++ "cs/file")\n',
        ):
            with self.subTest(source=source):
                put(self.repo, 'QICLean/Analysis/Added.lean', source)
                with self.assertRaisesRegex(guard.Refusal, 'QIC source (references|may read)'):
                    guard.additive_qic(self.repo, self.old, commit(self.repo))

    def test_sorted_refusal_witness(self):
        put(self.repo, 'Z.txt', 'unknown\n')
        put(self.repo, 'A.txt', 'unknown\n')
        with self.assertRaisesRegex(guard.Refusal, 'aggregator: A.txt$'):
            guard.additive_qic(self.repo, self.old, commit(self.repo))


class ProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.key = 'tnlean-build-' + 'e' * 64 + '-' + OLD
        self.caches = {'total_count': 1, 'actions_caches': [
            {'key': self.key, 'ref': 'refs/heads/main', 'version': VERSION}]}
        self.runs = {'workflow_runs': [{'id': 1, 'head_sha': OLD, 'head_branch': 'main',
                     'event': 'push', 'status': 'completed', 'path': '.github/workflows/pr-ci.yml'}]}
        self.jobs = {1: {'jobs': [{'name': 'build', 'conclusion': 'success', 'head_sha': OLD,
                                'labels': ['ubuntu-latest'], 'steps': [
                                    {'name': 'Save Lean build cache (main only)', 'conclusion': 'success'}]}]}}

    def check(self):
        guard.validate_provenance(self.key, OLD, self.caches, self.runs, self.jobs, VERSION)

    def test_verified_main_success(self):
        self.check()

    def test_branch_shadow(self):
        self.caches['actions_caches'][0]['ref'] = 'refs/pull/123/merge'
        with self.assertRaises(guard.Refusal):
            self.check()

    def test_missing_or_ambiguous_cache(self):
        for count in (0, 2, 101):
            self.caches['total_count'] = count
            with self.subTest(count=count), self.assertRaises(guard.Refusal):
                self.check()

    def test_wrong_or_incomplete_job(self):
        for key, value in [('head_sha', NEW), ('conclusion', 'failure'),
                           ('labels', ['windows-latest']), ('name', 'other'), ('steps', [])]:
            with self.subTest(key=key):
                jobs = copy.deepcopy(self.jobs)
                jobs[1]['jobs'][0][key] = value
                with self.assertRaises(guard.Refusal):
                    guard.validate_provenance(self.key, OLD, self.caches, self.runs, jobs, VERSION)

    def test_wrong_run(self):
        for key, value in [('head_sha', NEW), ('event', 'pull_request'),
                           ('head_branch', 'topic'), ('path', '.github/workflows/untrusted.yml'),
                           ('status', 'in_progress')]:
            with self.subTest(key=key):
                runs = copy.deepcopy(self.runs)
                runs['workflow_runs'][0][key] = value
                with self.assertRaises(guard.Refusal):
                    guard.validate_provenance(self.key, OLD, self.caches, runs, self.jobs, VERSION)

    def test_validate_exact_key_window_platform_and_missing_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            old, new = pinned_inputs(), updated(pinned_inputs())
            for path, raw in new.items():
                (root / path).write_bytes(raw)
            put(root, 'TNLean.lean', 'import QICLean\n')
            state = root / 'state.json'
            state.write_text(json.dumps({'commits': [OLD], 'baseline': OLD}))
            calls = iter([self.caches, self.runs, self.jobs[1]])
            env = {'RUNNER_OS': 'Linux', 'RUNNER_ARCH': 'X64', 'GITHUB_OUTPUT': str(root / 'out')}
            workflow = (ROOT / '.github/workflows/pr-ci.yml').read_bytes()
            with patch.dict(os.environ, env), \
                 patch.object(guard, 'config_at', side_effect=lambda _, c: new if c == 'HEAD' else old), \
                 patch.object(guard, 'file_at', return_value=workflow), \
                 patch.object(guard, 'api', side_effect=lambda _: next(calls)):
                guard.validate(root, state, self.key[:-40], self.key, VERSION)
                self.assertEqual((root / 'out').read_text(), 'key=' + self.key + '\nversion=' + VERSION + '\n')
            for platform, arch, prefix, key in [
                ('Windows', 'X64', self.key[:-40], self.key),
                ('Linux', 'ARM64', self.key[:-40], self.key),
                ('Linux', 'X64', 'tnlean-build-', self.key),
                ('Linux', 'X64', self.key[:-40], self.key + '-suffix'),
                ('Linux', 'X64', self.key[:-40], self.key[:-40] + NEW),
            ]:
                with self.subTest(platform=platform, key=key), \
                     patch.dict(os.environ, {**env, 'RUNNER_OS': platform, 'RUNNER_ARCH': arch}), \
                     patch.object(guard, 'config_at', side_effect=lambda _, c: new if c == 'HEAD' else old), \
                     self.assertRaises(guard.Refusal):
                    guard.validate(root, state, prefix, key, VERSION)
            with patch.dict(os.environ, env), \
                 patch.object(guard, 'config_at', side_effect=lambda _, c: new if c == 'HEAD' else old), \
                 patch.object(guard, 'file_at', return_value=workflow), \
                 patch.object(guard, 'api', side_effect=OSError('missing API evidence')), \
                 self.assertRaises(OSError):
                guard.validate(root, state, self.key[:-40], self.key, VERSION)

    def test_source_workflow_policy(self):
        raw = (ROOT / '.github/workflows/pr-ci.yml').read_text()
        guard.source_workflow(raw)
        for before, after in [
            ("if: success() && github.ref == 'refs/heads/main'", 'if: success()'),
            ('    .lake/packages/qiclean/.lake/build', '    .lake/packages/mathlib/.lake/build'),
            ('runs-on: ubuntu-latest', 'runs-on: windows-latest'),
        ]:
            with self.subTest(after=after), self.assertRaises(guard.Refusal):
                guard.source_workflow(raw.replace(before, after))


class CandidateTests(unittest.TestCase):
    """Exercise real validation for each candidate; only Git/API reads are faked."""
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.old, self.new = pinned_inputs(), updated(pinned_inputs())
        for path, raw in self.new.items():
            (self.root / path).write_bytes(raw)
        put(self.root, 'TNLean.lean', 'import QICLean\n')
        self.latest = 'c' * 40
        self.prefix = 'tnlean-build-' + 'e' * 64 + '-'
        self.matched = self.prefix + self.latest
        self.state = self.root / 'state.json'
        self.state.write_text(json.dumps({'commits': [self.latest, OLD], 'baseline': OLD}))
        self.workflow = (ROOT / '.github/workflows/pr-ci.yml').read_bytes()
        self.env = {'RUNNER_OS': 'Linux', 'RUNNER_ARCH': 'X64',
                    'GITHUB_OUTPUT': str(self.root / 'out')}
        self.responses = {}
        for id, commit in enumerate((self.latest, OLD), 1):
            key = self.prefix + commit
            self.responses[self.cache_path(key)] = {'total_count': 1, 'actions_caches': [
                {'key': key, 'ref': 'refs/heads/main', 'version': VERSION}]}
            self.responses[self.run_path(commit)] = {'total_count': 1, 'workflow_runs': [{
                'id': id, 'run_attempt': 1, 'head_sha': commit, 'head_branch': 'main',
                'event': 'push', 'path': '.github/workflows/pr-ci.yml',
                'status': 'in_progress' if id == 1 else 'completed',
                'conclusion': None if id == 1 else 'success'}]}
            self.responses[f'actions/runs/{id}/jobs?per_page=100'] = {
                'total_count': 1, 'jobs': [{'id': id + 10, 'run_id': id, 'run_attempt': 1,
                    'name': 'build', 'status': 'completed', 'conclusion': 'success',
                    'head_sha': commit, 'labels': ['ubuntu-latest'], 'steps': [{
                        'name': 'Save Lean build cache (main only)', 'status': 'completed',
                        'conclusion': 'success'}]}]}
        self.stack = contextlib.ExitStack()
        self.addCleanup(self.stack.close)
        self.stack.enter_context(patch.dict(os.environ, self.env))
        self.config = self.stack.enter_context(patch.object(
            guard, 'config_at', side_effect=lambda _, c: self.new if c == 'HEAD' else self.old))
        self.source = self.stack.enter_context(patch.object(guard, 'file_at', return_value=self.workflow))
        self.api = self.stack.enter_context(patch.object(
            guard, 'api', side_effect=lambda path: copy.deepcopy(self.responses[path])))
        self.stderr = io.StringIO()
        self.stack.enter_context(contextlib.redirect_stderr(self.stderr))
        self.stack.enter_context(contextlib.redirect_stdout(io.StringIO()))

    def cache_path(self, key):
        return 'actions/caches?' + guard.urllib.parse.urlencode({'key': key, 'per_page': 100})

    def run_path(self, commit):
        return 'actions/workflows/pr-ci.yml/runs?' + guard.urllib.parse.urlencode(
            {'head_sha': commit, 'event': 'push', 'per_page': 20})

    def select(self):
        guard.select(self.root, self.state, self.prefix, self.matched)

    def assert_no_selection(self):
        with self.assertRaises(guard.Refusal):
            self.select()
        self.assertFalse((self.root / 'out').exists())

    def test_newest_incomplete_older_valid_fallback(self):
        self.select()
        self.assertEqual((self.root / 'out').read_text(),
                         f'key={self.prefix + OLD}\nversion={VERSION}\n')
        # Only full candidate keys are queried, without hiding branch shadows.
        keys = [guard.urllib.parse.parse_qs(call.args[0].split('?', 1)[1])
                for call in self.api.call_args_list if call.args[0].startswith('actions/caches?')]
        self.assertEqual(keys, [{'key': [k], 'per_page': ['100']}
                              for k in (self.matched, self.matched, self.prefix + OLD)])
        line = next(line for line in self.stderr.getvalue().splitlines()
                    if line.startswith('Compatible cache run/job evidence: '))
        evidence = json.loads(line.split(': ', 1)[1])
        run = evidence['runs'][0]
        self.assertEqual((run['id'], run['run_attempt'], run['status']), (1, 1, 'in_progress'))
        self.assertEqual(run['build_jobs'][0]['saves'][0]['conclusion'], 'success')
        self.assertEqual(run['build_jobs'][0]['labels'], ['ubuntu-latest'])

    def test_valid_lookup_match_needs_no_older_candidate(self):
        self.responses[self.run_path(self.latest)]['workflow_runs'][0]['status'] = 'completed'
        self.select()
        self.assertEqual((self.root / 'out').read_text(),
                         f'key={self.matched}\nversion={VERSION}\n')
        self.assertNotIn(self.cache_path(self.prefix + OLD), [c.args[0] for c in self.api.call_args_list])

    def test_lookup_match_outside_frozen_window_refuses(self):
        self.state.write_text(json.dumps({'commits': [OLD], 'baseline': OLD}))
        self.assert_no_selection()
        self.api.assert_not_called()

    def test_no_completed_candidate_emits_no_key(self):
        self.responses[self.run_path(OLD)]['workflow_runs'][0]['status'] = 'in_progress'
        self.assert_no_selection()
        self.assertIn('no successful main build/save', self.stderr.getvalue())

    def test_candidate_cache_scope_version_key_missing_and_ambiguity(self):
        original = copy.deepcopy(self.responses[self.cache_path(self.prefix + OLD)])
        changes = {
            'wrong_scope': lambda c: c['actions_caches'][0].update(ref='refs/pull/1/merge'),
            'wrong_version': lambda c: c['actions_caches'][0].update(version='d' * 64),
            'missing_version': lambda c: c['actions_caches'][0].pop('version'),
            'malformed_version': lambda c: c['actions_caches'][0].update(version='x\ninjected=true'),
            'prefix_suffix': lambda c: c['actions_caches'][0].update(key=self.prefix + OLD + '-extra'),
            'missing': lambda c: c.update(total_count=0, actions_caches=[]),
            'ambiguous_scope_or_version': lambda c: c.update(total_count=2),
            'truncated': lambda c: c.update(total_count=101),
        }
        for label, change in changes.items():
            with self.subTest(label=label):
                entry = copy.deepcopy(original)
                change(entry)
                self.responses[self.cache_path(self.prefix + OLD)] = entry
                self.api.reset_mock()
                self.assert_no_selection()
                self.assertNotIn(self.run_path(OLD), [c.args[0] for c in self.api.call_args_list])

    def test_untrusted_lookup_anchor_cannot_supply_a_version(self):
        self.responses[self.cache_path(self.matched)]['total_count'] = 2
        self.assert_no_selection()
        self.api.assert_called_once_with(self.cache_path(self.matched))

    def test_wrong_current_platform(self):
        for platform, arch in [('Windows', 'X64'), ('Linux', 'ARM64')]:
            with self.subTest(platform=platform), patch.dict(
                    os.environ, {'RUNNER_OS': platform, 'RUNNER_ARCH': arch}):
                self.assert_no_selection()

    def test_wrong_candidate_inputs(self):
        changed = {**self.old, 'lean-toolchain': b'wrong toolchain'}
        # Baseline is the newer commit; older candidate must match it byte for byte.
        self.state.write_text(json.dumps({'commits': [self.latest, OLD], 'baseline': self.latest}))
        self.config.side_effect = lambda _, c: self.new if c == 'HEAD' else changed if c == OLD else self.old
        self.assert_no_selection()
        self.assertIn('inputs differ from verified baseline bytes', self.stderr.getvalue())

    def test_wrong_candidate_source_workflow(self):
        self.source.side_effect = lambda _, c, p: self.workflow.replace(
            b'runs-on: ubuntu-latest', b'runs-on: windows-latest') if c == OLD else self.workflow
        self.assert_no_selection()
        self.assertIn('source runner platform differs', self.stderr.getvalue())

    def test_wrong_candidate_run_and_build_or_save(self):
        path = 'actions/runs/2/jobs?per_page=100'
        original = copy.deepcopy(self.responses[path])
        changes = {
            'wrong_job_source': lambda j: j.update(head_sha=NEW),
            'wrong_job_runner': lambda j: j.update(labels=['windows-latest']),
            'unsuccessful_build': lambda j: j.update(conclusion='failure'),
            'missing_save': lambda j: j.update(steps=[]),
            'unsuccessful_save': lambda j: j['steps'][0].update(conclusion='failure'),
        }
        for label, change in changes.items():
            with self.subTest(label=label):
                self.responses[path] = copy.deepcopy(original)
                change(self.responses[path]['jobs'][0])
                self.assert_no_selection()
        self.responses[path] = original
        self.responses[self.run_path(OLD)]['workflow_runs'][0]['head_branch'] = 'topic'
        self.assert_no_selection()

    def test_only_frozen_window_is_searched_without_retries(self):
        commits = [self.latest, *[f'{i:040x}' for i in range(guard.WINDOW)]]
        self.state.write_text(json.dumps({'commits': commits, 'baseline': self.latest}))
        with patch.object(guard, 'validate', side_effect=guard.Refusal('fixture refusal')) as validate:
            self.assert_no_selection()
        self.assertEqual([c.args[3] for c in validate.call_args_list],
                         [self.prefix + c for c in commits[:guard.WINDOW]])

    def test_api_error_does_not_retry_or_emit_key(self):
        self.api.side_effect = OSError('API unavailable')
        with self.assertRaises(OSError):
            self.select()
        self.assertFalse((self.root / 'out').exists())
        self.assertEqual(self.api.call_count, 1)

    def test_postrestore_metadata_change_refuses_without_fallback_or_pruning(self):
        self.select()
        (self.root / 'out').unlink()
        self.responses[self.run_path(OLD)]['workflow_runs'][0]['status'] = 'in_progress'
        with patch.object(guard, 'select') as select, patch.object(guard, 'discard_unvalidated') as prune, \
                patch('sys.argv', ['ci_compatible_cache.py', 'validate', '--root', str(self.root),
                      '--state', str(self.state), '--prefix', self.prefix,
                      '--matched', self.prefix + OLD, '--version', VERSION]):
            self.assertEqual(guard.main(), 1)
            select.assert_not_called()
            prune.assert_not_called()
        self.assertFalse((self.root / 'out').exists())
        self.assertIn('"status": "in_progress"', self.stderr.getvalue())

    def test_postrestore_archive_version_change_refuses(self):
        self.select()
        (self.root / 'out').unlink()
        self.responses[self.cache_path(self.prefix + OLD)]['actions_caches'][0]['version'] = 'd' * 64
        with self.assertRaisesRegex(guard.Refusal, 'archive version differs'):
            guard.validate(self.root, self.state, self.prefix, self.prefix + OLD, VERSION)
        self.assertFalse((self.root / 'out').exists())


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        self.raw = (ROOT / '.github/workflows/pr-ci.yml').read_text()
        self.workflow = yaml.safe_load(self.raw)
        self.steps = self.workflow['jobs']['build']['steps']
        self.ids = {s['id']: s for s in self.steps if 'id' in s}

    def test_main_cache_producer_survives_superseding_pushes(self):
        # Share one ref-scoped group and the default single pending slot.
        # Main (including dispatch) must finish; PR refs still cancel stale runs.
        self.assertEqual(self.workflow['concurrency'], {
            'group': '${{ github.workflow }}-${{ github.ref }}',
            'cancel-in-progress': "${{ github.ref != 'refs/heads/main' }}",
        })
        self.assertNotIn('concurrency', self.workflow['jobs']['build'])

    def test_cache_policy_regressions_run_for_workflow_changes(self):
        job = self.workflow['jobs']['file-length']
        self.assertIn("needs.changes.outputs.workflow == 'true'", job['if'])
        step = next(s for s in job['steps']
                    if s.get('name') == 'Test compatible CI cache guards')
        self.assertNotIn('if', step)
        self.assertNotIn('continue-on-error', step)
        self.assertIn('python3 scripts/test_ci_compatible_cache.py', step['run'])

    def test_exact_keys_paths_and_main_only_saving_unchanged(self):
        self.assertEqual(tuple(self.workflow['env']['BUILD_CACHE_PATHS'].split()), guard.PATHS)
        self.assertEqual(self.ids['build-cache']['with']['key'], guard.KEY)
        self.assertEqual(self.ids['build-cache']['with']['restore-keys'].strip(), guard.KEY.rsplit('-', 1)[0] + '-')
        guard.source_workflow(self.raw)
        self.assertNotIn('mathlib', self.workflow['env']['BUILD_CACHE_PATHS'])

    def test_empty_matched_key_is_the_only_fallback_gate(self):
        for id in ('compatible-config', 'compatible-lookup', 'compatible-cache', 'compatible-restore'):
            condition = self.ids[id]['if']
            self.assertIn("steps.build-cache.outputs.cache-matched-key == ''", condition)
            self.assertNotIn('cache-hit', condition)
        # A prefix hit with cache-hit=false has a nonempty matched key and
        # cannot enter the fallback. A genuine empty match can.
        self.assertFalse(bool('tnlean-build-existing' == ''))
        self.assertTrue(bool('' == ''))

    def assert_actual_round_early_steps(self):
        names = [step.get('name') for step in self.steps]
        prune = names.index('Discard unvalidated cross-commit artifacts')
        build = names.index(FULL_BUILD_NAME)
        for offset, expected in enumerate(ACTUAL_ROUND_EARLY_STEPS, start=1):
            name = expected['name']
            self.assertEqual(names.count(name), 1)
            self.assertEqual(self.steps[prune + offset], expected)
            self.assertLess(prune + offset, build)
        self.assertEqual(names.count(FULL_BUILD_NAME), 1)
        self.assertEqual(self.steps[build], EXPECTED_FULL_BUILD)

    def test_lookup_then_validation_then_exact_restore_then_prune_then_build(self):
        self.assert_actual_round_early_steps()
        ids = [s.get('id') for s in self.steps]
        self.assertLess(ids.index('compatible-lookup'), ids.index('compatible-cache'))
        self.assertLess(ids.index('compatible-cache'), ids.index('compatible-restore'))
        lookup = self.ids['compatible-lookup']['with']
        self.assertIs(lookup['lookup-only'], True)
        self.assertIn("hashFiles('.ci-cache-baseline/lean-toolchain', '.ci-cache-baseline/lake-manifest.json', '.ci-cache-baseline/lakefile.toml')", lookup['restore-keys'])
        restore = self.ids['compatible-restore']
        self.assertNotIn('restore-keys', restore['with'])
        self.assertIs(restore['with']['fail-on-cache-miss'], True)
        self.assertNotIn('continue-on-error', restore)
        prune = next(i for i, s in enumerate(self.steps) if s.get('name') == 'Discard unvalidated cross-commit artifacts')
        build = next(i for i, s in enumerate(self.steps) if s.get('name') == 'Build Lean project and capture timings')
        self.assertLess(ids.index('compatible-restore'), prune)
        self.assertLess(prune, build)
        self.assertNotIn('continue-on-error', self.steps[prune])
        self.assertEqual(self.steps[prune]['if'], restore['if'])
        self.assertIn('test "$MATCHED_KEY" = "$VERIFIED_KEY"', self.steps[prune]['run'])
        self.assertIn(' select ', self.ids['compatible-cache']['run'])
        self.assertNotIn(' select ', self.steps[prune]['run'])
        self.assertIn(' validate ', self.steps[prune]['run'])
        self.assertIn('--version "$VERIFIED_VERSION"', self.steps[prune]['run'])
        self.assertEqual(self.steps[prune]['env']['VERIFIED_VERSION'],
                         '${{ steps.compatible-cache.outputs.version }}')
        self.assertLess(self.steps[prune]['run'].index(' validate '),
                        self.steps[prune]['run'].index(' prune'))
        self.assertNotIn('always()', self.steps[build].get('if', ''))
        for i, step in enumerate(self.steps):
            if any(command in step.get('run', '') for command in
                   ('lake env lean', 'lake env bash -c')):
                if step.get('name') == 'Check finite rectangular dual geometry early':
                    # One explicit early regression is safe after its complete
                    # import closure is rebuilt by Lake. No generic exemption.
                    self.assertLess(prune, i)
                    self.assertLess(i, build)
                    self.assertNotIn('continue-on-error', step)
                    run = step['run']
                    cache_guard = 'test -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean'
                    target = 'lake --fail-fast build +TNLean.PEPS.TorusDualRectangleFlux:olean'
                    self.assertLess(run.index(cache_guard), run.index(target))
                    self.assertLess(run.index(target), run.index('lake env lean'))
                    self.assertIn('+TNLean.PEPS.TorusDualWinding:olean', run)
                    self.assertIn('set -eo pipefail', run)
                    self.assertIn('-DwarningAsError=true', run)
                    self.assertIn('-DautoImplicit=false -DrelaxedAutoImplicit=false', run)
                    self.assertEqual(run.count('lake env lean'), 1)
                    checked = run.split('for source in ', 1)[1].split('; do', 1)[0]
                    self.assertEqual(checked.replace('\\', '').split(), [
                        'TNLean/PEPS/TorusDualRectangle.lean',
                        'TNLean/PEPS/TorusDualRectangleFlux.lean',
                        'TNLeanTest/TorusDualRectangle.lean',
                    ])
                    self.assertEqual(run.strip().splitlines()[-2].strip(), '"$source"')
                    self.assertEqual(run.strip().splitlines()[-1].strip(), 'done')
                    imports = (ROOT / 'TNLeanTest/TorusDualRectangle.lean').read_text().splitlines()
                    self.assertEqual([line for line in imports if line.startswith('import ')], [
                        'import TNLean.PEPS.TorusDualRectangleFlux',
                        'import TNLean.PEPS.TorusDualWinding',
                    ])
                elif step.get('name') == 'Check labelled open coefficients early':
                    self.assertLess(prune, i)
                    self.assertLess(i, build)
                    self.assertNotIn('continue-on-error', step)
                    run = step['run']
                    target = 'lake --fail-fast build +TNLean.PEPS.TorusDualOpenDeformation:olean'
                    self.assertIn('python3 scripts/check_collared_open_axioms.py', run)
                    self.assertIn('tee -a "$RUNNER_TEMP/collared-open-check.log"', run)
                    self.assertLess(run.index('test -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean'), run.index(target))
                    self.assertLess(run.index(target), run.index('lake env lean'))
                    for flag in ['set -eo pipefail', '-DwarningAsError=true',
                                 '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
                                 '-DmaxSynthPendingDepth=3', '-Dlinter.mathlibStandardSet=true']:
                        self.assertIn(flag, run)
                    checked = run.split('for source in ', 1)[1].split('; do', 1)[0]
                    self.assertEqual(checked.replace('\\', '').split(), [
                        'TNLeanTest/LabelledOpenCoefficient.lean',
                        'TNLean/PEPS/LabelledOpenCoefficient.lean',
                        'TNLean/PEPS/TorusLabelledOpenCoefficient.lean',
                        'TNLean/PEPS/TorusDualCollar.lean',
                        'TNLean/PEPS/TorusDualOpenDeformation.lean'])
                    imports = (ROOT / 'TNLeanTest/LabelledOpenCoefficient.lean').read_text().splitlines()
                    self.assertEqual([line for line in imports if line.startswith('import ')],
                                     ['import TNLean.PEPS.TorusDualOpenDeformation'])
                elif step.get('name') in ACTUAL_ROUND_STRICT_NAMES:
                    # Exact dictionaries, placement, and multiplicity are
                    # checked above; no broad name or command exemption.
                    self.assertLess(prune, i)
                    self.assertLess(i, build)
                else:
                    self.assertLess(build, i)
        setup = next(s for s in self.steps if s.get('uses') == 'leanprover/lean-action@v1')
        self.assertIs(setup['with']['build'], False)
        self.assertIs(setup['with']['use-github-cache'], False)

    def test_actual_round_early_steps_reject_weakened_commands_and_resources(self):
        original = self.steps
        focused = next(i for i, step in enumerate(original)
                       if step.get('name') == ACTUAL_ROUND_BUILD_NAME)
        replacements = {
            0: [
                ('set -eo pipefail', 'set -e'),
                ('test -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean', ':'),
                ('lake --fail-fast build', 'lake build'),
                ('+TNLean.PEPS.AreaLaw.Scan.ActualRoundTransport:olean',
                 '+TNLean.PEPS.AreaLaw.Scan.ActualTransportEstimates:olean'),
                ('+TNLean.PEPS.AreaLaw.Scan.FillTransportEndpoints:olean', ''),
                ('2>&1', ''), ('tee -a', 'tee'),
                ('lake-build.log', 'early-build.log'),
            ],
            1: [
                ('LEAN_NUM_THREADS=1', 'LEAN_NUM_THREADS=2'),
                ('--signal=INT', '--signal=TERM'), ('--kill-after=5s', '--kill-after=10s'),
                ('90s', '180s'), ('-j1', '-j2'), ('-DautoImplicit=false', ''),
                ('-DrelaxedAutoImplicit=false', ''), ('-Dpp.unicode.fun=true', ''),
                ('-DmaxSynthPendingDepth=3', ''), ('-Dlinter.mathlibStandardSet=true', ''),
                ('-DwarningAsError=true', ''),
            ],
            2: [
                ('set -eo pipefail', 'set +e'),
                ('TNLeanTest/ActualRoundTransport.lean', ''),
                ('TNLeanTest/ActualRoundTransportAxioms.lean', ''),
                ('-DwarningAsError=true', ''), ('90s', '180s'),
            ],
        }
        try:
            for offset, changes in replacements.items():
                for before, after in changes:
                    with self.subTest(offset=offset, removed=before):
                        self.steps = copy.deepcopy(original)
                        step = self.steps[focused + offset]
                        self.assertIn(before, step['run'])
                        step['run'] = step['run'].replace(before, after)
                        with self.assertRaises(AssertionError):
                            self.assert_actual_round_early_steps()
            for offset in range(3):
                for key, value in [('if', 'always()'), ('continue-on-error', True),
                                   ('timeout-minutes', 30), ('env', {'LEAN_NUM_THREADS': '2'})]:
                    with self.subTest(offset=offset, key=key):
                        self.steps = copy.deepcopy(original)
                        self.steps[focused + offset][key] = value
                        with self.assertRaises(AssertionError):
                            self.assert_actual_round_early_steps()
        finally:
            self.steps = original

    def test_actual_round_early_steps_reject_reordering_duplicates_and_unnamed_checks(self):
        original = self.steps
        focused = next(i for i, step in enumerate(original)
                       if step.get('name') == ACTUAL_ROUND_BUILD_NAME)
        try:
            for offset in range(3):
                with self.subTest(duplicate=offset):
                    self.steps = copy.deepcopy(original)
                    self.steps.append(copy.deepcopy(self.steps[focused + offset]))
                    with self.assertRaises(AssertionError):
                        self.assert_actual_round_early_steps()
            self.steps = copy.deepcopy(original)
            self.steps[focused], self.steps[focused + 1] = (
                self.steps[focused + 1], self.steps[focused])
            with self.assertRaises(AssertionError):
                self.assert_actual_round_early_steps()
            for command in ('lake env lean Unchecked.lean',
                            "lake env bash -c 'exec lean Unchecked.lean'"):
                with self.subTest(command=command):
                    self.steps = copy.deepcopy(original)
                    self.steps.insert(focused + 3, {'name': 'Unchecked early source', 'run': command})
                    with self.assertRaises(AssertionError):
                        self.test_lookup_then_validation_then_exact_restore_then_prune_then_build()
        finally:
            self.steps = original

    def test_actual_round_prerequisites_cover_every_strict_source_import(self):
        def imports(module):
            source = (ROOT / (module.replace('.', '/') + '.lean')).read_text()
            uncommented, error = strip_lean_comments(source)
            self.assertIsNone(error)
            return re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(\S+)',
                              uncommented, re.MULTILINE)

        target_names = [target.removeprefix('+').removesuffix(':olean')
                        for target in ACTUAL_ROUND_EARLY_STEPS[0]['run'].split()
                        if target.startswith('+TNLean.')]
        self.assertEqual(target_names, [
            'TNLean.PEPS.AreaLaw.Scan.ActualRoundTransport',
            'TNLean.PEPS.AreaLaw.Scan.FillTransportEndpoints',
        ])
        pending, closure, dependencies = list(target_names), set(), set()
        while pending:
            module = pending.pop()
            if module in closure:
                continue
            closure.add(module)
            for dependency in imports(module):
                dependencies.add(dependency)
                if dependency.startswith('TNLean.'):
                    pending.append(dependency)
        for module in ('TNLean.PEPS.AreaLaw.Scan.ActualRoundTransport',
                       'TNLeanTest.ActualRoundTransport', 'TNLeanTest.ActualRoundTransportAxioms'):
            with self.subTest(module=module):
                self.assertTrue(set(imports(module)) <= closure | dependencies)
        # These two fixtures are checked directly without an output overlay:
        # neither may acquire a TNLeanTest import unavailable to that command.
        for fixture in ('TNLeanTest.ActualRoundTransport', 'TNLeanTest.ActualRoundTransportAxioms'):
            self.assertFalse(any(module.startswith('TNLeanTest.') for module in imports(fixture)))

    def test_actual_round_timing_uses_shared_append_only_log_and_final_collector(self):
        self.assert_actual_round_early_steps()
        for step in self.steps:
            for line in step.get('run', '').splitlines():
                if 'lake-build.log' in line:
                    self.assertTrue('tee -a "$RUNNER_TEMP/lake-build.log"' in line
                                    or line.strip() == '"$RUNNER_TEMP/lake-build.log" \\', line)
        timing = next(step for step in self.steps
                      if step.get('name') == 'Check changed Lean compilation times')
        self.assertIn('python3 scripts/lake_build_hotspots.py \\\n'
                      '    "$RUNNER_TEMP/lake-build.log" \\', timing['run'])
        self.assertIn('50) result=limit ;;', timing['run'])
        self.assertNotIn('--error-threshold', timing['run'])
        gate = self.workflow['jobs']['compile-time']
        self.assertEqual(gate['needs'], ['changes', 'build'])
        enforce = gate['steps'][0]
        self.assertNotIn('continue-on-error', enforce)
        self.assertEqual(enforce['env']['TIMING_RESULT'],
                         '${{ needs.build.outputs.compilation-time-result }}')
        self.assertIn('limit)\n    echo "::error::A changed Lean module reached the '
                      '50-second compilation limit"\n    exit 1', enforce['run'])

    def test_postrestore_shell_stops_before_prune_or_build(self):
        step = next(s for s in self.steps if s.get('name') == 'Discard unvalidated cross-commit artifacts')
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            # No Lean or cache mutation: a failed validator stand-in records
            # whether the workflow shell erroneously continues to pruning.
            python = root / 'python3'
            python.write_text('#!/bin/sh\nprintf "%s\\n" "$2" >> "$CALLS"\nexit 1\n')
            python.chmod(0o755)
            env = {**os.environ, 'PATH': f'{root}:' + os.environ['PATH'],
                   'CALLS': str(root / 'calls'), 'MATCHED_KEY': 'exact',
                   'VERIFIED_KEY': 'exact', 'PRIMARY_KEY': 'exact',
                   'PREFIX': 'unused', 'VERIFIED_VERSION': VERSION, 'RUNNER_TEMP': tmp}
            result = subprocess.run(['bash', '-e', '-o', 'pipefail', '-c',
                                     step['run'] + '\nprintf "build\\n" >> "$CALLS"\n'],
                                    env=env, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual((root / 'calls').read_text(), 'validate\n')

    def test_failure_to_establish_evidence_skips_fallback(self):
        for id in ('compatible-config', 'compatible-lookup', 'compatible-cache'):
            self.assertIs(self.ids[id]['continue-on-error'], True)
        self.assertIn("steps.compatible-cache.outputs.key != ''", self.ids['compatible-restore']['if'])
        self.assertIn('cache-primary-key', self.raw)
        self.assertIn('cache-matched-key', self.raw)


class PruningTests(unittest.TestCase):
    def test_removed_unreachable_aggregator_and_root_artifacts_are_discarded(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for p, b in pinned_inputs().items():
                (root / p).write_bytes(b)
            put(root, 'TNLean.lean', 'import TNLean.QICLeanInterface\n')
            put(root, 'TNLean/QICLeanInterface.lean', 'import QICLean\n')
            put(root, '.lake/build/lib/lean/DeletedRoot.olean', 'stale')
            manifest = json.loads((root / 'lake-manifest.json').read_bytes())
            for package in ('Gametheory', 'checkdecls', 'qiclean'):
                directory = root / '.lake/packages' / package
                directory.mkdir(parents=True)
                guard.git(directory, 'init', '-q')
                put(directory, 'Existing.lean', 'def existing := 1\n')
                if package == 'qiclean':
                    put(directory, 'QICLean.lean', 'import Existing\n')
                    put(directory, 'Unreachable.lean', 'import QICLean\ndef stale := 1\n')
                rev = commit(directory)
                next(p for p in manifest['packages'] if p['name'] == package)['rev'] = rev
                for path in ('lib/lean/Existing.olean', 'lib/lean/Existing.olean.hash',
                             'lib/lean/Existing.trace', 'lib/lean/Removed.olean',
                             'lib/lean/Removed.olean.private', 'ir/Removed.c', 'bin/stale',
                             'lib/lean/QICLean.olean', 'lib/lean/Unreachable.olean'):
                    put(directory, '.lake/build/' + path, 'cached')
            (root / 'lake-manifest.json').write_text(json.dumps(manifest))
            guard.discard_unvalidated(root)
            self.assertFalse((root / '.lake/build').exists())
            for package in ('Gametheory', 'checkdecls', 'qiclean'):
                build = root / '.lake/packages' / package / '.lake/build'
                self.assertTrue((build / 'lib/lean/Existing.olean').exists())
                self.assertEqual((build / 'lib/lean/Existing.trace').read_text(), 'cached')
                self.assertEqual((build / 'lib/lean/Existing.olean.hash').read_text(), 'cached')
                self.assertFalse((build / 'lib/lean/Removed.olean').exists())
                self.assertFalse((build / 'lib/lean/Removed.olean.private').exists())
                self.assertFalse((build / 'ir/Removed.c').exists())
                self.assertFalse((build / 'bin/stale').exists())
                self.assertFalse((build / 'lib/lean/QICLean.olean').exists())
                self.assertFalse((build / 'lib/lean/Unreachable.olean').exists())

    def test_missing_qic_root_build_refuses(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            put(root, 'lakefile.toml', 'defaultTargets = ["TNLean"]\n')
            put(root, 'TNLean.lean', 'import TNLean.Other\n')
            with self.assertRaises(guard.Refusal):
                guard.require_qic_build(root)


if __name__ == '__main__':
    unittest.main()
