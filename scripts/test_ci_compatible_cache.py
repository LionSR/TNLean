#!/usr/bin/env python3
"""Configuration, provenance, pruning, and workflow guards; never invokes Lean."""
from __future__ import annotations

import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import yaml

import ci_compatible_cache as guard

ROOT = Path(__file__).resolve().parents[1]
OLD = 'a' * 40
NEW = 'b' * 40


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
    guard.git(repo, '-c', 'user.name=Cache Guard Test', '-c', 'user.email=cache-test@example.invalid',
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


class ProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.key = 'tnlean-build-' + 'e' * 64 + '-' + OLD
        self.caches = {'total_count': 1, 'actions_caches': [
            {'key': self.key, 'ref': 'refs/heads/main'}]}
        self.runs = {'workflow_runs': [{'id': 1, 'head_sha': OLD, 'head_branch': 'main',
                     'event': 'push', 'status': 'completed', 'path': '.github/workflows/pr-ci.yml'}]}
        self.jobs = {1: {'jobs': [{'name': 'build', 'conclusion': 'success', 'head_sha': OLD,
                                'labels': ['ubuntu-latest'], 'steps': [
                                    {'name': 'Save Lean build cache (main only)', 'conclusion': 'success'}]}]}}

    def check(self):
        guard.validate_provenance(self.key, OLD, self.caches, self.runs, self.jobs)

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
                    guard.validate_provenance(self.key, OLD, self.caches, self.runs, jobs)

    def test_wrong_run(self):
        for key, value in [('head_sha', NEW), ('event', 'pull_request'),
                           ('head_branch', 'topic'), ('path', '.github/workflows/untrusted.yml'),
                           ('status', 'in_progress')]:
            with self.subTest(key=key):
                runs = copy.deepcopy(self.runs)
                runs['workflow_runs'][0][key] = value
                with self.assertRaises(guard.Refusal):
                    guard.validate_provenance(self.key, OLD, self.caches, runs, self.jobs)

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
                guard.validate(root, state, self.key[:-40], self.key)
                self.assertEqual((root / 'out').read_text(), 'key=' + self.key + '\n')
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
                    guard.validate(root, state, prefix, key)
            with patch.dict(os.environ, env), \
                 patch.object(guard, 'config_at', side_effect=lambda _, c: new if c == 'HEAD' else old), \
                 patch.object(guard, 'file_at', return_value=workflow), \
                 patch.object(guard, 'api', side_effect=OSError('missing API evidence')), \
                 self.assertRaises(OSError):
                guard.validate(root, state, self.key[:-40], self.key)

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


class WorkflowTests(unittest.TestCase):
    def setUp(self):
        self.raw = (ROOT / '.github/workflows/pr-ci.yml').read_text()
        self.workflow = yaml.safe_load(self.raw)
        self.steps = self.workflow['jobs']['build']['steps']
        self.ids = {s['id']: s for s in self.steps if 'id' in s}

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

    def test_lookup_then_validation_then_exact_restore_then_prune_then_build(self):
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
        self.assertIn(' validate ', self.steps[prune]['run'])
        for i, step in enumerate(self.steps):
            if 'lake env lean' in step.get('run', ''):
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
                    target = 'lake --fail-fast build +TNLean.PEPS.LabelledOpenCoefficient:olean'
                    self.assertLess(run.index('test -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean'), run.index(target))
                    self.assertLess(run.index(target), run.index('lake env lean'))
                    for flag in ['set -eo pipefail', '-DwarningAsError=true',
                                 '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
                                 '-DmaxSynthPendingDepth=3', '-Dlinter.mathlibStandardSet=true']:
                        self.assertIn(flag, run)
                    checked = run.split('for source in ', 1)[1].split('; do', 1)[0]
                    self.assertEqual(checked.replace('\\', '').split(), [
                        'TNLean/PEPS/LabelledOpenCoefficient.lean',
                        'TNLeanTest/LabelledOpenCoefficient.lean'])
                    imports = (ROOT / 'TNLeanTest/LabelledOpenCoefficient.lean').read_text().splitlines()
                    self.assertEqual([line for line in imports if line.startswith('import ')],
                                     ['import TNLean.PEPS.LabelledOpenCoefficient'])
                else:
                    self.assertLess(build, i)
        setup = next(s for s in self.steps if s.get('uses') == 'leanprover/lean-action@v1')
        self.assertIs(setup['with']['build'], False)
        self.assertIs(setup['with']['use-github-cache'], False)

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
