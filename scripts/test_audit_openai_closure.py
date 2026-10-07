"""Regression tests for source closure and the cache-first audit gate."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from audit_openai_closure import blob, closure, imports, mask
from prepare_openai_baseline import prepare
from run_openai_build_audit import run_audit


class ClosureTests(unittest.TestCase):
    def test_nested_comments_strings_and_lines(self):
        source = '/- import OAI.Bad /- nested -/ -/\nimport OAI.Real -- import OAI.No\n' + '\ndef text := "import OAI.String \\" sorry"\n'
        self.assertEqual(imports(source), ['OAI.Real'])
        self.assertEqual(mask(source).count('\n'), source.count('\n'))
        self.assertNotIn('sorry', mask(source))

    def test_multiple_imports_and_modifiers(self):
        self.assertEqual(imports('public import OAI.A OAI.B\nmeta import Mathlib\n'),
                         ['Mathlib', 'OAI.A', 'OAI.B'])

    def test_unterminated_comment_rejected(self):
        with self.assertRaises(ValueError): mask('/- nested /- -/')

    def test_unsupported_import_rejected(self):
        with self.assertRaises(ValueError): imports('import OAI.A; #eval 1\n')

    def test_diamond_is_deduplicated_and_dependency_first(self):
        sources = {'OAI.A': 'import OAI.B OAI.C', 'OAI.B': 'import OAI.D',
                   'OAI.C': 'import OAI.D', 'OAI.D': 'import Mathlib',
                   'OAI.Unrelated': 'import Bad'}
        rows, order = closure(['OAI.A'], sources.__getitem__)
        self.assertEqual(order, ['OAI.D', 'OAI.B', 'OAI.C', 'OAI.A'])
        self.assertEqual(len(rows), 4)

    def test_missing_local_dependency_rejected(self):
        with self.assertRaises(KeyError):
            closure(['OAI.A'], {'OAI.A': 'import OAI.Missing'}.__getitem__)

    def test_cycle_rejected(self):
        with self.assertRaisesRegex(ValueError, 'cycle'):
            closure(['OAI.A'], {'OAI.A': 'import OAI.B', 'OAI.B': 'import OAI.A'}.__getitem__)

    def test_git_reads_immutable_object(self):
        with patch('audit_openai_closure.git', return_value=b'import Mathlib') as git:
            self.assertEqual(blob(Path('/repo'), 'abc', 'lean/A.lean'), b'import Mathlib')
            git.assert_called_once_with(Path('/repo'), 'show', 'abc:lean/A.lean')

    def test_harness_rejects_production_destination(self):
        with self.assertRaisesRegex(ValueError, 'outside'):
            prepare(Path('/up'), Path('/repo'), Path('/repo/vendor'), Path('/lock'))


class CacheGateTests(unittest.TestCase):
    def exercise(self, cache_exit=0, sentinel=True, build_exit=0):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        root = Path(temp.name)
        (root/'lean-toolchain').write_text('test')
        (root/'lake-manifest.json').write_text('{}')
        lake = root/'lake'
        lake.write_text('#!/bin/sh\ncase "$1" in\nexe) exit ' + str(cache_exit) +
                        ';;\nbuild) exit ' + str(build_exit) + ';;\n*) exit 0;;\nesac\n')
        lake.chmod(0o755)
        if sentinel:
            target = root/'.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean'
            target.parent.mkdir(parents=True); target.touch()
        return run_audit(root, lake, root/'logs', ['OAI.Root'], 5, 'Audit.lean')

    def test_failed_cache_never_builds_even_with_stale_sentinel(self):
        result = self.exercise(cache_exit=1)
        self.assertEqual(result['cache_gate'], 'failed_cache_command')
        self.assertEqual(len(result['attempts']), 2)

    def test_successful_command_without_sentinel_never_builds(self):
        result = self.exercise(sentinel=False)
        self.assertEqual(result['cache_gate'], 'missing_Mathlib.olean')
        self.assertEqual(result['library_build_status'], 'not_attempted')

    def test_successful_gate_builds_then_prints_axioms(self):
        result = self.exercise()
        self.assertEqual(result['library_build_status'], 'passed')
        self.assertEqual(result['axiom_status'], 'command_passed_requires_review')
        self.assertEqual([a['command'][1] for a in result['attempts']],
                         ['--version', 'exe', 'build', 'env'])

    def test_failed_build_never_prints_axioms(self):
        result = self.exercise(build_exit=1)
        self.assertEqual(result['library_build_status'], 'failed')
        self.assertEqual(result['axiom_status'], 'not_attempted')

class CommittedManifestTests(unittest.TestCase):
    def test_graph_and_root_signatures(self):
        import hashlib
        path = Path(__file__).resolve().parents[1]/'docs/provenance/openai-math-port-manifest.json'
        manifest = json.loads(path.read_text())
        rows = manifest['modules']
        self.assertEqual(len(rows), manifest['module_count'])
        self.assertEqual(sum(row['lines'] for row in rows), manifest['source_lines'])
        by_name = {row['module']: row for row in rows}
        positions = {row['module']: i for i, row in enumerate(rows)}
        for row in rows:
            for dep in row['imports']:
                if dep.startswith('OAI.'):
                    self.assertLess(positions[dep], positions[row['module']])
        for root in manifest['roots']:
            sources = {name: '\n'.join('import '+dep for dep in row['imports'])
                       for name, row in by_name.items()}
            found, order = closure([root['module']], sources.__getitem__)
            self.assertEqual(order, root['topological_order'])
            self.assertEqual(len(found), root['module_count'])
            self.assertEqual(hashlib.sha256(root['signature'].encode()).hexdigest(), root['signature_sha256'])


class BuildEvidenceTests(unittest.TestCase):
    def test_retained_logs_match_hashes_and_failed_gates(self):
        import gzip
        import hashlib
        repo = Path(__file__).resolve().parents[1]
        evidence = json.loads((repo/'docs/provenance/openai-math-build-audit.json').read_text())
        for run in evidence['runs']:
            self.assertEqual(run['library_build_status'], 'not_attempted')
            self.assertEqual(run['axiom_status'], 'not_attempted')
            self.assertNotEqual(run['cache_gate'], 'passed')
            for attempt in run['attempts']:
                data = gzip.decompress((repo/attempt['compressed_log']).read_bytes())
                self.assertEqual(hashlib.sha256(data).hexdigest(), attempt['log_sha256'])
                self.assertNotIn('build', attempt['command'])
        for probe in evidence['access_probes']:
            data = (repo/probe['log']).read_bytes()
            self.assertEqual(hashlib.sha256(data).hexdigest(), probe['log_sha256'])


if __name__ == '__main__': unittest.main()
