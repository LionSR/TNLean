#!/usr/bin/env python3
"""Optional tiny, dependency-free Lake invalidation experiment.

Requires explicit exclusive Lean access; not part of parallel Python/CI tests.
Never reads or writes a TNLean/QICLean/Mathlib build directory.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

import ci_compatible_cache as guard

ROOT = Path(__file__).resolve().parents[1]


def write(root, path, source):
    file = root / path
    file.parent.mkdir(parents=True, exist_ok=True)
    file.write_text(source)


def run(lake, root, *args, succeeds=True):
    result = subprocess.run([str(lake), *args], cwd=root, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=90,
                            env={'PATH': f'{lake.parent}:/usr/bin:/bin', 'HOME': str(root),
                                 'LAKE_CACHE_DIR': '', 'LAKE_ARTIFACT_CACHE': 'false',
                                 'LEAN_NUM_THREADS': '1'})
    print(result.stdout, end='')
    if (result.returncode == 0) != succeeds:
        raise AssertionError(f'Unexpected exit {result.returncode}: {args}')


def olean(root, module):
    return root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')


def stamps(root):
    return {m: olean(root, 'Fixture.' + m).stat().st_mtime_ns
            for m in ('Upstream', 'Dependent', 'Independent')}


def commit(root):
    guard.git(root, 'add', '.')
    guard.git(root, '-c', 'user.name=Lake Fixture', '-c', 'user.email=fixture@example.invalid',
              'commit', '-qm', 'fixture')
    return guard.git(root, 'rev-parse', 'HEAD').decode().strip()


def experiment(lake):
    with tempfile.TemporaryDirectory(prefix='tnlean-lake-invalidation-') as temp:
        base = Path(temp)
        source, seeded = base / 'source', base / 'seeded'
        source.mkdir()
        shutil.copyfile(ROOT / 'lean-toolchain', source / 'lean-toolchain')
        write(source, 'lakefile.toml', 'name = "fixture"\nversion = "0.1.0"\n'
              'enableArtifactCache = false\ndefaultTargets = ["Fixture"]\n[[lean_lib]]\nname = "Fixture"\n')
        write(source, 'Fixture.lean', 'import Fixture.Dependent\nimport Fixture.Independent\n')
        write(source, 'Fixture/Upstream.lean', 'def upstream : Nat := 1\n')
        write(source, 'Fixture/Dependent.lean', 'import Fixture.Upstream\ndef dependent : Nat := upstream + 1\n')
        write(source, 'Fixture/Independent.lean', 'def independent : Nat := 7\n')
        # Leaf targets explicitly serialized: there is never a pair of ready
        # unbuilt independent Lean targets within one Lake invocation.
        for target in ('Fixture.Upstream', 'Fixture.Dependent', 'Fixture.Independent', 'Fixture'):
            run(lake, source, 'build', target)
        shutil.copytree(source, seeded, copy_function=shutil.copy2)
        before = stamps(seeded)
        time.sleep(0.02)
        run(lake, seeded, 'build', 'Fixture')
        assert stamps(seeded) == before, 'unchanged seeded modules were rebuilt'
        print('PASS: unchanged seed reused')

        write(seeded, 'Fixture/Upstream.lean', 'def upstream : Nat := 2\n')
        time.sleep(0.02)
        run(lake, seeded, 'build', 'Fixture.Dependent')
        run(lake, seeded, 'build', 'Fixture')
        changed = stamps(seeded)
        assert changed['Upstream'] != before['Upstream'], 'changed upstream did not rebuild'
        assert changed['Dependent'] != before['Dependent'], 'dependent did not rebuild'
        assert changed['Independent'] == before['Independent'], 'independent module did not reuse'
        print('PASS: changed upstream/dependent rebuilt; independent reused')

        trace = seeded / '.lake/build/lib/lean/Fixture/Upstream.trace'
        assert trace.is_file(), 'expected pinned Lake trace missing before experiment'
        trace.unlink()
        time.sleep(0.02)
        run(lake, seeded, 'build', 'Fixture.Dependent')
        assert stamps(seeded)['Upstream'] != changed['Upstream'], 'missing trace was incorrectly accepted'
        print('PASS: missing trace rebuilt')

        write(seeded, 'Fixture/Upstream.lean', 'def upstream : Nat := doesNotExist\n')
        run(lake, seeded, 'build', 'Fixture', succeeds=False)
        print('PASS: broken source cannot pass the mandatory full build')

        # A removed module can retain an old .olean. The additive eligibility
        # guard must refuse even though that artifact still exists.
        qic = base / 'qic'
        qic.mkdir()
        guard.git(qic, 'init', '-q')
        for path in guard.INPUTS:
            write(qic, path, 'identical fixture metadata')
        write(qic, '.gitignore', '.lake/\n')
        write(qic, 'QICLean/Removed.lean', 'def removed : Nat := 1\n')
        old = commit(qic)
        artifact = qic / '.lake/build/lib/lean/QICLean/Removed.olean'
        artifact.parent.mkdir(parents=True)
        shutil.copyfile(olean(source, 'Fixture.Upstream'), artifact)
        (qic / 'QICLean/Removed.lean').unlink()
        write(qic, 'QICLean/Added.lean', 'def added : Nat := 2\n')
        new = commit(qic)
        assert artifact.exists()
        try:
            guard.additive_qic(qic, old, new)
        except guard.Refusal:
            pass
        else:
            raise AssertionError('removed source was eligible despite surviving stale artifact')
        print('PASS: removed module refused despite surviving compiled artifact')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', type=Path, required=True, help='verified pinned Lake executable')
    parser.add_argument('--sole-lean-slot', action='store_true', required=True,
                        help='assert exclusive Lean slot has explicitly been granted')
    args = parser.parse_args()
    lake = args.lake.resolve(strict=True)
    experiment(lake)


if __name__ == '__main__':
    main()
