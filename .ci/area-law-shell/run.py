"""Elaborate one frozen shell proof without creating Lean output artifacts.

An unfinished goal remains an actual nonzero Lean result. This diagnostic is
separate from the production build and does not establish theorem completion.
"""

from pathlib import Path
import hashlib
import json
import os
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / '.ci/area-law-shell/Input.lean'
SOURCE_SHA = '9ce7ba58252dd68000cc8454bd141b1cb9576a1fa2d73f7ad0dea18c3a7452bf'
MATHLIB = 'c55e6e786f49471c72fbddbec5415808896aec1e'
TOOLCHAIN = 'leanprover/lean4:v4.35.0-rc3'
SOURCE_BASE = 'dd2e900d25464445c125b94d7a78fac6b2dd8d6e'
CONTROLS = {
    'lakefile.toml': '95504db1cb367757949e8ab1abc856f8eb587ab9f0d8eeb23f451c41bf3df0c4',
    'lake-manifest.json': '3847f6407b4e2bfeede30601c429b82dc82078e144d0f39c1cc2046b72df7a12',
}
IMPORTS = [
    'Mathlib.Data.Int.Interval',
    'Mathlib.Data.Finset.Lattice.Fold',
    'Mathlib.Algebra.Order.Group.Abs',
    'Mathlib.Algebra.Order.Group.Int',
    'Mathlib.Data.Finset.Prod',
    'Lean.Elab.Tactic.Omega',
]
OPTIONS = [
    '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
    '-Dpp.unicode.fun=true', '-DmaxSynthPendingDepth=3',
    '-Dlinter.mathlibStandardSet=true', '-DwarningAsError=true',
]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def output(command):
    return subprocess.check_output(command, text=True, timeout=10).strip()


def signal_group(process, sig):
    try:
        os.killpg(process.pid, sig)
    except ProcessLookupError:
        pass


def group_present(process):
    try:
        os.killpg(process.pid, 0)
    except ProcessLookupError:
        return False
    return True


def close_owned_group(process, deadline):
    cleanup_deadline = min(time.monotonic() + 4.5, deadline - 0.5)
    if group_present(process):
        signal_group(process, signal.SIGTERM)
        term_deadline = min(time.monotonic() + 1.5, cleanup_deadline)
        while group_present(process) and time.monotonic() < term_deadline:
            process.poll()
            time.sleep(0.05)
        if group_present(process):
            signal_group(process, signal.SIGKILL)
    while group_present(process) and time.monotonic() < cleanup_deadline:
        process.poll()
        time.sleep(0.05)
    process.poll()
    return process.returncode is not None and not group_present(process)


def main():
    require(digest(SOURCE) == SOURCE_SHA, 'Frozen proof input changed')
    require((ROOT / 'lean-toolchain').read_text().strip() == TOOLCHAIN,
            'TNLean source toolchain changed')
    require(Path('lean-toolchain').read_text().strip() == TOOLCHAIN,
            'Mathlib toolchain changed')
    for path, expected in CONTROLS.items():
        require(digest(ROOT / path) == expected, f'Package control changed: {path}')
    actual_imports = [line.removeprefix('import ') for line in SOURCE.read_text().splitlines()
                      if line.startswith('import ')]
    require(actual_imports == IMPORTS, 'Direct imports changed')
    package = Path.cwd()
    require(output(['git', '-C', str(package), 'rev-parse', 'HEAD']) == MATHLIB,
            'Mathlib revision changed')
    require(not output(['git', '-C', str(package), 'status', '--porcelain',
                        '--untracked-files=no']), 'Mathlib source is dirty')
    library = package / '.lake/build/lib/lean'
    for module in IMPORTS[:-1]:
        require((library / (module.replace('.', '/') + '.olean')).is_file(),
                f'Prebuilt direct import is missing: {module}')
    lean = Path(output(['elan', 'which', 'lean']))
    require(lean.is_file(), 'Pinned Lean executable is missing')
    require((lean.parent.parent / 'lib/lean/Lean/Elab/Tactic/Omega.olean').is_file(),
            'Prebuilt core direct import is missing')
    version = output([str(lean), '--version'])
    require('4.35.0-rc3' in version, 'Lean version changed')
    checkout = output(['git', '-C', str(ROOT), 'rev-parse', 'HEAD'])
    require(checkout == os.environ.get('GITHUB_SHA'), 'Hosted checkout differs from event SHA')
    command = [str(lean), '-j1', *OPTIONS, str(SOURCE)]
    print(json.dumps({
        'checkout': checkout, 'source_base': SOURCE_BASE,
        'workflow_sha': os.environ.get('GITHUB_SHA'),
        'source_sha256': SOURCE_SHA, 'mathlib_revision': MATHLIB,
        'lean_version': version, 'lean_executable_sha256': digest(lean),
        'command': command, 'thread_limit': 1, 'output_artifacts_requested': False,
        'kernel_proof_claimed': False,
    }), flush=True)
    environment = dict(os.environ, LEAN_NUM_THREADS='1')
    termination = [None]

    def mark_termination(sig, _frame):
        termination[0] = sig

    watched_signals = (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)
    old_handlers = {sig: signal.signal(sig, mark_termination) for sig in watched_signals}
    start = time.monotonic()
    deadline = start + 60
    elaboration_deadline = deadline - 5.5
    process = None
    timed_out = False
    diagnostic = ''
    owned_group_absent = False
    try:
        require(termination[0] is None, 'Termination requested before child launch')
        process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                   text=True, env=environment, start_new_session=True)
        while termination[0] is None:
            remaining = elaboration_deadline - time.monotonic()
            if remaining <= 0:
                timed_out = True
                break
            try:
                diagnostic, _ = process.communicate(timeout=min(0.5, remaining))
                break
            except subprocess.TimeoutExpired:
                pass
    finally:
        if process is not None:
            owned_group_absent = close_owned_group(process, deadline)
            if owned_group_absent:
                diagnostic, _ = process.communicate(timeout=max(0.01,
                    deadline - time.monotonic() - 0.1))
        for sig, old in old_handlers.items():
            signal.signal(sig, old)
    print('::group::Actual Lean diagnostic', flush=True)
    print(diagnostic, end='' if diagnostic.endswith('\n') else '\n', flush=True)
    print('::endgroup::', flush=True)
    print(json.dumps({
        'actual_lean_exit_code': process.returncode, 'timed_out': timed_out,
        'termination_signal': termination[0], 'owned_group_absent': owned_group_absent,
        'elapsed_seconds': time.monotonic() - start,
        'diagnostic_sha256': hashlib.sha256(diagnostic.encode()).hexdigest(),
        'kernel_proof_claimed': False,
    }), flush=True)
    if not owned_group_absent:
        return 125
    if termination[0] is not None:
        return 128 + termination[0]
    return 124 if timed_out else process.returncode


if __name__ == '__main__':
    sys.exit(main())
