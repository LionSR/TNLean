#!/usr/bin/env python3
"""Prepare the physical Gaussian source contribution without changing frozen drafts."""
from pathlib import Path
import gzip
import hashlib
import importlib.util
import json
import re
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
root = Path('/Users/siruilu/Local/agentFormalization/TNLean/worktrees/peps-source-physical')
base = Path('/private/tmp/tnlean-source-physical')
base.mkdir(exist_ok=True)
manifest = json.loads(Path('/tmp/tnlean-physical-integration-root-manifest.json').read_text())
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == manifest['base']
assert not (root / '.lake').exists()
(base / 'original-sources').mkdir(exist_ok=True)
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
spec = importlib.util.spec_from_file_location('policy', root / 'scripts/check_openai_provenance.py')
policy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(policy)
preservation = []
declarations = []
replacements = {
    'import SourceCircuitLifetime': 'import TNLean.PEPS.Approximation.SourceCircuitLifetime',
    'import TNLean.PEPS.Approximation.PhysicalBlockTraceNorm': 'import QICLean.Channel.PartialTraceBlocks',
    'import TNLean.PEPS.Approximation.PhysicalBasisInvariance': 'import QICLean.Channel.PartialTraceBasisInvariance',
}
labels = {
    'SourceCircuitLifetime': 'eq:compression-choice-cost',
    'CorrectedSourcePartition': 'eq:compression-exterior-input',
    'GaussianPhysicalSource': 'eq:compression-one-choice',
    'GaussianSourceIntegrability': 'eq:compression-block-second-moment',
    'SourceGaussianMoments': 'eq:compression-product-covariance',
    'SourceGaussianPhysicalIntegrability': 'eq:compression-total-error',
    'SourceGaussianVectorDensity': 'eq:compression-product-covariance',
    'SourceGaussianBranchDensity': 'eq:compression-total-error',
    'PreparedSourceVectorDensity': 'eq:compression-exterior-contraction',
    'SourceSamplingCount': 'eq:compression-total-error',
}
for row in manifest['sources']:
    original = Path(row['source'])
    assert sha(original) == row['source_sha256']
    shutil.copy2(original, base / 'original-sources' / original.name)
    if row['already_moved_wholly_to_qic']:
        preservation.append({**row, 'action': 'Use the canonical QIC module; no TN copy created.'})
        continue
    text = original.read_text()
    source_tokens = policy.lean_parts(text)[0].split()
    if row['generic_declaration_moved_to_qic']:
        start = text.index('namespace ProbabilityTheory')
        end = text.index('end ProbabilityTheory', start) + len('end ProbabilityTheory')
        removed = text[start:end]
        text = text[:start] + text[end:]
        text = text.replace('import QICLean.Probability.WeightedSourceError',
                            'import QICLean.Probability.WeightedSourceError\nimport QICLean.Probability.MatrixTraceNormIntegrability')
        if 'import QICLean.Probability.MatrixTraceNormIntegrability' not in text:
            end_import = list(re.finditer(r'^import .+$', text, re.M))[-1].end()
            text = text[:end_import] + '\nimport QICLean.Probability.MatrixTraceNormIntegrability' + text[end_import:]
    for before, after in replacements.items():
        text = text.replace(before, after)
    if not text.startswith('/-\nCopyright'):
        text = ('/-\nCopyright (c) 2026 TNLean contributors. All rights reserved.\n'
                'Released under Apache 2.0 license as described in the file LICENSE.\n'
                'Authors: TNLean contributors\n-/\n' + text)
    private_names = set(re.findall(r'^\s*private\s+(?:theorem|lemma|def|abbrev|instance)\s+([^\s:(]+)', policy.lean_parts(text)[0], re.M))
    names = sorted(n for n in policy.declarations(text) if n.rsplit('.', 1)[-1] not in private_names)
    assert names, row['module']
    label = labels.get(row['module'], 'eq:compression-exterior-contraction')
    notice = ['/-!', 'Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,',
              label + '.',
              'Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.',
              'Independently formalized; no upstream Lean proof text reused.', '']
    relative = 'TNLean/PEPS/Approximation/' + row['module'] + '.lean'
    for i, name in enumerate(names, 1):
        identifier = '8769-physical-' + row['module'].lower() + f'-{i:02d}'
        declarations.append({'id': identifier, 'path': relative, 'declaration': name, 'paper_label': label})
        declaration_text = name if len(name) <= 100 else ('https://lionsr.github.io/TNLean/docs/' + relative[:-5] + '.html#' + name)
        notice += ['Provenance-ID: ' + identifier, 'Downstream declaration:', declaration_text, '']
    notice += ['-/', '']
    module_doc = text.index('/-!')
    module_end = text.index('-/', module_doc) + 2
    text = text[:module_end] + '\n\n' + '\n'.join(notice) + text[module_end:]
    (root / relative).write_text(text)
    # The only mathematical-token removal is the already canonical QIC theorem block.
    before = original.read_text()
    if row['generic_declaration_moved_to_qic']:
        before = before.replace(removed, '')
    strip_imports = lambda s: re.sub(r'^import .+\n', '', policy.lean_parts(s)[0], flags=re.M).split()
    assert strip_imports(before) == strip_imports(text), row['module']
    preservation.append({**row, 'path': relative, 'production_sha256': sha(root / relative),
                         'proof_tokens_preserved': True, 'public_declarations': len(names)})

old_pin = 'b2521d2a2843d824ce85a4d94bf4b60d322d6c6f'
for name, count in [('lakefile.toml', 1), ('lake-manifest.json', 2), ('docbuild/lake-manifest.json', 2)]:
    path = root / name
    text = path.read_text()
    assert text.count(old_pin) == count or text.count(manifest['qic_pin']) == count, name
    path.write_text(text.replace(old_pin, manifest['qic_pin']))
patch = '/tmp/tnlean-orthonormal-coordinate-norm-refactor.patch'
if subprocess.run(['git', 'apply', '--reverse', '--check', patch], cwd=root, capture_output=True).returncode:
    subprocess.run(['git', 'apply', patch], cwd=root, check=True)
(base / 'norm-refactor.patch.gz').write_bytes(gzip.compress(Path(manifest['norm_refactor']).read_bytes(), mtime=0))
shutil.copy2('/tmp/tnlean-physical-integration-root-manifest.json', base / 'root-manifest.json')
(base / 'source-preservation.json').write_text(json.dumps(preservation, indent=2) + '\n')
(base / 'declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
print('PREPARED', len([r for r in preservation if 'path' in r]), len(declarations), flush=True)
