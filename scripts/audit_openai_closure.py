#!/usr/bin/env python3
"""Reproduce #8741's immutable module-import audit; never a proof verifier.

Reads Git objects, not potentially edited checkout files. The comment/string
masker supports nested Lean block comments and preserves source line numbers.
Declaration rows are lexical anchors, not elaborated names or proof dependencies.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

PIN = 'adc7f1241b42e322a6451854ab7e4b4c146bf78a'
BASE = 'b7a0184ce22b29102fe17a6e96a9ba83b98d5510'
ROOTS = {
    'OAI.MathematicalPhysics.PEPSFilters.GeometricOptimizer':
        'OAI.PolynomialPEPS.PinnedEntropy.NestedFilter.Energy.geometric_optimizer_producer',
    'OAI.MathematicalPhysics.PEPSMove.PhysicalMove':
        'OAI.PolynomialPEPS.PhysicalMove.LocalMovePhysical.one_copy_move_bound',
    'OAI.MathematicalPhysics.PEPSSubvolume.Subvolume':
        'OAI.PolynomialPEPS.Subvolume.RectangleTiling.uniform_subvolume_square',
}
TOKEN = re.compile(r'\b(?:sorry|admit|axiom|native_decide|unsafeCast|unsafeCoerce)\b')
DECL = re.compile(r'^\s*(?:@\[[^\n]*?\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
                  r'(theorem|lemma|def|abbrev|structure|class|instance)\s+([^\s:({\[]+)', re.M)


def mask(text):
    """Blank comments and strings, retaining byte-independent character positions."""
    out = list(text)
    i, depth = 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i+2] = '  '; depth += 1; i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = '  '; depth -= 1; i += 2
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i+2] = '  '; depth = 1; i += 2
        elif text.startswith('--', i):
            while i < len(text) and text[i] != '\n':
                out[i] = ' '; i += 1
        elif text[i] == '"':
            out[i] = ' '; i += 1
            while i < len(text):
                c = text[i]
                if c != '\n': out[i] = ' '
                i += 1
                if c == '\\' and i < len(text):
                    if text[i] != '\n': out[i] = ' '
                    i += 1
                elif c == '"': break
            else:
                raise ValueError('unterminated string')
        else:
            i += 1
    if depth: raise ValueError('unterminated block comment')
    return ''.join(out)


def imports(text):
    clean = mask(text)
    result = []
    # Audited source uses one or more module identifiers on each import line.
    for match in re.finditer(r'^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\s+([^\n]+)', clean, re.M):
        for module in match[1].split():
            if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*(?:\.[A-Za-z_0-9]+)*', module):
                raise ValueError(f'unsupported import syntax: {module}')
            result.append(module)
    return sorted(set(result))


def closure(roots, read):
    rows, order, active = {}, [], set()
    def visit(module):
        if module in active: raise ValueError(f'import cycle: {module}')
        if module in rows: return
        active.add(module)
        source = read(module)
        deps = imports(source)
        for dep in deps:
            if dep.startswith('OAI.'): visit(dep)
        active.remove(module)
        rows[module] = (source, deps)
        order.append(module)
    for root in sorted(roots): visit(root)
    return rows, order


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args])


def blob(repo, revision, path):
    return git(repo, 'show', f'{revision}:{path}')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def source_path(module):
    return 'lean/' + module.replace('.', '/') + '.lean'


def audit(upstream, downstream):
    def read(module): return blob(upstream, PIN, source_path(module)).decode()
    rows, order = closure(ROOTS, read)
    roots = []
    for module, declaration in ROOTS.items():
        subrows, suborder = closure([module], read)
        source = rows[module][0]
        short = declaration.rsplit('.', 1)[1]
        matches = list(re.finditer(r'^theorem ' + re.escape(short) + r'\b', source, re.M))
        if len(matches) != 1: raise ValueError(f'ambiguous root: {declaration}')
        start = matches[0].start()
        end = source.index(':= by', start)
        signature = source[start:end].rstrip()
        roots.append({'module': module, 'declaration': declaration,
                      'signature': signature, 'source_url': f'https://github.com/openai/math/blob/{PIN}/{source_path(module)}#L{source.count(chr(10), 0, start)+1}', 'signature_sha256': digest(signature.encode()),
                      'source_lines': [source.count('\n', 0, start)+1, source.count('\n', 0, end)+1],
                      'module_count': len(subrows), 'topological_order': suborder,
                      'kernel_dependency_closure': 'not_verified', 'axioms': 'not_computed_by_inventory; see openai-math-ci-audit.json'})
    modules = []
    for module in order:
        source, deps = rows[module]
        path = source_path(module)
        clean = mask(source)
        anchors = [{'kind': m[1], 'unqualified_name': m[2],
                    'line': clean.count('\n', 0, m.start(1))+1} for m in DECL.finditer(clean)]
        modules.append({'module': module, 'path': path, 'sha256': digest(source.encode()),
                        'git_blob': git(upstream, 'rev-parse', f'{PIN}:{path}').decode().strip(),
                        'lines': len(source.splitlines()), 'imports': deps,
                        'lexical_declarations': anchors,
                        'selected_declarations': [ROOTS[module]] if module in ROOTS else [],
                        'decision': 'deferred_to_issue', 'issue': 8741,
                        'owner_repository': None, 'downstream_path': None,
                        'ownership_note': 'Mixed source module: classify each retained declaration as QICLean generic or TNLean physical before reuse.',
                        'source_scope': module.split('.')[2],
                        'source_token_findings': [{'token': m[0], 'line': clean.count('\n', 0, m.start())+1} for m in TOKEN.finditer(clean)],
                        'build_result': 'see openai-math-build-audit.json; not implied by inventory'})
    def configuration(repo, revision, prefix, files):
        records = {}
        for name in files:
            data = blob(repo, revision, prefix+name)
            records[name] = {'sha256': digest(data)}
            if name == 'lean-toolchain': records[name]['value'] = data.decode().strip()
            if name == 'lake-manifest.json': records[name]['packages'] = json.loads(data)['packages']
        return records
    predicate_module = 'OAI.MathematicalPhysics.PEPSMove.PhysicalMove'
    predicate_source = rows[predicate_module][0]
    predicate_start = predicate_source.index('def OneCopyMoveBound : Prop :=')
    predicate_end = predicate_source.index('\nend ', predicate_start)
    predicate_text = predicate_source[predicate_start:predicate_end].rstrip()
    licenses = {path: digest(blob(upstream, PIN, path)) for path in ['LICENSE', 'lean/LICENSE']}
    return {'schema_version': 1, 'audit_kind': 'module_import_closure_not_proof_port',
            'source': {'repository': 'openai/math', 'commit': PIN},
            'downstream': {'repository': 'LionSR/TNLean', 'base_commit': BASE},
            'provenance_policy_issue': 'https://github.com/LionSR/TNLean/issues/8737',
            'declaration_ledger': 'docs/provenance/openai-math.d/8741.json (future declaration mappings; owned schema #8737)',
            'source_configuration': configuration(upstream, PIN, 'lean/', ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']),
            'downstream_configuration': configuration(downstream, BASE, '', ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']),
            'licenses_sha256': licenses,
            'tracked_notice_paths': [p for p in git(upstream, 'ls-tree', '-r', '--name-only', PIN).decode().splitlines() if Path(p).name.upper().startswith('NOTICE')],
            'module_count': len(rows), 'source_lines': sum(m['lines'] for m in modules),
            'external_imports': sorted({d for _, ds in rows.values() for d in ds if not d.startswith('OAI.')}),
            'roots': roots, 'modules': modules,
            'root_predicate_expansions': [{'module': predicate_module,
                'declaration': 'OAI.PolynomialPEPS.PhysicalMove.LocalMove.OneCopyMoveBound',
                'source_lines': [48, 56], 'text': predicate_text, 'sha256': digest(predicate_text.encode())}],
            'excluded_from_roots': ['OAI.MathematicalPhysics.PEPSSubvolume.Main', 'OAI.MathematicalPhysics.TensorNetwork.VectorColumn'],
            'reserved_issues': [8739, 8761, 8762, 8763, 8764, 8768],
            'limitations': ['Minimal under unchanged explicit module imports; not minimal declaration dependencies.',
                            'Lexical declaration anchors are not fully qualified kernel names; anonymous/generated declarations are not enumerated.',
                            'No mathematical equivalence, source faithfulness, axiom closure, or compiled port is inferred.',
                            'No MPU-gauging work; dependency pins unchanged.']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream', type=Path, required=True)
    parser.add_argument('--downstream', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path, default=Path('docs/provenance/openai-math-port-manifest.json'))
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = json.dumps(audit(args.upstream, args.downstream), ensure_ascii=False, indent=2) + '\n'
    if args.check:
        if args.output.read_text() != result: raise SystemExit('manifest differs; regenerate and review')
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result)


if __name__ == '__main__': main()
