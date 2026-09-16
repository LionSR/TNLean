"""Bounded environment-four coefficient-kernel experiments.

Run from the repository root with single-threaded BLAS:
    OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 -B \
        docs/audits/rfp_intrinsic/checks/environment_four_search.py
Use --validate-only to independently rebuild saved numerical results.

Source: next_targets.tex, equations Gram, trace-cp, Pauli, cheap. Physical
basis is (logical, redundant) followed by the scalar, with lexicographic
virtual index (u,u'). All arrays are dimensionless. No CPTP feasibility is
inferred from a small kernel residual. A separately developed obstruction is
in docs/audits/rfp_intrinsic/environment_four.tex. The experiments
below are regression/conditioning evidence, not the proof of that obstruction.

Exploratory parameterization: four minimal Kraus matrices of a faithful
rank-one replacement CP map, mixed by U(4), with the first two active.
The search varies the active two-plane using exponential Grassmann charts
around seeded Haar frames. The canonical mode takes R=I and L diagonal;
its sufficiency for a general classification is NOT assumed here. A
second mode samples independent positive input and output weights.
Neither finite charts nor finite local optimization certify global coverage.

The physical Hilbert-Schmidt metric matters: J1 multiplies each of the four
active coordinate norms by ||tau||_F, not by one. Computation in 5 and 25
coordinates is checked against literal 25 and 625 physical coordinates.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass, replace
from itertools import product
import hashlib
import json
from pathlib import Path
import platform
import time

import numpy as np
import scipy
from scipy.linalg import expm
from scipy.optimize import least_squares
import sympy as sp


@dataclass(frozen=True)
class Config:
    seed: int = 20260916
    tau: tuple[float, float] = (1 / 3, 2 / 3)
    canonical_starts: int = 12
    full_starts: int = 4
    max_nfev: int = 180
    rank_rtol: float = 1e-9
    survivor_tol: float = 1e-8
    span_ratio_floor: float = 0.05
    weight_floor: float = 0.10
    enforce_canonical_weight_floor: bool = False
    penalty_scale: float = 10.0
    optimizer_tol: float = 1e-10
    refinement_nfev: int = 500
    refinement_penalty: float = 100.0
    refinement_span_floor: float = 0.06
    refinement_diff_steps: tuple[float, float] = (1e-5, 1e-6)
    interior_weight_floors: tuple[float, float] = (0.2, 0.3)
    output: str = 'build/audits/rfp_intrinsic/environment_four'


CONFIG = Config()
PAULI = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]],
                  [[1, 0], [0, -1]]], dtype=complex)


def adjoint(a: np.ndarray) -> np.ndarray:
    return a.conj().T


def positive_root(a: np.ndarray) -> np.ndarray:
    d, v = np.linalg.eigh(a)
    return (v * np.sqrt(d)) @ adjoint(v)


def haar(rng: np.random.Generator, n: int) -> np.ndarray:
    q, r = np.linalg.qr(rng.normal(size=(n, n)) + 1j*rng.normal(size=(n, n)))
    return q @ np.diag(np.diag(r) / np.abs(np.diag(r)))


def density(v: np.ndarray, config: Config) -> np.ndarray:
    # The Bloch radius stays strictly below 1-2*weight_floor.
    b = (1 - 2*config.weight_floor)*v / np.sqrt(1 + np.dot(v, v))
    return (np.eye(2) + np.einsum('i,ijk->jk', b, PAULI))/2


def parameters(x: np.ndarray, base: np.ndarray, mode: str,
               config: Config) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray]:
    z = x[:4].reshape(2, 2) + 1j*x[4:8].reshape(2, 2)
    generator = np.block([[np.zeros((2, 2)), z], [-adjoint(z), np.zeros((2, 2))]])
    unitary = expm(generator) @ base
    if mode == 'canonical':
        r = np.eye(2)
        ell = np.diag([x[8], 1-x[8]])
    else:
        r = 2*density(x[8:11], config)
        ell = density(x[11:14], config)
        ell = ell / np.trace(ell @ r).real
    sr, sl = positive_root(r), positive_root(ell)
    units = np.eye(4).reshape(4, 2, 2)
    minimal = np.array([sr @ e @ sl for e in units])
    kraus = np.einsum('ab,bij->aij', unitary, minimal)
    return kraus, r, ell, unitary


def coordinate_rows(kraus: np.ndarray) -> np.ndarray:
    active, scalar = kraus[:2], kraus[2:]
    return np.array([np.kron(a, b.conj()) for a in active for b in active] +
                    [sum(np.kron(c, c.conj()) for c in scalar)])


def coefficient_maps(kraus: np.ndarray, config: Config) -> tuple[np.ndarray, np.ndarray]:
    rows = coordinate_rows(kraus)
    weights = np.array([np.linalg.norm(config.tau)]*4 + [1.0])
    one = (rows * weights[:, None, None]).reshape(5, 16)
    two = np.einsum('iab,jbc->ijac', rows, rows)
    two *= weights[:, None, None, None]*weights[None, :, None, None]
    return one, two.reshape(25, 16)


def kernel_residual(one: np.ndarray, two: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    _, singular, vh = np.linalg.svd(one, full_matrices=False)
    projection = adjoint(vh) @ vh
    return (two - two @ projection)/np.linalg.norm(two), singular


def objective(x: np.ndarray, base: np.ndarray, mode: str, config: Config) -> np.ndarray:
    kraus, r, ell, _ = parameters(x, base, mode, config)
    one, two = coefficient_maps(kraus, config)
    residual, singular = kernel_residual(one, two)
    penalty = config.penalty_scale*max(0., config.span_ratio_floor-singular[-1]/singular[0])
    if config.enforce_canonical_weight_floor:
        sr = positive_root(r)
        minimum = np.linalg.eigvalsh(sr @ ell @ sr)[0]
        weight_penalty = config.penalty_scale*max(0., config.weight_floor-minimum)
        return np.r_[residual.real.ravel(), residual.imag.ravel(), penalty, weight_penalty]
    return np.r_[residual.real.ravel(), residual.imag.ravel(), penalty]


def physical_letters(kraus: np.ndarray, config: Config) -> np.ndarray:
    rows = coordinate_rows(kraus)
    letters = np.zeros((4, 4, 5, 5), dtype=complex)
    for a, b in product(range(4), repeat=2):
        letters[a, b, :4, :4] = np.kron(rows[:4, a, b].reshape(2, 2), np.diag(config.tau))
        letters[a, b, 4, 4] = rows[4, a, b]
    return letters


def literal_blocking(letters: np.ndarray) -> np.ndarray:
    return np.array([[sum(np.kron(letters[a, c], letters[c, b]) for c in range(4))
                      for b in range(4)] for a in range(4)])


def singular_record(matrix: np.ndarray, config: Config) -> dict:
    singular = np.linalg.svd(matrix, compute_uv=False)
    rank = int(np.sum(singular > singular[0]*config.rank_rtol))
    return {'singular_values': singular.tolist(), 'rank': rank,
            'smallest_nonzero': float(singular[rank-1]),
            'nonzero_ratio': float(singular[rank-1]/singular[0])}


def metrics(kraus: np.ndarray, r: np.ndarray, ell: np.ndarray, config: Config) -> dict:
    one, two = coefficient_maps(kraus, config)
    residual, singular = kernel_residual(one, two)
    _, s2, vh2 = np.linalg.svd(two, full_matrices=False)
    rank2 = np.sum(s2 > s2[0]*config.rank_rtol)
    p2 = adjoint(vh2[:rank2]) @ vh2[:rank2]
    rows = coordinate_rows(kraus)
    transfer = rows[0] + rows[3] + rows[4]
    expected = np.outer(r.ravel(), ell.T.ravel())
    gram_scalar = kraus[2:].reshape(2, 4).T @ kraus[2:].reshape(2, 4).conj()
    weights = [np.linalg.eigvalsh(w/np.trace(w)).tolist() for w in (r, ell)]
    sr = positive_root(r)
    canonical_weights = np.linalg.eigvalsh(sr @ ell @ sr).tolist()
    forward = float(np.linalg.norm(residual))
    ratio = float(singular[-1]/singular[0])
    return {'forward_normalized': forward,
            'reverse_normalized': float(np.linalg.norm(one-one@p2)/np.linalg.norm(one)),
            'one': singular_record(one, config), 'two': singular_record(two, config),
            'one_span_ratio': ratio,
            'trace_idempotence_normalized': float(np.linalg.norm(transfer@transfer-transfer)/np.linalg.norm(transfer)),
            'trace_reconstruction_normalized': float(np.linalg.norm(transfer-expected)/np.linalg.norm(expected)),
            'trace_singular_values': np.linalg.svd(transfer, compute_uv=False).tolist(),
            'weight_spectra_normalized': weights,
            'canonical_weight_spectrum': canonical_weights,
            'gram_B0_eigenvalue': float(np.linalg.norm(kraus[:2])**2),
            'gram_B1_eigenvalues': np.linalg.eigvalsh(gram_scalar).tolist(),
            'survivor': bool(forward < config.survivor_tol and ratio >= config.span_ratio_floor
                             and rank2 == 5 and min(map(min, weights)) >= config.weight_floor-1e-12
                             and canonical_weights[0] >= config.weight_floor-1e-12)}


def reconstruction_checks(kraus: np.ndarray, r: np.ndarray, ell: np.ndarray,
                          config: Config, rng: np.random.Generator) -> dict:
    one, two = coefficient_maps(kraus, config)
    letters = physical_letters(kraus, config)
    blocked = literal_blocking(letters)
    literal_one = letters.reshape(16, 25).T
    literal_two = blocked.reshape(16, 625).T
    gram_errors = [np.linalg.norm(adjoint(a)@a-adjoint(b)@b)
                   for a, b in ((one, literal_one), (two, literal_two))]
    # Build the four environment amplitudes rather than infer Gram ranks.
    amplitudes = np.zeros((2, 2, 4, 5), dtype=complex)
    for u, v in product(range(2), repeat=2):
        for redundant in range(2):
            amplitudes[u, v, redundant, redundant:4:2] = np.sqrt(config.tau[redundant])*kraus[:2, u, v]
        amplitudes[u, v, 2:, 4] = kraus[2:, u, v]
    rebuilt = np.einsum('uvei,wxej->uwvxij', amplitudes, amplitudes.conj()).reshape(4, 4, 5, 5)
    purification_error = np.linalg.norm(rebuilt-letters)
    env = amplitudes.transpose(2, 0, 1, 3).reshape(4, 20)
    env_singular = np.linalg.svd(env, compute_uv=False)
    # Virtual similarity changes coordinate norms, but preserves exact kernels.
    g = haar(rng, 2) @ np.diag([1., 1.4]) @ haar(rng, 2)
    gi = np.linalg.inv(g)
    changed = np.array([g @ k @ gi for k in kraus])
    gauge = np.kron(g, g.conj())
    gauge_error = np.linalg.norm(coordinate_rows(changed)-
                                 np.array([gauge @ c @ np.linalg.inv(gauge) for c in coordinate_rows(kraus)]))
    # Empirical canonical reconstruction, not a proof of global chart coverage.
    sr = positive_root(r)
    eigenvalues, eigenvectors = np.linalg.eigh(sr @ ell @ sr)
    gc = adjoint(eigenvectors) @ np.linalg.inv(sr)
    canonical = np.array([gc @ k @ np.linalg.inv(gc) for k in kraus])
    minimal = np.array([e @ np.diag(np.sqrt(eigenvalues)) for e in np.eye(4).reshape(4, 2, 2)])
    mixing = canonical.reshape(4, 4) @ np.linalg.inv(minimal.reshape(4, 4))
    mixing_error = np.linalg.norm(mixing @ adjoint(mixing)-np.eye(4))
    # Independent environment rotations: active rotates logical coordinates,
    # scalar rotation leaves the scalar letters unchanged.
    sector_rotation = scipy.linalg.block_diag(haar(rng, 2), haar(rng, 2))
    rotated = np.einsum('ab,bij->aij', sector_rotation, kraus)
    rotation_error = abs(metrics(rotated, r, ell, config)['forward_normalized']-
                         metrics(kraus, r, ell, config)['forward_normalized'])
    values = [*gram_errors, purification_error, gauge_error, mixing_error, rotation_error]
    assert max(values) < 1e-10, values
    assert env_singular[-1] > 1e-5
    return {'physical_gram_errors': [float(e) for e in gram_errors],
            'purification_error': float(purification_error),
            'environment_singular_values': env_singular.tolist(),
            'virtual_gauge_error': float(gauge_error),
            'canonical_mixing_unitarity_error': float(mixing_error),
            'sector_rotation_residual_error': float(rotation_error)}


def exact_structured_checks() -> list[dict]:
    # A small exact relation suffices to reject, even when ranks happen to agree.
    units = [sp.eye(4)[:, i].reshape(2, 2)/sp.sqrt(2) for i in range(4)]
    seeds = {'pauli': [sp.eye(2)/2, sp.Matrix([[0, 1], [1, 0]])/2,
                       sp.Matrix([[0, -sp.I], [sp.I, 0]])/2, sp.diag(1, -1)/2],
             'matrix_units_diagonal_active': [units[i] for i in (0, 3, 1, 2)],
             'matrix_units_row_active': units,
             'matrix_units_column_active': [units[i] for i in (0, 2, 1, 3)]}
    records = []
    for name, ks in seeds.items():
        rows = [sp.kronecker_product(a, sp.conjugate(b)) for a in ks[:2] for b in ks[:2]]
        rows += [sum((sp.kronecker_product(c, sp.conjugate(c)) for c in ks[2:]), sp.zeros(4))]
        one = sp.Matrix.vstack(*(m.reshape(1, 16) for m in rows))
        two = sp.Matrix.vstack(*((a*b).reshape(1, 16) for a in rows for b in rows))
        transfer = rows[0]+rows[3]+rows[4]
        assert transfer**2 == transfer and transfer.rank() == 1
        witness = None
        for c in one.nullspace():
            image = two*c
            nz = next((i for i, v in enumerate(image) if v != 0), None)
            if nz is not None:
                witness = {'relation': [str(v) for v in c], 'blocked_coordinate': nz,
                           'residual': str(image[nz])}
                assert one*c == sp.zeros(5, 1)
                break
        entry = {'name': name, 'one_rank': one.rank(), 'two_rank': two.rank(),
                 'kernel_inclusion': witness is None, 'witness': witness}
        if name == 'pauli':
            assert entry['one_rank'] == 5 and entry['two_rank'] == 6
            tau = sp.diag(sp.Rational(1, 3), sp.Rational(2, 3))
            letters = {}
            for a, b in product(range(4), repeat=2):
                letters[a, b] = sp.diag(sp.kronecker_product(sp.Matrix(2, 2, [row[a, b] for row in rows[:4]]), tau), rows[4][a, b])
            assert letters[1, 0] == letters[0, 1]
            residual = sum((sp.kronecker_product(letters[1, c], letters[c, 0])-
                            sp.kronecker_product(letters[0, c], letters[c, 1]) for c in range(4)), sp.zeros(25))
            assert residual[4, 14] == sp.Rational(1, 24)
            entry['physical_witness_4_14'] = str(residual[4, 14])
        records.append(entry)
    return records


def write_json(path: Path, data: dict | list) -> None:
    path.write_text(json.dumps(data, indent=2, allow_nan=False)+'\n')


def validate_saved(config: Config) -> dict:
    out = Path(config.output)
    saved = json.loads((out/'results.json').read_text())
    rng = np.random.default_rng(config.seed)
    checks = []
    records = saved['runs'].copy()
    if (out/'refinements.json').exists():
        records += json.loads((out/'refinements.json').read_text())['runs']
    for record in records:
        data = np.load(out/record['artifact'])
        local = Config(**json.loads(str(data['config_json'])))
        kraus, r, ell, unitary = parameters(data['x'], data['base'], record['mode'], local)
        assert np.linalg.norm(kraus-data['kraus']) < 1e-12
        assert np.linalg.norm(unitary@adjoint(unitary)-np.eye(4)) < 1e-12
        check = reconstruction_checks(kraus, r, ell, local, rng)
        current = metrics(kraus, r, ell, local)
        assert current['trace_idempotence_normalized'] < 1e-12
        assert current['trace_reconstruction_normalized'] < 1e-12
        assert abs(current['forward_normalized']-record['final']['forward_normalized']) < 1e-12
        check['artifact'] = record['artifact']
        check['metrics_recomputed'] = current
        checks.append(check)
    return {'checks': checks, 'all_passed': True}


def ideal_diagnostic(kraus: np.ndarray, r: np.ndarray, ell: np.ndarray,
                     config: Config) -> dict:
    """Test rank-one-ideal dimensions in a trace-preserving replacement gauge.

    Closure is checked numerically, not presumed. The identity rank(V T V) =
    d_left*d_right is only a diagnostic here, not an exclusion theorem.
    """
    g = positive_root(ell)
    gi = np.linalg.inv(g)
    active = np.array([g @ a @ gi for a in kraus[:2]])
    rho = g @ r @ g
    left = np.array([rho] + [a @ rho @ adjoint(b) for a in active for b in active])
    right = np.array([np.eye(2)] + [adjoint(b) @ a for a in active for b in active])
    transfer = np.outer(rho.ravel(), np.eye(2).ravel())
    v = np.array([transfer] + [np.kron(a, b.conj()) for a in active for b in active])
    ideal = np.array([a @ transfer @ b for a in v for b in v]).reshape(25, 16)
    _, _, vh = np.linalg.svd(v.reshape(5, 16), full_matrices=False)
    projection = adjoint(vh) @ vh
    leakage = np.linalg.norm(ideal-ideal@projection)/np.linalg.norm(ideal)
    return {'left': singular_record(left.reshape(5, 4), config),
            'right': singular_record(right.reshape(5, 4), config),
            'ideal': singular_record(ideal, config),
            'ideal_leakage_normalized': float(leakage),
            'rho_spectrum': np.linalg.eigvalsh(rho).tolist(),
            'interpretation': 'Numerical singular spectra, not an exact closure/no-go certificate.'}


def exact_ideal_diagnostics() -> list[dict]:
    units = [sp.eye(4)[:, i].reshape(2, 2)/sp.sqrt(2) for i in range(4)]
    seeds = {'pauli': [sp.eye(2)/2, sp.Matrix([[0, 1], [1, 0]])/2],
             'matrix_units_diagonal_active': [units[0], units[3]],
             'matrix_units_row_active': units[:2],
             'matrix_units_column_active': [units[0], units[2]],
             'generic_lemma_control': [sp.Matrix([[1, 1], [0, 1]]),
                                      sp.Matrix([[1, 0], [1, 2]])]}
    result = []
    rho = sp.eye(2)/2
    transfer = rho.reshape(4, 1)*sp.eye(2).reshape(1, 4)
    for name, active in seeds.items():
        left = [rho]+[a*rho*b.conjugate().T for a in active for b in active]
        right = [sp.eye(2)]+[b.conjugate().T*a for a in active for b in active]
        v = [transfer]+[sp.kronecker_product(a, sp.conjugate(b)) for a in active for b in active]
        flatten = lambda matrices: sp.Matrix.vstack(*(a.reshape(1, len(a)) for a in matrices))
        dl, dr = flatten(left).rank(), flatten(right).rank()
        ideal = flatten([a*transfer*b for a in v for b in v])
        assert ideal.rank() == dl*dr
        square = flatten([a*b for a in v for b in v])
        result.append({'name': name, 'd_left': dl, 'd_right': dr,
                       'V_dimension': flatten(v).rank(),
                       'V_square_dimension': square.rank(),
                       'V_plus_V_square_dimension': flatten(v).col_join(square).rank(),
                       'ideal_rank': ideal.rank(),
                       'ideal_contained_in_V': flatten(v).col_join(ideal).rank() == flatten(v).rank(),
                       'scope': 'lemma-only control; no four-Kraus completion asserted' if name.startswith('generic')
                                else 'trace-preserving replacement Kraus seed'})
    return result


def supplementary(config: Config) -> None:
    """Recenter low-residual charts and vary numerical/domain controls."""
    out = Path(config.output)
    saved = json.loads((out/'results.json').read_text())
    rng = np.random.default_rng(config.seed)
    diagnostic = {'exact_structured': exact_ideal_diagnostics(), 'endpoints': []}
    for record in saved['runs']:
        a = np.load(out/record['artifact'])
        diagnostic['endpoints'].append({'run': record['run'],
            **ideal_diagnostic(a['kraus'], a['R'], a['L'], config)})
    write_json(out/'ideal_diagnostics.json', diagnostic)
    selected = [min((a for a in saved['runs'] if a['mode'] == mode),
                    key=lambda a: a['final']['forward_normalized']) for mode in ('canonical', 'full')]
    tests = []
    for record in selected:
        for step in config.refinement_diff_steps:
            tests.append((record, config.weight_floor, step))
    for floor in config.interior_weight_floors:
        for record in selected:
            tests.append((record, floor, config.refinement_diff_steps[-1]))
    results = {'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
               'description': 'Eight recentered refinements, varied finite differences and interior weight floors.',
               'runs': []}
    for index, (record, floor, step) in enumerate(tests):
        local = replace(config, weight_floor=floor, span_ratio_floor=config.refinement_span_floor,
                        penalty_scale=config.refinement_penalty, max_nfev=config.refinement_nfev)
        data = np.load(out/record['artifact'])
        base = data['unitary']
        x = data['x'].copy()
        x[:8] = 0
        if record['mode'] == 'canonical':
            x[8] = max(x[8], floor+1e-4)
        lower, upper = data['lower'].copy(), data['upper'].copy()
        if record['mode'] == 'canonical':
            lower[8] = floor
        start = time.monotonic()
        solution = least_squares(objective, x, args=(base, record['mode'], local),
                                 bounds=(lower, upper), diff_step=step,
                                 max_nfev=local.max_nfev, ftol=local.optimizer_tol,
                                 xtol=local.optimizer_tol, gtol=local.optimizer_tol)
        kraus, r, ell, unitary = parameters(solution.x, base, record['mode'], local)
        final = metrics(kraus, r, ell, local)
        artifact = f'refine_{index:02d}.npz'
        np.savez_compressed(out/artifact, x=solution.x, initial_x=x, base=base, kraus=kraus,
                            R=r, L=ell, unitary=unitary, config_json=json.dumps(asdict(local)),
                            seed=local.seed, tau=np.array(local.tau), lower=lower, upper=upper)
        rebuilt, rr, ll, _ = parameters(solution.x, base, record['mode'], local)
        checks = reconstruction_checks(rebuilt, rr, ll, local, rng)
        entry = {'index': index, 'parent_run': record['run'], 'mode': record['mode'],
                 'diff_step': step, 'config': asdict(local), 'artifact': artifact,
                 'final': final, 'validation': checks,
                 'ideal': ideal_diagnostic(kraus, r, ell, local),
                 'nfev': solution.nfev, 'status': solution.status,
                 'optimality': float(solution.optimality),
                 'elapsed_seconds': time.monotonic()-start}
        results['runs'].append(entry)
        write_json(out/'refinements.json', results)
        print(json.dumps({'refinement': index, 'floor': floor, 'mode': record['mode'],
                          'residual': final['forward_normalized'], 'span_ratio': final['one_span_ratio']}), flush=True)
    # Distribution summaries are generated from persisted endpoints, not copied constants.
    summary = {}
    for mode in ('canonical', 'full'):
        records = [r['final'] for r in saved['runs'] if r['mode'] == mode]
        summary[mode] = {'count': len(records)}
        for key in ('forward_normalized', 'one_span_ratio'):
            summary[mode][key+'_min_median_max'] = np.quantile([r[key] for r in records], [0, .5, 1]).tolist()
        summary[mode]['one_smallest_nonzero_min_max'] = [float(f([r['one']['smallest_nonzero'] for r in records])) for f in (min, max)]
    summary['survivors_initial_and_refined'] = sum(r['final']['survivor'] for r in saved['runs']+results['runs'])
    summary['domain_caveat'] = 'Finite local charts with bounded faithful weights. No universal nonexistence claim.'
    write_json(out/'summary.json', summary)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--validate-only', action='store_true')
    parser.add_argument('--supplementary', action='store_true')
    parser.add_argument('--controls-only', action='store_true')
    parser.add_argument('--output', type=str, help='Use a separate output directory.')
    args = parser.parse_args()
    config = replace(CONFIG, output=args.output) if args.output else CONFIG
    out = Path(config.output)
    if args.controls_only:
        proof = Path('docs/audits/rfp_intrinsic/sections/environment_four/obstruction.tex')
        write_json(out/'structural_controls.json', {
            'exact': exact_ideal_diagnostics(), 'pauli_and_seed_checks': exact_structured_checks(),
            'independent_proof': str(proof),
            'proof_sha256': hashlib.sha256(proof.read_bytes()).hexdigest() if proof.exists() else None,
            'scope': 'Exact finite controls of a separate lemma; optimizations are not a nonexistence proof.'})
        print('Exact structural controls passed.')
        return
    if args.supplementary:
        supplementary(config)
        return
    if args.validate_only:
        result = validate_saved(config)
        write_json(out/'validation.json', result)
        print(json.dumps({'all_passed': result['all_passed'], 'runs': len(result['checks'])}))
        return
    out.mkdir(parents=True, exist_ok=True)
    if (out/'results.json').exists():
        raise FileExistsError('Existing results.json: preserve prior experiments before rerunning.')
    started = time.monotonic()
    rng = np.random.default_rng(config.seed)
    result = {'config': asdict(config), 'versions': {'python': platform.python_version(),
              'numpy': np.__version__, 'scipy': scipy.__version__, 'sympy': sp.__version__},
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'hypothesis': 'No kernel-compatible nondegenerate interior point in bounded trials.',
              'scope': 'Exploratory canonical and independent-weight Grassmann charts, not a general no-go.',
              'structured': exact_structured_checks(), 'runs': []}
    print(json.dumps(result['structured']), flush=True)
    modes = ['canonical']*config.canonical_starts + ['full']*config.full_starts
    for index, mode in enumerate(modes):
        base = haar(rng, 4)
        x = np.zeros(9 if mode == 'canonical' else 14)
        lower, upper = np.full(len(x), -np.pi), np.full(len(x), np.pi)
        if mode == 'canonical':
            x[8] = rng.uniform(config.weight_floor, .5)
            lower[8], upper[8] = config.weight_floor, .5
        else:
            x[8:] = rng.uniform(-1, 1, 6)
            lower[8:], upper[8:] = -2, 2
        initial_k, initial_r, initial_l, _ = parameters(x, base, mode, config)
        initial = metrics(initial_k, initial_r, initial_l, config)
        begin = time.monotonic()
        solution = least_squares(objective, x, args=(base, mode, config),
                                 bounds=(lower, upper), max_nfev=config.max_nfev,
                                 ftol=config.optimizer_tol, xtol=config.optimizer_tol,
                                 gtol=config.optimizer_tol)
        kraus, r, ell, unitary = parameters(solution.x, base, mode, config)
        final = metrics(kraus, r, ell, config)
        artifact = f'run_{index:02d}.npz'
        np.savez_compressed(out/artifact, x=solution.x, initial_x=x, base=base, kraus=kraus,
                            R=r, L=ell, unitary=unitary, lower=lower, upper=upper,
                            tau=np.array(config.tau), seed=config.seed,
                            config_json=json.dumps(asdict(config)))
        record = {'run': index, 'mode': mode, 'artifact': artifact, 'initial': initial,
                  'final': final, 'nfev': solution.nfev, 'njev': solution.njev,
                  'status': solution.status, 'message': solution.message,
                  'optimality': float(solution.optimality),
                  'elapsed_seconds': time.monotonic()-begin,
                  'parameters': solution.x.tolist()}
        result['runs'].append(record)
        result['elapsed_seconds'] = time.monotonic()-started
        write_json(out/'results.json', result)
        print(json.dumps({k: record[k] for k in ('run', 'mode', 'nfev', 'elapsed_seconds')} |
                         {'residual': final['forward_normalized'], 'span_ratio': final['one_span_ratio'],
                          'rank_two': final['two']['rank'], 'survivor': final['survivor']}), flush=True)
    write_json(out/'validation.json', validate_saved(config))
    print('Independent reconstruction checks passed.', flush=True)


if __name__ == '__main__':
    main()
