# Source audit: analytic infrastructure for the Q2 proof

**Date:** 2026-07-16
**Scope:** Matrix trace norm, locally integrable time-dependent Lindblad propagators,
weak-* compactness of convex-hull-valued controls and continuity of controlled
trajectories, and degenerate Hermitian eigenvalue perturbation.
**Primary local source audited:** Michael M. Wolf, *Quantum Channels & Operations:
Guided Tour*, TeX transcription in `Notes/WolfNoteTexSource/`.
**Comparison source:** Wolff--Malz--Trivedi, *Contractivity of time-dependent
driven-dissipative systems*, arXiv:2602.16067v1 (2026), abbreviated **WMT**.
**Mathlib snapshot:** rescanned against the upgraded `origin/main` target,
Lean/Mathlib v4.32.0, Mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`.  The checked-out audit branch
still has a v4.31.0 toolchain file; all v4.32 source comparisons and the
trace-norm compatibility test were performed without changing that branch.

---

## Executive conclusion

Wolf is a reliable source for the **static finite-dimensional trace/Schatten norm
background** and for **homogeneous, time-independent quantum dynamical
semigroups**.  Wolf is not a source for the full analytic infrastructure required
by Q2:

1. Chapter 8 defines the trace norm and proves variational duality, but does not
   prove its directional derivative at singular Hermitian matrices.
2. Chapter 7 treats constant generators and one-parameter semigroups, not
   propagators for locally integrable non-autonomous generators.
3. The notes contain no weak-* compactness theory for measurable controls and no
   weak-* continuity theorem for controlled trajectories.
4. Chapter 6 contains spectral decompositions and resolvents, but no degenerate
   Hermitian first-order perturbation theorem.

WMT Proposition 19 states the target trace-norm right-derivative formula and
cites Kato for the spectral perturbation step.  WMT merely **asserts** existence
of the locally integrable time-dependent propagator by writing a time-ordered
exponential; it does not prove the existence, uniqueness, cocycle, stability, or
CPTP properties needed for a faithful Lean development.  Consequently, the Q2
formalization should separate the Wolf-derived static API from the external or
direct analytic developments.

### Lean/Mathlib 4.32 rescout

The v4.32 upgrade does not change the source verdict.  A direct comparison of
Mathlib revisions v4.31.0 and v4.32.0 found:

- no new `traceNorm`, Schatten norm, or nuclear norm declaration;
- no Hermitian eigenvalue perturbation, eigenvalue-continuity, or matrix-sign
  API sufficient for Proposition 19;
- no non-autonomous propagator, Peano--Baker, or locally-integrable linear ODE
  construction; the changes in `Mathlib.Analysis.ODE` are only maintenance;
- the existing Banach--Alaoglu theorems remain available;
- `ContinuousLinearMap.lpPairing` already provides the useful `L∞`/`L¹`
  integration pairing, while v4.32 adds `WeakDual.extendRCLikeL` for real/complex
  weak-dual transport; neither supplies the missing `L∞ ≃ (L¹)′` or admissible
  control compactness theorem.

Separately, TNLean already has a basic trace-norm prototype on branch
`feat/analysis-schatten-one`.  Cherry-picking its two implementation commits
onto upgraded `origin/main` and compiling
`TNLean/Analysis/SchattenNorm.lean` under Lean/Mathlib v4.32.0 succeeded without
source changes.  Thus the first implementation PR should be resumed and rebased,
not restarted.

---

## Coverage table

| Ingredient | Wolf coverage | WMT coverage | Formalization reliability | Current Mathlib/TNLean support | Missing Lean lemmas | Recommended source hierarchy |
|---|---|---|---|---|---|---|
| **Matrix trace norm and variational/directional derivative theory** | **Partial.** Chapter 8, §8.1, `ch08_distance_measures.tex:44-203`: Schatten and Ky Fan norms at lines 63-75; `‖A‖₁ = tr |A|` at lines 86-95; Hölder trace duality Eq. (8.6); Ky Fan variational formula Eq. (8.9); theorem *Variational ways to p-norms*, Eqs. (8.10)-(8.13); dual norm Eq. (8.14). No sign matrix, subgradient, or directional derivative. | **Proposition 19**, label `prop:right time derivative form`, lines 624-635, gives the right derivative along driven Lindblad evolution. Its proof is in the appendix, lines 1053-1129, and invokes Kato at lines 1085-1089. | Wolf is reliable for definitions and duality, but insufficient for differentiation. WMT is a useful target statement, not a self-contained foundational source. | Mathlib 4.32 still has `LinearMap.singularValues` but no packaged Schatten-1 norm or singular-value triangle inequality. TNLean branch `feat/analysis-schatten-one` already defines `Matrix.schattenOneNorm`/`Matrix.traceNorm` and proves support expansions, nonnegativity, and definiteness. That prototype was compile-tested successfully against v4.32, but it is not yet on upgraded `origin/main` and does not yet prove the norm, duality, or derivative API. | Complete the existing prototype with norm axioms, unitary invariance, Hermitian eigenvalue formula, operator-norm duality, kernel projection and matrix sign, one-sided directional derivative, and commutator cancellation. | Existing TNLean prototype + Mathlib singular values → Wolf §8.1 for conventions/duality → Kato plus a direct finite-dimensional trace-norm corollary → WMT Proposition 19 as application. |
| **Propagators for locally integrable time-dependent Lindblad generators** | **Absent.** Chapter 7 proves the homogeneous semigroup theory: Eq. (7.1), differential equation (7.2), Proposition 7.1 (`T_t = e^{tL}`), Duhamel Lemma 7.1 and Eq. (7.10), Dyson--Phillips Eq. (7.13), and time-independent GKSL forms Eqs. (7.20)-(7.23). The note source contains no `T_{t,s}`, locally integrable generator, or non-autonomous propagator theorem. | At source line 164, after Eq. `time_dep_lindblad`, WMT says that local integrability gives a unique solution `E_{t,s} = T exp(∫ L_τ dτ)`. This is an assertion and notation, not a construction or proof. | **Insufficient as cited.** A time-ordered exponential symbol does not establish existence, uniqueness, absolute continuity, the cocycle law, stability, or CPTP preservation. | Mathlib has Bochner integration, Gronwall, and continuous-vector-field Picard--Lindelöf, including `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`, but no ready-made locally-integrable linear evolution family. TNLean has constant-generator `expSemigroupCLM` and constant-generator Duhamel/Dyson results. | Volterra/Peano--Baker construction for `L ∈ L¹_loc`; uniqueness; integral equation; absolute continuity; identity and cocycle; `L¹` stability estimate; step-function approximation; Hermiticity, trace, positivity, and complete-positivity preservation. | Standard Carathéodory linear ODE theorem or direct Peano--Baker proof → direct step-approximation/CPTP closure proof → WMT only for notation and intended application. Wolf only for the constant-generator specialization. |
| **Weak-* compactness of convex-hull-valued controls and weak-* continuity of trajectories** | **Absent.** Chapter 4 §4.1 is finite-dimensional convex optimization/SDP duality. It contains no Banach--Alaoglu theorem, `L∞` control space, relaxed controls, or weak-* trajectory theorem. | **Absent.** WMT quantifies over locally integrable Hamiltonians but does not prove compactness of an admissible control class, existence of optimizing controls, or weak-* continuity of the propagator. | Requires an external functional-analysis/control source and substantial direct proof. Wolf and WMT should not be cited for this ingredient. | Mathlib 4.32 has `WeakDual.isCompact_closedBall`, `WeakDual.isSeqCompact_closedBall`, and `ContinuousLinearMap.lpPairing`, which supplies the Hölder integral map from `Lp`--in particular `L∞`--into the dual of its conjugate `Lp` space. The new `WeakDual.extendRCLikeL` helps pass between real and complex weak duals. There is still no `L∞ ≃ (L¹)′` equivalence/isometry or closed-image theorem, no a.e. convex-valued control compactness theorem, and no trajectory-continuity API. TNLean has only `TNLean.IsCompact.convexHull` for finite-dimensional point sets. | Complete the `L∞`-to-weak-dual bridge or use an alternative compactness representation; prove weak-* sequential compactness and closedness of a.e. simplex/convex-hull constraints; measurable representatives; uniform trajectory bounds/equicontinuity; passage to the limit in the control-affine integral equation; weak-* control convergence implying uniform trajectory convergence. | Mathlib `lpPairing` and Banach--Alaoglu foundation → standard `L∞`/optimal-control source → direct finite-dimensional controlled-propagator continuity proof. |
| **Degenerate Hermitian eigenvalue perturbation** | **Absent.** Chapter 6's resolvent discussion, `ch06_spectral_properties.tex:286-332`, gives Eqs. (6.17)-(6.21), including contour spectral projections and holomorphic functional calculus. It does not give first-order eigenvalue splitting in a degenerate eigenspace. Chapter 7 perturbation theory concerns constant semigroup generators, not eigenvalue branches. | Used in the proof of Proposition 19 at lines 1085-1089 and again in the proof following Proposition 26 at lines 1171-1175. WMT says to diagonalize the compressed perturbation inside each degenerate eigenspace and cites Kato §2.6. | WMT is an application sketch. Kato or a direct finite-dimensional theorem is needed as the actual source. | Mathlib has Hermitian spectral decomposition, eigenvalues, eigenvector unitaries, and singular values. TNLean has extremal-eigenvalue and spectral-shift helpers in `TNLean/Algebra/HermitianHelpers.lean`. Neither contains a first-order degenerate perturbation theorem. | For `A + εB`, identify the first-order shifts near an eigenvalue `λ` with the eigenvalues of `P_λ B P_λ`; establish the required `o(ε)` control; derive the zero-eigenspace term in the trace-norm derivative. | Kato, Chapter II §§5-6 → direct Hermitian-matrix and trace-norm corollaries → WMT Proposition 19 as downstream use. Wolf is not a source. |

---

## Exact Wolf source inventory

### Chapter 8: trace and Schatten norms

The useful Wolf material is concentrated in
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`:

- §8.1, *Norms*, lines 44-203.
- Schatten `p`-norm and Ky Fan `k`-norm definitions: lines 63-75.
- Monotonicity of Schatten norms: Eq. **(8.1)**, lines 77-85.
- Trace norm `‖A‖₁ = tr |A|`: lines 86-95.
- Theorem *Unitarily invariant norms*: lines 106-142.
- Trace Hölder inequality: Eq. **(8.6)**, lines 144-148.
- §8.1 paragraph *Variational characterization of norms*: lines 170-202.
- Ky Fan variational formula: Eq. **(8.9)**.
- Theorem *Variational ways to p-norms*: Eqs. **(8.10)-(8.13)**.
- General dual norm: Eq. **(8.14)**.

This supports a static trace-norm PR.  It does not support the derivative theorem
needed in WMT Proposition 19.

### Chapter 7: homogeneous semigroups only

`Notes/WolfNoteTexSource/ch07_semigroup_structure.tex` contains:

- §7.1, *Dynamical semigroups*, beginning at line 36.
- Semigroup law: Eq. **(7.1)**.
- Constant-generator ODE: Eq. **(7.2)**.
- **Proposition 7.1**, *From continuous semigroups to differentiable groups*,
  lines 67-85.
- Duhamel formula: **Lemma 7.1**, Eq. **(7.10)**.
- Perturbation estimate: **Corollary 7.1**, Eq. **(7.12)**.
- Dyson--Phillips series: Eq. **(7.13)**.
- §7.2, *Quantum dynamical semigroups*, beginning at line 154.
- **Proposition 7.2**, conditional complete positivity, Eqs. **(7.14)-(7.15)**.
- **Proposition 7.3**, completely positive dynamical semigroups.
- Theorem *Generators for semigroups of quantum channels*, Eqs.
  **(7.20)-(7.23)**.

All of these are time-independent.  The notes do not define or construct a
non-autonomous evolution family `E_{t,s}`.

### Chapter 6: static spectral calculus, not perturbation theory

The relevant material is the paragraph *Resolvents* in
`ch06_spectral_properties.tex:286-332`:

- resolvent definition: Eq. **(6.17)**;
- resolvent series: Eq. **(6.18)**;
- contour spectral projection: Eq. **(6.20)**;
- holomorphic functional calculus: Eq. **(6.21)**.

These results are useful possible ingredients for a direct perturbation proof,
but Wolf does not state the degenerate first-order theorem.

### Chapter 4: no weak-* control theory

Chapter 4 §4.1 addresses finite-dimensional convex optimization and Lagrange
or SDP duality.  It does not discuss weak-* topologies, Banach--Alaoglu,
measurable control functions, or compactness of admissible controls.

---

## WMT Proposition 19 and its analytic caveat

WMT Proposition 19, *Right time-derivative of the trace norm under Lindblad
evolution*, states the exact downstream formula required in the contractivity
argument.  Its appendix defines

```text
Δ_ε(t) = (1/ε) ∫_[t,t+ε] (-i[H(τ),x(t)] + D x(t)) dτ
```

and uses the fixed-direction expansion

```text
‖x + εΔ‖₁ = ‖x‖₁
  + tr(sign(x) εΔ)
  + ‖ε Δ|_{ker x}‖₁
  + R_{x,Δ}(ε),
```

with `R_{x,Δ}(ε) = o(ε)` for fixed `x` and `Δ`.

For direct formalization, an extra justification is needed: in the WMT
application, `Δ = Δ_ε(t)` itself depends on `ε`.  Under only local integrability
of `H`, the averages `(1/ε)∫ H` need not be uniformly bounded at every time.
Thus an `o(ε)` estimate proved only for each fixed direction cannot simply be
substituted without a uniform remainder estimate.  The preceding replacement
of the varying state `x(τ)` by the frozen state `x(t)` also requires a careful
argument at this regularity.

A robust Lean proof should use one of the following approaches:

1. first prove the result for bounded piecewise-continuous controls and later
   extend it by approximation;
2. move to an interaction picture, removing the Hamiltonian term exactly by
   unitary conjugation before differentiating the trace norm; or
3. prove a perturbation remainder estimate uniform over the actual family of
   averaged directions.

Kato supplies the fixed finite-dimensional degenerate perturbation theorem, but
not this `ε`-dependent-direction passage automatically.

---

## Current TNLean inventory

The time-independent Wolf Chapter 7 infrastructure is already substantially
present.  In addition, the parallel feature branch `feat/analysis-schatten-one`
contains a v4.32-compatible first slice of the trace-norm API:

- `TNLean/Analysis/SchattenNorm.lean` on `feat/analysis-schatten-one`
  - `Matrix.schattenOneNorm` and `Matrix.traceNorm`;
  - finite-support, rank-range, and `Fin D` singular-value sum formulas;
  - nonnegativity, zero characterization, and positivity away from zero;
  - compile-tested after cherry-picking onto Lean/Mathlib v4.32.0;
  - not yet present on upgraded `origin/main`, and not yet a complete norm API.
- `TNLean/Channel/Semigroup/Basic.lean`
  - `expSemigroupCLM`;
  - `hasDerivAt_expSemigroupCLM`;
  - `continuousDynSemigroup_eq_exp` (Wolf Proposition 7.1).
- `TNLean/Channel/Semigroup/Perturbation.lean`
  - `duhamel_formula`;
  - `perturbation_bound`;
  - Dyson--Phillips terms, convergence, remainder estimates, and series identity.
- `TNLean/Channel/Semigroup/LindbladForm/`
  - conditional complete positivity and time-independent GKSL infrastructure.
- `TNLean/Channel/Semigroup/HamiltonianIndependentContractivity.lean`
  - explicitly records that it formalizes only algebraic companions to WMT and
    not the full analytic conjecture;
  - references Proposition 19 but does not define the trace norm or its derivative.
- `TNLean/Analysis/ConvexHullCompact.lean`
  - finite-dimensional compactness of the convex hull of a compact set.
- `TNLean/Algebra/HermitianHelpers.lean`
  - static extremal-eigenvalue and spectral-shift tools, not perturbation theory.

The static Chapter 7 material therefore should not be duplicated in the Q2
analytic PR series.

---

## Recommended PR decomposition

### PR 1: rebase and complete the general matrix trace norm -- the genuine Wolf PR

Primary source: Wolf Chapter 8 §8.1, supplemented by Mathlib singular values.
Start from the already reviewed prototype on `feat/analysis-schatten-one`; rebase
or cherry-pick it onto the Lean/Mathlib v4.32 branch rather than redefining the
foundational declarations.

The existing branch already supplies `Matrix.traceNorm`, singular-value sum
expansions, nonnegativity, and definiteness.  The completed target API should
include declarations morally equivalent to:

```lean
Matrix.traceNorm
Matrix.traceNorm_eq_sum_singularValues
Matrix.traceNorm_eq_trace_abs
Matrix.traceNorm_eq_sum_abs_eigenvalues_of_isHermitian
Matrix.traceNorm_unitary_mul
Matrix.traceNorm_mul_unitary
Matrix.traceNorm_conj_unitary
Matrix.traceNorm_dual_opNorm
Matrix.abs_trace_mul_le_traceNorm_mul_opNorm
Matrix.continuous_traceNorm
```

This should be a general matrix norm, not a function defined only on Hermitian
matrices.

### PR 2: degenerate perturbation and the trace-norm directional derivative

Primary source: Kato, Chapter II §§5-6.  WMT Proposition 19 is the target
application, not the foundational source.

Desired endpoints include:

```lean
Matrix.IsHermitian.firstOrder_eigenvalues_add_smul
Matrix.IsHermitian.hasRightDerivAt_traceNorm_add_smul
Matrix.trace_sign_commutator_eq_zero
Matrix.traceNorm_rightDerivative_commutator_add
```

The principal formula is

```text
D⁺ ‖X‖₁[Δ]
  = re (tr (sign(X) Δ)) + ‖P_ker(X) Δ P_ker(X)‖₁.
```

### PR 3: locally integrable linear propagators

Construct the finite-dimensional Volterra/Peano--Baker propagator for
`L ∈ L¹_loc` and prove:

- existence and uniqueness of the absolutely continuous trajectory;
- the integral equation;
- `E_{s,s} = I` and the cocycle law;
- norm bounds and stability with respect to `L¹` perturbations.

This is not a Wolf PR.

### PR 4: locally integrable Lindblad propagators are CPTP

Build on PR 3 and the existing constant-generator GKSL API.  Approximate by
stepwise-constant generators and prove closure of Hermiticity preservation,
trace preservation, positivity, and complete positivity.

### PR 5: weak-* compact admissible controls

Define bounded controls whose values lie almost everywhere in a fixed compact
convex hull.  Prove weak-* sequential compactness and weak-* closedness of the
pointwise constraint using Mathlib's `WeakDual` Banach--Alaoglu API plus the
necessary `L∞` integration bridge.

### PR 6: weak-* continuity of controlled trajectories

For the finite-dimensional control-affine Lindblad equation, prove that
weak-* convergence of bounded controls implies uniform convergence of the
corresponding trajectories or propagators on compact time intervals.  The proof
should pass to the limit in the integral equation and use the stability and
Gronwall infrastructure from PR 3.

### PR 7: Q2 assembly

Extract a convergent admissible-control subsequence, pass to the trajectory
limit, and apply the trace-norm/contractivity theorem.

---

## Source policy for theorem documentation

Use the following attribution discipline in Lean docstrings and PR descriptions:

- **Wolf:** trace/Schatten norm definitions and variational duality; homogeneous
  semigroups; Duhamel/Dyson formulas; time-independent GKSL structure.
- **WMT:** Proposition 19's target derivative formula and its role in the driven
  Lindblad contractivity argument.
- **Kato:** degenerate first-order Hermitian eigenvalue perturbation.
- **External standard ODE source or direct proof:** locally integrable
  propagators.
- **Mathlib Banach--Alaoglu plus external control/functional analysis or direct
  proof:** weak-* compactness and control-to-trajectory continuity.

Do not cite Wolf for the non-autonomous propagator, weak-* control compactness,
or degenerate perturbation theorem.  Do not cite WMT's time-ordered exponential
sentence as if it were a proof of locally integrable propagator existence.

---

## Final status

| Question | Answer |
|---|---|
| Are all four analytic ingredients explicitly in Wolf? | **No.** |
| Is Wolf sufficient as the sole faithful formalization source? | **No.** |
| Did Mathlib v4.32 add any of the four missing turnkey APIs? | **No.** It adds useful weak-dual transport infrastructure, but no trace norm, non-autonomous propagator, admissible-control compactness theorem, or degenerate eigenvalue perturbation theorem. |
| Is there a useful Wolf-first PR? | **Yes:** rebase and complete the existing `feat/analysis-schatten-one` prototype into the general matrix trace norm and Chapter 8 §8.1 variational API. |
| Does the existing trace-norm prototype survive the v4.32 upgrade? | **Yes.** Its implementation commits compile successfully when cherry-picked onto upgraded `origin/main`. |
| Is the existing Wolf Chapter 7 semigroup API reusable? | **Yes:** constant-generator semigroups, Duhamel/Dyson, and GKSL are already substantially formalized. |
| Must locally integrable propagator existence be proved independently? | **Yes.** WMT only states it. |
| Must weak-* control compactness and trajectory continuity be developed independently? | **Yes.** |
| What is the primary source for degenerate perturbation? | **Kato, Chapter II §§5-6**, followed by a direct trace-norm corollary. |
