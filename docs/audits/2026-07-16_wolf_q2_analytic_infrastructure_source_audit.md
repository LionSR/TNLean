# Source audit: analytic infrastructure for the Q2 proof

**Date:** 2026-07-16

**Updated:** 2026-07-27

**Question:** Which parts of the Q2 proof are supplied by Michael M. Wolf's
lecture notes, and which analytic results require other sources or direct
proofs?

**Primary source:** Michael M. Wolf, *Quantum Channels & Operations: Guided
Tour*, July 5, 2012.

**Comparison source:** Lasse H. Wolff, Daniel Malz, and Rahul Trivedi,
*Contractivity of time-dependent driven-dissipative systems*,
arXiv:2602.16067v1, February 17, 2026, abbreviated **WMT**.

**Repository transcription:** `Notes/WolfNoteTexSource/`.

**Current formalization snapshot:** `origin/main` at commit `8cbb6217f`, with
Lean 4.32.0 and Mathlib revision
`81a5d257c8e410db227a6665ed08f64fea08e997`.

## Executive conclusion

Wolf supplies the static finite-dimensional trace-norm theory and the
homogeneous, time-independent semigroup theory relevant to Q2. He does not
supply the other analytic ingredients used by the proof.

1. Chapter 8, Section 8.1 defines the trace norm and gives its absolute-value
   and variational descriptions. The corresponding foundational results,
   including the triangle inequality and trace-norm contractivity of positive
   trace-preserving maps on Hermitian inputs, are already formalized on current
   `origin/main`.
2. Wolf does not prove the one-sided directional derivative of the trace norm
   at a singular Hermitian matrix.
3. Chapter 7 treats fixed generators and one-parameter semigroups. It does not
   construct propagators for locally integrable time-dependent generators.
4. Wolf contains no weak-* compactness theorem for convex-valued measurable
   controls and no weak-* continuity theorem for the corresponding
   trajectories.
5. Chapter 6 develops static spectral calculus, but not first-order splitting
   of a degenerate Hermitian eigenvalue.

WMT Proposition 19 states the trace-norm right-derivative formula used in its
contractivity argument. Its proof invokes finite-dimensional perturbation
theory and contains a regularity issue that must be treated explicitly in a
formal proof. WMT also writes the locally integrable evolution as a time-ordered
exponential, but does not prove the existence, uniqueness, cocycle, stability,
or positivity results needed for Q2.

The next trace-norm contribution should therefore start from the four modules
already imported by `TNLean/Analysis.lean`:

- `TNLean/Analysis/SchattenNorm.lean`;
- `TNLean/Analysis/TraceNormAbs.lean`;
- `TNLean/Analysis/TraceNormVariational.lean`;
- `TNLean/Analysis/TraceNormContractivity.lean`.

It should add the Hermitian directional-derivative theory rather than recreate
the trace-norm foundation.

## Exact source and version

The TNLean bibliographies identify Wolf's notes in
`blueprint/src/references.bib:51-58` and
`docs/paper-gaps/references.bib:178-185`. The archived title page gives the
version date July 5, 2012. The second page warns that parts of the notes remain
incomplete or erroneous, so this audit distinguishes definitions, collected
statements, proof sketches, and full proofs.

The Chapter 8 transcription is
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`. Its header says that the
transcription is partial and stops at the heading of Section 8.8. The archived
PDF was therefore also checked for absence claims. Printed theorem numbers in
this audit refer to the July 5, 2012 PDF. Local source locations refer to the
repository transcription and should be used to locate the text when the
transcription's automatic numbering differs from the printed notes.

WMT was checked against the LaTeX source of arXiv:2602.16067v1. In
`main_aps.tex`, the locally integrable evolution is introduced at lines 161-164,
Proposition 19 is stated at lines 624-636, and its appendix proof occupies lines
1053-1129. The perturbation step cites Kato, Section 2.6, at lines 1085-1089.
This audit verifies what WMT states and how it uses the citation. It does not
identify a theorem in Kato whose hypotheses and conclusion already match the
exact Lean statement; that theorem-level source check remains part of the
directional-derivative work.

The formalization inventory below was recomputed from current `origin/main`,
not from an earlier feature branch. Both `lean-toolchain` and
`lake-manifest.json` record the Lean/Mathlib 4.32.0 upgrade at this snapshot.

## Coverage table

| Q2 ingredient | Wolf location and proof status | WMT location and proof status | Current Mathlib/TNLean support | Remaining formalization | Source recommendation |
|---|---|---|---|---|---|
| **Matrix trace norm** | Chapter 8, Section 8.1, printed pp. 131-133; local lines 63-202. Wolf defines Schatten norms and the trace norm, states `‖A‖₁ = tr |A|`, and gives a variational formula. Some Section 8.1 arguments are sketches. Theorem 8.16, local lines 898-918, proves contractivity of positive trace-preserving maps on Hermitian matrices. | Proposition 19, lines 624-636, uses the trace norm along a driven Lindblad trajectory. The appendix proof, lines 1053-1129, invokes first-order perturbation theory. | Mathlib supplies singular values and finite-dimensional spectral calculus. Current TNLean defines `Matrix.traceNorm`, proves `‖A‖₁ = Re tr |A|`, scalar homogeneity, two-sided unitary invariance, the attained unitary variational formula, the triangle inequality, and trace-norm contractivity for positive trace-preserving maps on Hermitian inputs. All four trace-norm modules are imported by `TNLean/Analysis.lean`. | A Hermitian eigenvalue formula convenient for differentiation; matrix sign and kernel compression; the one-sided directional derivative at singular matrices; commutator cancellation in that derivative. A bundled norm structure and operator-norm duality may be useful, but are not prerequisites for the Q2 derivative if the Hermitian variational formula is proved directly. | Wolf for definitions, variational facts, and contractivity; a theorem-level perturbation source or direct finite-dimensional proof for the derivative; WMT Proposition 19 as the downstream application. |
| **Locally integrable linear and Lindblad propagators** | Absent. Chapter 7 proves the fixed-generator semigroup law, the exponential representation, Duhamel's formula, the Dyson--Phillips expansion, and time-independent GKSL structure. | At line 164 WMT says that local integrability gives a unique solution and writes `E_{t,s} = T exp(∫ L_τ dτ)`. No construction or proof is supplied there. | Mathlib has Bochner integration, Grönwall inequalities, and ordinary differential-equation results for more regular vector fields. TNLean has `expSemigroupCLM`, fixed-generator differentiation, Duhamel bounds, Dyson--Phillips results, and time-independent Lindblad structure. No current module constructs the required evolution family for an `L¹_loc` coefficient. | Existence and uniqueness of absolutely continuous trajectories; the Volterra integral equation; identity and cocycle laws; norm and `L¹` stability bounds; approximation by step coefficients; Hermiticity, trace, positivity, and complete-positivity preservation. | A standard Carathéodory linear-ODE source or a direct finite-dimensional Volterra proof. Use Wolf only for the constant-generator specialization and WMT only for the intended notation and application. |
| **Weak-* compact convex-valued controls and trajectory continuity** | Absent. Chapter 4 treats finite-dimensional convex optimization and semidefinite programming, not weak-* compactness of measurable controls. | Absent. WMT quantifies over locally integrable Hamiltonians but does not prove compactness of an admissible control class or continuity under weak-* convergence. | Mathlib provides `WeakDual.isCompact_closedBall`, `WeakDual.isSeqCompact_closedBall`, and `ContinuousLinearMap.lpPairing`. TNLean proves finite-dimensional compactness of convex hulls in `TNLean/Analysis/ConvexHullCompact.lean`. There is no current theorem giving weak-* compactness of the almost-everywhere convex constraint or uniform convergence of controlled trajectories. | A concrete finite-dimensional representation of the `L∞` control space in a weak dual; weak-* closedness of the pointwise convex constraint; measurable representatives; uniform trajectory bounds and equicontinuity; passage to the limit in the control-affine integral equation. | Mathlib Banach--Alaoglu and `lpPairing`, together with a standard optimal-control or functional-analysis source and a direct finite-dimensional trajectory proof. Do not cite Wolf or WMT for this step. |
| **Degenerate Hermitian first-order perturbation** | Absent. Chapter 6, local lines 286-332, contains resolvents, contour spectral projections, and holomorphic functional calculus, but not first-order splitting inside a degenerate eigenspace. | Used in the proof of Proposition 19 at lines 1085-1089 and again near lines 1171-1175. WMT describes diagonalizing the compressed perturbation on each degenerate eigenspace and cites Kato, Section 2.6. | Mathlib and TNLean provide Hermitian spectral decompositions, eigenvalue enumerations, support projections, positive and negative parts, and extremal-eigenvalue facts. No current declaration proves first-order degenerate eigenvalue splitting or the singular trace-norm derivative. | A theorem for the first-order eigenvalue shifts of `A + εB`, or a direct convex-analytic proof of the trace-norm directional derivative that avoids constructing individual eigenvalue branches. | Verify the exact theorem in Kato or another perturbation reference before citing it in theorem documentation. A direct finite-dimensional proof is also acceptable. WMT is an application sketch, not the foundational source. |

## Wolf source inventory

### Trace and Schatten norms

The relevant Chapter 8 material is in
`Notes/WolfNoteTexSource/ch08_distance_measures.tex`:

- Section 8.1, *Norms*, local lines 44-203;
- Schatten `p`-norm and Ky Fan `k`-norm definitions, lines 63-75;
- monotonicity of Schatten norms, Eq. (8.1), lines 77-85;
- `‖A‖₁ = tr |A|`, lines 86-95;
- Theorem 8.2, *Unitarily invariant norms*, local lines 106-142;
- trace Hölder inequality, Eq. (8.6), lines 144-148;
- Theorem 8.3 and the variational formulas, local lines 170-202;
- Theorem 8.16 and Eqs. (8.79)-(8.80), local lines 898-918.

Theorem 8.3 contains a proof sketch with an explicit ellipsis. Theorem 8.16
contains a proof. These distinctions should remain visible in declaration
documentation.

Nothing in this material states the derivative

```text
D⁺ ‖·‖₁(X;Y)
  = tr(sign(X)Y) + ‖P_ker(X) Y P_ker(X)‖₁
```

for singular Hermitian `X`.

### Homogeneous semigroups

`Notes/WolfNoteTexSource/ch07_semigroup_structure.tex` contains:

- the semigroup law, Eq. (7.1);
- the fixed-generator equation, Eq. (7.2);
- the exponential representation of a continuous finite-dimensional
  semigroup;
- Duhamel's formula, Eq. (7.10);
- the perturbation estimate, Eq. (7.12);
- the Dyson--Phillips expansion, Eq. (7.13);
- the time-independent quantum dynamical semigroup and GKSL results,
  Eqs. (7.14)-(7.23).

These results concern one fixed generator. The notes do not define a two-time
evolution family `E_{t,s}` for a merely locally integrable coefficient.

### Static spectral calculus

The resolvent discussion in
`Notes/WolfNoteTexSource/ch06_spectral_properties.tex:286-332` contains:

- the resolvent, Eq. (6.17);
- the resolvent series, Eq. (6.18);
- the contour spectral projection, Eq. (6.20);
- the holomorphic functional calculus, Eq. (6.21).

These are possible ingredients for perturbation theory. They do not state the
first-order splitting theorem used by WMT.

### No weak-* control theory

Chapter 4, Section 4.1 concerns finite-dimensional convex optimization,
Lagrange duality, and semidefinite programming. It contains no Banach--Alaoglu
theorem, `L∞` control space, relaxed-control compactness theorem, or weak-*
continuity theorem for trajectories.

## WMT Proposition 19 and the varying-direction issue

WMT Proposition 19 states that, for
`x(t) = E_{t,s}(ρ - σ)`, the function `‖x(t)‖₁` is right differentiable and gives
an explicit expression in an eigenbasis of `x(t)`. The appendix begins with

```text
x(t+ε) - x(t) = ε Δ_ε(t) + o(ε),
```

where

```text
Δ_ε(t) = (1/ε) ∫_[t,t+ε] (-i[H(τ),x(t)] + D x(t)) dτ.
```

It then applies the fixed-direction expansion

```text
‖x + εΔ‖₁ = ‖x‖₁
  + tr(sign(x) εΔ)
  + ‖ε Δ|_{ker x}‖₁
  + R_{x,Δ}(ε),
```

with `R_{x,Δ}(ε) = o(ε)` for fixed `x` and `Δ`.

The direction in the application is `Δ_ε(t)`, which depends on `ε`. Local
integrability of `H` does not give a uniform bound on every interval average
`ε⁻¹∫_[t,t+ε] H(τ)dτ` at every time. A remainder estimate established only for
each fixed direction cannot be substituted into this varying family without
an additional uniformity argument. Freezing `x(τ)` at `x(t)` also requires a
regularity estimate compatible with the stated hypotheses.

A formal proof can avoid this gap in several ways:

1. prove the formula first for bounded piecewise-continuous controls and pass to
   the required class by approximation;
2. pass to an interaction picture, where unitary invariance removes the
   Hamiltonian evolution before the trace norm is differentiated;
3. prove a perturbation remainder estimate uniform on the bounded family of
   directions that actually occurs;
4. use the convex directional derivative of the trace norm together with an
   absolutely continuous chain rule whose hypotheses are verified directly.

This caveat concerns the analytic passage to the time derivative. It does not
invalidate the finite-dimensional directional-derivative formula itself.

## Current TNLean inventory

The current `origin/main` inventory is as follows.

### Trace norm

- `TNLean/Analysis/SchattenNorm.lean`
  - defines `Matrix.schattenOneNorm` and `Matrix.traceNorm`;
  - proves finite-support and finite-dimensional singular-value sum formulas;
  - proves nonnegativity, definiteness, and strict positivity away from zero;
  - gives the sum of square roots of the eigenvalues of `A†A`.
- `TNLean/Analysis/TraceNormAbs.lean`
  - proves `Matrix.traceNorm_eq_re_trace_abs`;
  - proves scalar homogeneity;
  - proves left, right, and two-sided unitary invariance.
- `TNLean/Analysis/TraceNormVariational.lean`
  - proves the upper bound and attainment in Wolf's unitary variational
    formula;
  - identifies the trace norm as the corresponding supremum;
  - proves `Matrix.traceNorm_add_le`.
- `TNLean/Analysis/TraceNormContractivity.lean`
  - proves the positive/negative-part formula for Hermitian matrices;
  - proves trace-norm contraction under positive trace-preserving maps;
  - proves trace-distance contraction for two positive semidefinite inputs.

These modules were merged through PRs #4031, #4051, #4052, #4073, and #4078
and are imported by the generated `TNLean/Analysis.lean` aggregator. The audit
must not describe them as an unmerged or incomplete feature-branch snapshot.

### Fixed-generator semigroups

- `TNLean/Channel/Semigroup/Basic.lean` contains `expSemigroupCLM`, its
  derivative, and the exponential representation of continuous finite-
  dimensional semigroups.
- `TNLean/Channel/Semigroup/Perturbation.lean` contains Duhamel's formula,
  perturbation bounds, and the Dyson--Phillips expansion.
- `TNLean/Channel/Semigroup/LindbladForm/` and related modules contain the
  time-independent positivity and GKSL theory.
- `TNLean/Channel/Semigroup/HamiltonianIndependentContractivity.lean` proves
  algebraic facts surrounding WMT's question. Its module documentation
  explicitly excludes the full analytic HIC theorem.

### Compactness and spectral ingredients

- `TNLean/Analysis/ConvexHullCompact.lean` proves compactness of a convex hull
  in a finite-dimensional real normed space. It does not prove compactness of
  a set of measurable controls.
- `TNLean/Algebra/HermitianHelpers.lean` contains static extremal-eigenvalue and
  spectral-shift results, not first-order perturbation theory.
- `TNLean/Algebra/PosSemidefSupport.lean` supplies support projections and
  kernel absorption. These results are likely reusable in the singular
  directional-derivative proof.

## Recommended contribution sequence

### PR 1: Hermitian trace-norm spectral and sign formulas

Build directly on `SchattenNorm`, `TraceNormAbs`, `TraceNormVariational`, and
`PosSemidefSupport`. Add only the results needed to express the derivative on a
Hermitian matrix:

```lean
Matrix.IsHermitian.traceNorm_eq_sum_abs_eigenvalues
Matrix.IsHermitian.sign
Matrix.IsHermitian.kernelProj
Matrix.IsHermitian.trace_sign_mul
Matrix.IsHermitian.traceNorm_eq_max_orderInterval
```

The exact declaration names may follow the surrounding TNLean conventions.
The mathematical content should identify the sign and kernel projection by
Hermitian functional calculus and prove the order-interval variational formula
used by the Q2 source proof.

### PR 2: one-sided trace-norm directional derivative

Prove, for Hermitian `X` and `Y`,

```text
D⁺ ‖·‖₁(X;Y)
  = Re tr(sign(X)Y) + ‖P_ker(X) Y P_ker(X)‖₁.
```

Then prove the commutator cancellation and the specialization to a Lindblad
direction. Before citing Kato in declaration documentation, identify the exact
edition, theorem, and hypotheses. If the proof instead uses the variational
formula and finite-dimensional convex analysis, cite that source directly.

### PR 3: locally integrable linear propagators

For finite-dimensional `L ∈ L¹_loc`, construct the evolution family and prove:

- existence and uniqueness of absolutely continuous trajectories;
- the Volterra integral equation;
- `E_{s,s} = I` and the cocycle law;
- exponential norm bounds;
- stability under `L¹` perturbations.

This contribution is not sourced from Wolf.

### PR 4: locally integrable Lindblad propagators

Use stepwise-constant approximation and the existing fixed-generator Lindblad
theory to prove preservation of Hermiticity, trace, positivity, and complete
positivity. Apply `Matrix.traceNorm_map_le_of_positive_of_tracePreserving` to
obtain trace-norm contraction on Hermitian differences. This avoids reproving
the static contraction theorem inside the propagator development.

### PR 5: weak-* compact admissible controls

Represent the finite-dimensional `L∞` control space in a weak dual, prove
weak-* sequential compactness of bounded controls, and prove weak-* closedness
of the almost-everywhere compact convex constraint. The proof should state
precisely where `ContinuousLinearMap.lpPairing` and the weak-dual
Banach--Alaoglu theorems are used.

### PR 6: weak-* continuity of controlled trajectories

For a bounded finite-dimensional control-affine equation, prove that weak-*
convergence of controls implies uniform convergence of the corresponding
trajectories on compact intervals. Pass to the limit in the Volterra equation
and use the bounds from PR 3.

### PR 7: proof of uniform Hamiltonian-independent contractivity

Combine the compactness theorem, continuity of trajectories, the trace-norm
directional derivative, and the algebraic jump-generation argument to prove
the Q2 theorem. The proof should use the total weighted jump family at singular
matrices, because the trace-norm directional derivative is not linear in the
direction.

## Attribution policy

- Cite **Wolf Chapter 8** for the trace-norm definition, the absolute-value and
  variational descriptions, and Theorem 8.16 contractivity. Distinguish the
  Section 8.1 proof sketches from results with complete proofs.
- Cite **Wolf Chapter 7** only for fixed-generator semigroups, Duhamel and
  Dyson--Phillips formulas, and time-independent GKSL structure.
- Cite **WMT Proposition 19** for the target derivative formula and its role in
  the driven contractivity argument. Do not cite the time-ordered exponential
  sentence as a proof of propagator existence.
- Cite **Kato or another perturbation source** only after matching an exact
  theorem to the formal statement. WMT's citation to Kato, Section 2.6, is not
  by itself a theorem-level source check.
- Cite **Mathlib Banach--Alaoglu and `lpPairing` results**, together with an
  external control source or a direct proof, for weak-* compactness and
  trajectory continuity.
- Describe current TNLean support by modules on `origin/main`. Do not recommend
  restoring obsolete feature-branch commits whose content has already merged.

## Final status

| Question | Answer |
|---|---|
| Are all four analytic ingredients explicitly proved in Wolf? | **No.** Wolf covers the static trace norm and fixed-generator semigroups, but not the singular derivative, locally integrable propagators, weak-* control compactness, or degenerate first-order perturbation. |
| Is the trace-norm foundation already on the target branch? | **Yes.** `SchattenNorm`, `TraceNormAbs`, `TraceNormVariational`, and `TraceNormContractivity` are present on current `origin/main` and imported by `TNLean/Analysis.lean`. |
| Which trace-norm results are already formalized? | The singular-value definition, `Re tr |A|`, scalar homogeneity, unitary invariance, the attained unitary variational formula, the triangle inequality, and contractivity of positive trace-preserving maps on Hermitian inputs. |
| What trace-norm result remains central to Q2? | The one-sided directional derivative at a singular Hermitian matrix, including the compressed kernel term and commutator cancellation. |
| Does Mathlib provide the missing non-autonomous or control theorem directly? | **No result was found** for the required locally integrable evolution family, convex-valued weak-* compact controls, or weak-* continuity of trajectories. Mathlib does provide Bochner integration, Grönwall inequalities, weak-dual Banach--Alaoglu, and `lpPairing`. |
| Does WMT prove locally integrable propagator existence? | **No.** It states uniqueness and writes a time-ordered exponential at source line 164. |
| Is WMT Proposition 19 sufficient as a foundational derivative proof? | **Not without an additional regularity argument.** Its appendix inserts an `ε`-dependent averaged direction into a remainder estimate stated for a fixed direction. |
| What should the next contribution do? | Start from the trace-norm modules already on `origin/main` and prove the Hermitian sign, kernel-compression, and one-sided directional-derivative results. |
