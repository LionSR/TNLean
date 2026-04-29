# TNLean

[![Lean Action CI](https://github.com/LionSR/TNLean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/LionSR/TNLean/actions/workflows/lean_action_ci.yml)
[![Compile blueprint](https://github.com/LionSR/TNLean/actions/workflows/blueprint.yml/badge.svg)](https://github.com/LionSR/TNLean/actions/workflows/blueprint.yml)
![sorries](https://img.shields.io/endpoint?url=https://sirui-lu.com/TNLean/badges/sorries.json)
![axioms](https://img.shields.io/endpoint?url=https://sirui-lu.com/TNLean/badges/axioms.json)
![Lean](https://img.shields.io/endpoint?url=https://sirui-lu.com/TNLean/badges/lean.json)
![Mathlib](https://img.shields.io/endpoint?url=https://sirui-lu.com/TNLean/badges/mathlib.json)

A Lean 4 formalization of major components of the **Fundamental Theorem of Matrix Product States**, the repository's **cumulative Quantum Wielandt theory**, and a growing body of finite-dimensional **quantum-channel theory** inspired by M. M. Wolf's *Quantum Channels & Operations*, using [Mathlib](https://github.com/leanprover-community/mathlib4) v4.29.0.

## Overview

[Matrix Product States](https://en.wikipedia.org/wiki/Matrix_product_state) (MPS) — equivalently, Tensor Networks with one-dimensional geometry — are a central tool in quantum information theory and condensed matter physics. The **Fundamental Theorem of MPS** states that two MPS tensors generating the same family of quantum states must be related by a gauge transform. The **Quantum Wielandt Bound** gives a constructive upper bound on the length needed for products of matrices to span the full algebra. On the MPS side, this repository formalizes the injective single-block theorem, substantial Perron–Frobenius / canonical-form infrastructure, and strong-hypothesis multi-block and canonical-form assembly theorems, but not yet a full arbitrary-tensor → final canonical-form / biCF pipeline matching Section 2 + Appendix A of [arXiv:1606.00608](https://arxiv.org/abs/1606.00608). In parallel, the channel side now includes Choi/Kraus/Stinespring representation theory, a substantial Chapter-5 Schwarz package, a broad Chapter-6 spectral / fixed-point package, and a near-complete Chapter-7 semigroup / GKSL package.

## Current Status

Done in Lean today:

- injective single-block FT
- arbitrary tensor → irreducible block decomposition
- density-matrix Brouwer, Perron–Frobenius eigenvector existence, and TP-gauge normalization for irreducible blocks (no project-specific PF / Brouwer axiom remains on the main path)
- CFII / diagonal fixed-point data and periodicity removal by blocking
- canonical-form / CF-BNT theorems under stated structural hypotheses, including
  the same-structure equal-MPV theorem and the proportional theorem with
  explicit hypotheses on convergence of the relevant overlap coefficients
- the cumulative `D²` Wielandt bound for the project's `IsNormal` notion
- periodic tensor definitions for the irreducible-form theory (`IsPeriodic`, `IsIrreducibleForm`, `ZGaugeEquiv`, `RepeatedBlocks`)
- translation-invariance corollary for injective MPS chains (`ti_tensors_collapse_to_single_gauge`)
- blocked normal-chain FT endpoint via `IsNBlkInjective` bridge (`isNBlkInjective_iff_blockTensor_isInjective`)
- physical-rotation symmetry corollary: physical `u`-action on MPS implies virtual Z-gauge equivalence (`gaugeEquiv_of_sameMPV_rotatePhysical`; Corollary 4.1 of [arXiv:1708.00029](https://arxiv.org/abs/1708.00029))
- SameState-to-SameMPV bridge interface for injective chains (`SameStateBridgeHyp`), providing `fundamentalTheorem_injective_chain_of_sameState` as a weaker-hypothesis chain FT endpoint; the actual proof that `SameState` implies `SameMPV` is packaged as an abstract hypothesis rather than a completed argument
- `physRealize_mul` for general injective tensors: the physical realization map is multiplicative
- periodic blocking helper API in `MPS/Irreducible/PeriodicBlocking.lean` (`periodicBlockCount`, `periodicBlockPeriod`, `orbitSumProjection`, `blockedSectorProjection`; Lemma 2.4–2.5 bookkeeping infrastructure)
- on-site symmetry definitions (`IsOnSiteSymmetric`, `twistedTensor`) and gauge uniqueness for injective tensors (`gauge_unique_up_to_scalar`: two gauge equivalences of the same injective tensor are related by a scalar)
- renormalization fixed-point definitions (`IsRFP` from arXiv:1606.00608 Def 3.2) and `isRFP_iff_kraus_isometry` (Thm 3.1); structural-form theorems `rfp_cf_structural` and `rfp_bnt_structural` proved as reductions from the `rfp_nt_structural` sorry (rank-1 transfer map, requires rectangular Kraus freedom); zero-correlation-length predicates (`IsCID`, `IsLocallyOrthogonal`, `IsZCL`) and ZCL equivalence theorem (`zcl_iff_idempotent_transfer`) formalized in `MPS/RFP/ZeroCorrelationLength.lean`; reverse direction of Theorem 3.8 (`isCID_implies_isRFP`) proved sorry-free: a tensor with a PosDef fixed point and correlations independent of distance is a renormalization fixed point
- parent Hamiltonian with real orthogonal projector implementation (`parentHamiltonian`, `IsFrustrationFree`, `localTerm`); `parentHamiltonian_annihilates` and `parentHamiltonian_frustrationFree` proved; ground-space intersection property (`IntersectionProperty.lean`) and unique ground state infrastructure (`UniqueGroundState.lean`): `chainGroundSpace_eq_mpvSubmodule` proved sorry-free for `IsInjective` tensors (the IsNBlkInjective analogue remains sorry'd); commuting parent Hamiltonians and decorrelation theorem backward direction (`Commuting.lean`, `Decorrelation.lean`)
- exploratory PEPS definitions on finite simple graphs (`TNLean/PEPS/Defs.lean`): `Tensor`, `stateCoeff`, `SameState`, `IsVertexInjective`; scaffold for the Fundamental Theorem for injective PEPS (`TNLean/PEPS/FundamentalTheorem.lean`, refs arXiv:1804.04964 Thm 2): definitions `edgeGaugeAt`, `gaugeVertex`, `applyGauge`, `GaugeEquiv`, `localTensorEval`, and theorems `applyGauge_stateCoeff`, `GaugeEquiv.sameState`, `localGauge_exists`, `gaugeConsistency`, `fundamentalTheorem_PEPS`, `gauge_unique_up_to_scalar` (all proofs sorry'd pending the full argument)
- finite-length FT variant: for injective tensors, `SameMPV` can be weakened to `SameMPVFrom N₀` for any finite threshold N₀ (`MPS/FundamentalTheorem/FiniteLength.lean`; core propagation proof carries a sorry)
- QPF with relaxed injectivity: quantum Perron-Frobenius holds under `IsIrreducibleMap (transferMap A)`, not just `IsInjective A`, exposing the natural generality of Wolf Theorem 6.3 and applying to blocked tensors (`QPF/Primitive.lean`)
- primitive proportional FT convenience wrapper: `gaugePhaseEquiv_of_proportionalMPV₂_of_isPrimitiveMPS` reduces the 7-hypothesis proportional form to 4 by composing irreducibility, left-canonicality, and overlap-convergence from `IsPrimitiveMPS` (`MPS/FundamentalTheorem/ProportionalPrimitive.lean`)
- periodic fundamental theorem infrastructure: `fundamentalTheorem_periodic_proportional` (Theorem 3.4, arXiv:1708.00029) proved conditionally on `PeriodicOverlapHypothesis`; Z-gauge construction helpers for the equal-case (Theorem 3.8 steps 5–7) proved sorry-free (`MPS/FundamentalTheorem/Periodic.lean`)
- periodic overlap dichotomy: `periodicOverlapDichotomy` (Proposition 3.3, arXiv:1708.00029) stated with type-correct hypotheses; core proof bodies are sorry'd pending the full argument (`MPS/FundamentalTheorem/PeriodicOverlap.lean`)
- MPO/MPDO/LPDO foundations: `MPOTensor`, `MPOTensor.IsMPDO`, `MPOTensor.IsLPDO`, transfer map, toMPSTensor bridge, and LPDO→Hermitian proved (`MPS/MPDO/Defs.lean`)
- string order and local symmetry: `twistedTransferMap`, `stringOrderParam`, `IsLocalSymmetry`, `condC2_iff_condC3`, `condC1_imp_condC2`, and `stringOrder_iff_localSymmetry` stated; spectral-theory proofs (requiring canonical fixed-point primitivity) carry sorry stubs (`MPS/Symmetry/StringOrder.lean`)
- virtual symmetry equation: `virtual_symmetry_eq` — injective MPS with on-site symmetry U(g) admits virtual representatives X(g) satisfying the conjugation equation (`MPS/Symmetry/SymmetricMPS.lean`)
- scalar 2-cocycle cohomology: `ScalarCocycle.IsCoboundary`, `CohomologousTo`, `H2` quotient, `ProjectivelyEquivalent`, and `projRep_equiv_iff_cohomologous` (`Algebra/CocycleCohomology.lean`); gauge independence `cohomologousTo_of_isInjective` (`MPS/Symmetry/CocycleCoboundary.lean`)

Remaining formalization targets:

- prove the canonical-form theorem for an arbitrary tensor, matching Section 2
  and Appendix A of [arXiv:1606.00608](https://arxiv.org/abs/1606.00608)
- prove that the primitive blocks obtained after trace-preserving normalization
  and Canonical Form II normalization satisfy the block-injectivity and
  normality hypotheses required by the final canonical-form predicate
- complete the multi-block proportional theorem for periodic tensors, including
  the hypotheses asserting convergence of the overlap coefficients needed to
  assemble the block gauges

Complementary quantum-channel milestones now in Lean:

- Choi, Kraus, and Stinespring representation results from Wolf Chapter 2, including existential Stinespring dilation theorems (`exists_stinespring_dilation`, `exists_stinespring_isometry_of_cptp`; Wolf Thm 2.2 in both Heisenberg and Schrödinger pictures)
- Wolf Proposition 5.1, Theorems 5.5–5.7, and Example 5.3 in the Schwarz package
- Wolf Theorem 6.1 together with substantial Chapter-6 spectral / fixed-point theory, including Theorems 6.12–6.13, the stationary-support package (Lemma 6.4, Proposition 6.9, `stationaryState`, `stationarySupport`), the full bidirectional equivalence for Wolf Theorem 6.2 item 3 (irreducibility ↔ exponential semigroup strict positivity, `irreducible_iff_exp_posDef_forall`), Propositions 6.6/6.8 (similarity invariance of irreducibility, Hermitian fixed-point decomposition; `wolf_prop_6_6`, `wolf_prop_6_8`), and Theorem 6.15 scalar conditional expectation (`Kraus.wolf_theorem_6_15_scalar`)
- Wolf Chapter-7 semigroup / GKSL package through Proposition 7.6 and Theorem 7.2, Proposition 7.5 (irreducible implies primitive for QDS), and a partial non-reducibility criterion for Corollary 7.2; the full convergence statement of Corollary 7.2 remains unformalized
- `IsNPositiveMap` hierarchy (n-positive maps) and `kadison_schwarz_2positive` for unital 2-positive maps (Kadison 1952, Choi 1974), generalizing the CP-based Kadison–Schwarz result (`Channel/Schwarz/TwoPositive.lean`; connection from CP through 2-positive to Kadison–Schwarz carries partial sorry stubs)
- peripheral eigenvalue group structure (`PeripheralSpectrum` namespace, `Channel/Peripheral/GroupStructure.lean`): peripheral eigenvalues of irreducible channels form a cyclic group with period dividing dimension (Wolf Thm 6.6, `peripheral_eigenvalues_form_cyclic_group`, `channel_period_divides_dim` proved); multiplicity-one result (`peripheral_eigenvalue_multiplicity_one`) proved sorry-free; product closure of peripheral eigenvalues proved sorry-free in `Channel/Peripheral/CyclicGroup.lean`
- spectral gap of injective channels (`spectral_gap_of_injective`), exponential convergence of injective primitive channels (`exponential_convergence_of_primitive`), and correlation length bound (`correlation_length_bound`) all proved sorry-free in `Spectral/QuantitativeGap.lean`

### Wolf quantum-channel snapshot (audit of 2026-03-26)

| Wolf chapter | Topic | Estimated theorem-level coverage |
|---|---|---:|
| Ch1 | Deconstructing quantum | ~18% |
| Ch2 | Representations | ~13% |
| Ch3 | Positive not completely positive | 0% |
| Ch4 | Convex structure | equation-only |
| Ch5 | Schwarz inequalities | ~23% |
| Ch6 | Spectral properties | ~50% |
| Ch7 | Semigroup structure | ~95% |
| Ch8 | Distance measures | 0% |

## Main Results

### Single-Block Fundamental Theorem

```lean
theorem fundamentalTheorem_singleBlock {A B : MPSTensor d D}
    (hA : IsInjective A) (hAB : SameMPV A B) : GaugeEquiv A B
```

If an MPS tensor `A` is *injective* (its matrices span the full matrix algebra) and `B` generates the same MPV family, then `B i = X * A i * X⁻¹` for some invertible `X`.

### Multi-Block Assembly from Per-Block SameMPV

```lean
theorem fundamentalTheorem_multiBlock_full
    (μ : Fin r → ℂ) (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame : ∀ k, SameMPV (A k) (B k)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)
```

This is a same-structure assembly theorem: once each block pair is known to have the same MPV family, Lean produces both the per-block gauge transforms and the global gauge equivalence of the block-diagonal tensors. It is **not** a raw `SameMPV₂` separation theorem.

### Same-Structure CF-BNT Equal-MPV Theorem

```lean
theorem fundamentalTheorem_equalMPV_CFBNT
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : IsCanonicalFormBNT μ A) (hB : IsCanonicalFormBNT μ B)
    (hSame : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)) :
    (∀ k, GaugeEquiv (A k) (B k)) ∧
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)
```

This is the equal-MPV canonical-form theorem currently available in Lean: both sides already share the same block count, the same block dimensions, and the same `μ` data.

### Proportional CF-BNT Theorem with Explicit Coefficient Data

```lean
theorem fundamentalTheorem_proportionalMPV_CFBNT
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A) (hB : IsCanonicalFormBNT μB B)
    (A_total : MPSTensor d DtotA) (B_total : MPSTensor d DtotB)
    (aCoeff bCoeff ... ) (aLim bLim ... ) (c cLim ...)
    (hA_decomp ...) (hB_decomp ...)
    (haCoeff ...) (hbCoeff ...) (haLim_ne ...) (hbLim_ne ...)
    (hProp ...) (hc ...) (hcLim_ne ...) :
    ∃ h : rA = rB, ∃ perm : Fin rA ≃ Fin rB, ...
```

This is the current proportional-case top theorem in Lean. The decomposition
coefficients, their convergence, and their nonvanishing data are explicit
hypotheses; the present formalization has not yet derived them from arbitrary
input tensors.

### Cumulative Quantum Wielandt Bound

```lean
theorem cumulative_wielandt_bound [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    cumulativeSpan A (D ^ 2) = ⊤
```

For the project's `IsNormal` notion, products of the matrices of `A` of length at most `D²` cumulatively span the full matrix algebra `M_D(ℂ)`.

### Perron–Frobenius Eigenvector Existence

```lean
theorem exists_posSemidef_eigenvector [NeZero D]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hpos : IsPositiveMap E)
    (hNZ : ∀ {ρ}, ρ.PosSemidef → ρ ≠ 0 → E ρ ≠ 0) :
    ∃ ρ r, ρ.PosSemidef ∧ ρ ≠ 0 ∧ 0 < r ∧ E ρ = (r : ℂ) • ρ
```

This is the positive-map Perron–Frobenius step used later to build TP gauges for irreducible tensors. Its proof now goes through a proved Brouwer theorem on density matrices rather than a project-specific axiom.

## Building

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
lake build
```

Requires Lean 4 v4.29.0 (managed via `lean-toolchain`).

For repository-specific migration notes about the Lean/Mathlib 4.29 upgrade, see
[docs/upgrade_4_29.md](docs/upgrade_4_29.md).

## Blueprint

The repository ships a LeanBlueprint in `blueprint/` covering both the MPS development and the Wolf quantum-channel material. As of 2026-04-07, the blueprint chapters `ch02b_mpdo.tex`, `ch04_channels.tex`, `ch05_schwarz.tex`, `ch06_spectral.tex`, `ch07_wielandt.tex`, `ch08_canonical.tex`, `ch11_assembly.tex`, `ch12_semigroup.tex`, `ch13_algebraic_ft.tex`, `ch13b_symmetry.tex`, `ch14_parent_hamiltonian.tex`, and `ch15_correlations.tex` have been synchronized to reflect current Lean status, including the stationary-support package, periodic tensor definitions, semigroup sorry closures, MPDO foundations, symmetry / string-order / coboundary entries, chain FT declarations, quantitative spectral gap / correlation decay results, PEPS FT scaffold definitions, and the `isCID_implies_isRFP` reverse direction entry.

Typical blueprint commands:

```bash
lake build TNLean
cd blueprint
leanblueprint checkdecls
leanblueprint web   # or: leanblueprint pdf / leanblueprint all
```

The blueprint tooling assumes that the Lean project itself builds successfully; if you are working with local experimental edits, rebuild the affected Lean modules before running `checkdecls`.

## References

The formalization follows these papers:

- D. Pérez-García, F. Verstraete, M. M. Wolf, J. I. Cirac, *Matrix Product State Representations*, [arXiv:quant-ph/0608197](https://arxiv.org/abs/quant-ph/0608197), Quantum Inf. Comput. **7** (2007) — original MPS fundamental theorem, support projector arguments, irreducible form
- M. Sanz, D. Pérez-García, M. M. Wolf, J. I. Cirac, *A quantum version of Wielandt's inequality*, [arXiv:0909.5347](https://arxiv.org/abs/0909.5347), J. Math. Phys. **51**, 102205 (2010) — quantum Wielandt bound
- J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, *Matrix Product Density Operators*, [arXiv:1606.00608](https://arxiv.org/abs/1606.00608), Annals of Physics **378** (2017) — MPDO canonical form, irreducible decomposition (Appendix A)
- G. De las Cuevas, J. I. Cirac, N. Schuch, D. Pérez-García, *Irreducible forms of Matrix Product States: Theory and Applications*, [arXiv:1708.00029](https://arxiv.org/abs/1708.00029), J. Math. Phys. **58**, 121901 (2017) — irreducible forms, Gram matrix characterization
- J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, *Matrix Product States and Projected Entangled Pair States*, [arXiv:2011.12127](https://arxiv.org/abs/2011.12127), Rev. Mod. Phys. **93**, 045003 (2021) — review, Theorem 4.4 (proportional MPV), BNT permutation structure
- A. Molnár, N. Schuch, F. Verstraete, J. I. Cirac, *Fundamental theorem for injective projected entangled pair states*, [arXiv:1804.04964](https://arxiv.org/abs/1804.04964) (2018) — PEPS fundamental theorem, Section 3
- M. M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012) — representation theory, positive maps, Schwarz inequalities, spectral theory, and semigroups
- [Mathlib4](https://github.com/leanprover-community/mathlib4) — Lean 4 mathematics library
