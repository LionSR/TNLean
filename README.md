# TNLean

[![Lean Action CI](https://github.com/LionSR/TNLean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/LionSR/TNLean/actions/workflows/lean_action_ci.yml)
[![Compile blueprint](https://github.com/LionSR/TNLean/actions/workflows/blueprint.yml/badge.svg)](https://github.com/LionSR/TNLean/actions/workflows/blueprint.yml)

A Lean 4 formalization of major components of the **Fundamental Theorem of Matrix Product States**, the repository's **cumulative Quantum Wielandt theory**, and a growing body of finite-dimensional **quantum-channel theory** inspired by M. M. Wolf's *Quantum Channels & Operations*, using [Mathlib](https://github.com/leanprover-community/mathlib4) v4.28.0.

## Overview

[Matrix Product States](https://en.wikipedia.org/wiki/Matrix_product_state) (MPS) — equivalently, Tensor Networks with one-dimensional geometry — are a central tool in quantum information theory and condensed matter physics. The **Fundamental Theorem of MPS** states that two MPS tensors generating the same family of quantum states must be related by a gauge transform. The **Quantum Wielandt Bound** gives a constructive upper bound on the length needed for products of matrices to span the full algebra. On the MPS side, this repository formalizes the injective single-block theorem, substantial Perron–Frobenius / canonical-form infrastructure, and strong-hypothesis multi-block and canonical-form assembly theorems, but not yet a full arbitrary-tensor → final canonical-form / biCF pipeline matching Section 2 + Appendix A of [arXiv:1606.00608](https://arxiv.org/abs/1606.00608). In parallel, the channel side now includes Choi/Kraus/Stinespring representation theory, a substantial Chapter-5 Schwarz package, a broad Chapter-6 spectral / fixed-point package, and a near-complete Chapter-7 semigroup / GKSL package.

## Current Status

Done in Lean today:

- injective single-block FT
- arbitrary tensor → irreducible block decomposition
- density-matrix Brouwer, Perron–Frobenius eigenvector existence, and TP-gauge normalization for irreducible blocks (no project-specific PF / Brouwer axiom remains on the main path)
- CFII / diagonal fixed-point data and periodicity removal by blocking
- strong-hypothesis canonical-form / CF-BNT theorems, including the same-structure equal-MPV theorem and the proportional theorem with explicit coefficient-convergence data
- the cumulative `D²` Wielandt bound for the project's `IsNormal` notion
- injective chain FT for non-translation-invariant periodic chains (`MPSChainTensor.fundamentalTheorem_injective_chain`) and its TI-collapse corollary (`MPSChainTensor.ti_tensors_collapse_to_single_gauge`); a blocked-chain endpoint (`MPSChainTensor.fundamentalTheorem_blockedChain`) bridges `IsNBlkInjective` to the chain theorem

Still not assembled end-to-end:

- arbitrary tensor → final repository canonical form / biCF theorem matching Section 2 + Appendix A of [arXiv:1606.00608](https://arxiv.org/abs/1606.00608)
- the bridge from primitive blocked TP / CFII data to the stronger block-injective / `IsNormal` hypotheses used by the final canonical-form predicate
- the fully automatic multi-block proportional assembly in the oscillatory / coefficient-convergence regime

Complementary channel-side milestones now in Lean:

- Choi, Kraus, and Stinespring representation results from Wolf Chapter 2
- Wolf Proposition 5.1, Theorems 5.5–5.7, and Example 5.3 in the Schwarz package
- Wolf Theorem 6.1 together with substantial Chapter-6 spectral / fixed-point theory, including Theorems 6.12–6.13
- Wolf Chapter-7 semigroup / GKSL package through Proposition 7.6 and Theorem 7.2; only Corollary 7.2 remains unformalized

### Wolf channel-side snapshot (audit of 2026-03-19)

| Wolf chapter | Topic | Estimated theorem-level coverage |
|---|---|---:|
| Ch1 | Deconstructing quantum | ~18% |
| Ch2 | Representations | ~13% |
| Ch3 | Positive not completely positive | 0% |
| Ch4 | Convex structure | equation-only |
| Ch5 | Schwarz inequalities | ~23% |
| Ch6 | Spectral properties | ~44% |
| Ch7 | Semigroup structure | ~91% |
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

This is the current proportional-case top theorem in Lean. The decomposition coefficients and their convergence / nonvanishing data are explicit hypotheses; Lean does not yet derive them automatically from arbitrary raw input tensors.

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

Requires Lean 4 v4.28.0 (managed via `lean-toolchain`).

## Blueprint

The repository ships a LeanBlueprint in `blueprint/` covering both the MPS development and the channel-side Wolf material. After the 2026-03-23 documentation sync, the blueprint chapters `ch04_channels.tex`, `ch05_schwarz.tex`, `ch06_spectral.tex`, `ch11_assembly.tex`, `ch12_semigroup.tex`, and `ch13_algebraic_ft.tex` reflect the current Lean status of the representation, Schwarz, spectral / stationary-support, periodic-tensor assembly, semigroup, and algebraic chain-FT packages.

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
- M. M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012) — representation theory, positive maps, Schwarz inequalities, spectral theory, and semigroups
- [Mathlib4](https://github.com/leanprover-community/mathlib4) — Lean 4 mathematics library
