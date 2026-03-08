# TNLean

A Lean 4 formalization of major components of the **Fundamental Theorem of Matrix Product States** and the repository's **cumulative Quantum Wielandt theory**, using [Mathlib](https://github.com/leanprover-community/mathlib4) v4.28.0.

## Overview

[Matrix Product States](https://en.wikipedia.org/wiki/Matrix_product_state) (MPS) — equivalently, Tensor Networks with one-dimensional geometry — are a central tool in quantum information theory and condensed matter physics. The **Fundamental Theorem of MPS** states that two MPS tensors generating the same family of quantum states must be related by a gauge transform. The **Quantum Wielandt Bound** gives a constructive upper bound on the length needed for products of matrices to span the full algebra. This repository currently formalizes the injective single-block theorem, substantial Perron–Frobenius / canonical-form infrastructure, and strong-hypothesis multi-block and canonical-form assembly theorems, but not yet a full arbitrary-tensor → final canonical-form / biCF pipeline matching Section 2 + Appendix A of [arXiv:1606.00608](https://arxiv.org/abs/1606.00608).

## Current Status

Done in Lean today:

- injective single-block FT
- arbitrary tensor → irreducible block decomposition
- density-matrix Brouwer, Perron–Frobenius eigenvector existence, and TP-gauge normalization for irreducible blocks (no project-specific PF / Brouwer axiom remains on the main path)
- CFII / diagonal fixed-point data and periodicity removal by blocking
- strong-hypothesis canonical-form / CF-BNT theorems, including the same-structure equal-MPV theorem and the proportional theorem with explicit coefficient-convergence data
- the cumulative `D²` Wielandt bound for the project's `IsNormal` notion

Still not assembled end-to-end:

- arbitrary tensor → final repository canonical form / biCF theorem matching Section 2 + Appendix A of [arXiv:1606.00608](https://arxiv.org/abs/1606.00608)
- the bridge from primitive blocked TP / CFII data to the stronger block-injective / `IsNormal` hypotheses used by the final canonical-form predicate
- the fully automatic multi-block proportional assembly in the oscillatory / coefficient-convergence regime

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

## References

The formalization follows these papers:

- D. Pérez-García, F. Verstraete, M. M. Wolf, J. I. Cirac, *Matrix Product State Representations*, [arXiv:quant-ph/0608197](https://arxiv.org/abs/quant-ph/0608197), Quantum Inf. Comput. **7** (2007) — original MPS fundamental theorem, support projector arguments, irreducible form
- M. Sanz, D. Pérez-García, M. M. Wolf, J. I. Cirac, *A quantum version of Wielandt's inequality*, [arXiv:0909.5347](https://arxiv.org/abs/0909.5347), J. Math. Phys. **51**, 102205 (2010) — quantum Wielandt bound
- J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, *Matrix Product Density Operators*, [arXiv:1606.00608](https://arxiv.org/abs/1606.00608), Annals of Physics **378** (2017) — MPDO canonical form, irreducible decomposition (Appendix A)
- G. De las Cuevas, J. I. Cirac, N. Schuch, D. Pérez-García, *Irreducible forms of Matrix Product States: Theory and Applications*, [arXiv:1708.00029](https://arxiv.org/abs/1708.00029), J. Math. Phys. **58**, 121901 (2017) — irreducible forms, Gram matrix characterization
- J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, *Matrix Product States and Projected Entangled Pair States*, [arXiv:2011.12127](https://arxiv.org/abs/2011.12127), Rev. Mod. Phys. **93**, 045003 (2021) — review, Theorem 4.4 (proportional MPV), BNT permutation structure
- M. M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012) — positive map spectral theory, Kadison–Schwarz inequality
- [Mathlib4](https://github.com/leanprover-community/mathlib4) — Lean 4 mathematics library
