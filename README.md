# TNLean

A formal verification of the **Fundamental Theorem of Matrix Product States** and the **Quantum Wielandt Bound** in Lean 4, using [Mathlib](https://github.com/leanprover-community/mathlib4) v4.28.0.

## Overview

[Matrix Product States](https://en.wikipedia.org/wiki/Matrix_product_state) (MPS) — equivalently, Tensor Networks with one-dimensional geometry — are a central tool in quantum information theory and condensed matter physics. The **Fundamental Theorem of MPS** states that two MPS tensors generating the same family of quantum states must be related by a gauge transform. The **Quantum Wielandt Bound** gives a constructive upper bound on the length needed for products of matrices to span the full algebra.

## Main Results

### Single-Block Fundamental Theorem

```lean
theorem fundamentalTheorem_singleBlock {A B : MPSTensor d D}
    (hA : IsInjective A) (hAB : SameMPV A B) : GaugeEquiv A B
```

If an MPS tensor `A` is *injective* (its matrices span the full matrix algebra) and `B` generates the same MPV family, then `B i = X * A i * X⁻¹` for some invertible `X`.

### Multi-Block Fundamental Theorem

```lean
theorem fundamentalTheorem_multiBlock_full
    (hA : ∀ k, IsInjective (A k)) (hSame : SameMPV₂ μ A μ B) ... :
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)
```

Block-diagonal MPS tensors with the same MPVs are globally gauge equivalent, handling block permutations, proportional eigenvalues, and spectral separation.

### Pi-Algebra Fundamental Theorem

```lean
theorem fundamentalTheorem_canonicalForm_sameStructure
    (C₁ C₂ : CanonicalForm d) (hC₁ : C₁.AllBlocksInjective)
    (hSame : SameMPV C₁.toTensor C₂.toTensor) ... :
    C₁.numBlocks = C₂.numBlocks ∧ ...
```

Two canonical-form MPS tensors with the same MPVs have the same block structure (number of blocks, dimensions up to permutation) and are related by a block-permuting gauge transform.

### Quantum Wielandt Bound

```lean
theorem cumulative_wielandt_bound [NeZero D]
    (A : MPSTensor d D) (hN : IsNormal A) :
    cumulativeSpan A (D ^ 2) = ⊤
```

For a normal MPS tensor, products of its matrices of length at most `D²` span the full matrix algebra `M_D(ℂ)`.

### Quantum Perron–Frobenius

```lean
theorem IsChannel.exists_posSemidef_fixedPoint
    (hE : IsChannel E) (hD : 0 < D) :
    ∃ ρ, ρ.PosSemidef ∧ ρ ≠ 0 ∧ E ρ = ρ
```

Every quantum channel has a nonzero positive semidefinite fixed point (Cesàro mean / Markov–Kakutani argument).

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
