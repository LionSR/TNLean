# MPSLean

A formal verification of the **Fundamental Theorem of Matrix Product States** in Lean 4, using [Mathlib](https://github.com/leanprover-community/mathlib4) v4.27.0.

## Overview

[Matrix Product States](https://en.wikipedia.org/wiki/Matrix_product_state) (MPS) are a central tool in quantum information theory and condensed matter physics. The **Fundamental Theorem of MPS** states that if two MPS tensors generate the same family of quantum states (the same "Matrix Product Vectors"), then they are related by a gauge transform — a simultaneous similarity by an invertible matrix.

This project formalizes the theorem following the treatment in:

> J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete,  
> *Matrix Product States and Projected Entangled Pair States: Concepts, Symmetries, and Theorems*,  
> [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) (2020), Rev. Mod. Phys. **93**, 045003 (2021).

## Main Results

### Single-Block Fundamental Theorem

```lean
theorem fundamentalTheorem_singleBlock {A B : MPSTensor d D}
    (hA : IsInjective A) (hAB : SameMPV A B) : GaugeEquiv A B
```

**Statement:** If an MPS tensor `A` is *injective* (its matrices span the full matrix algebra) and `B` generates the same MPV family as `A`, then `B i = X * A i * X⁻¹` for some invertible matrix `X`.

**Proof chain:**
1. **Trace nondegeneracy** → the bilinear form `(M, N) ↦ tr(MN)` is nondegenerate
2. **Linear extension** → there is a unique linear map `T` with `T(Aⁱ) = Bⁱ`, and it is multiplicative
3. **Simplicity of matrix rings** → a nonzero multiplicative endomorphism of `M_D(ℂ)` is bijective
4. **Skolem–Noether theorem** → every automorphism of `M_D(ℂ)` is inner

### Multi-Block Fundamental Theorem

```lean
theorem fundamentalTheorem_multiBlock_global
    (hA : ∀ k : Fin r, IsInjective (A k))
    (hSame : ∀ k : Fin r, SameMPV (A k) (B k)) :
    GaugeEquiv (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)
```

**Statement:** Given block-diagonal MPS tensors `⊕_k μ_k A_k` and `⊕_k μ_k B_k`, if each block `A_k` is injective and generates the same MPV as `B_k`, then the block-diagonal tensors are globally gauge equivalent via a block-diagonal gauge transform.

### Additional Results

- **Gauge invariance** (`GaugeEquiv.sameMPV`): gauge-equivalent tensors generate the same MPVs
- **MPV decomposition** (`mpv_toTensor_eq_sum`): the MPV of a block-diagonal tensor decomposes as `mpv(⊕_k μ_k A_k)(σ) = Σ_k μ_k^N · mpv(A_k)(σ)`
- **Vandermonde separation** (`block_mpvs_lin_indep_at_fixed_size`): block MPVs with distinct eigenvalues are linearly independent
- **Block-diagonal gauge assembly**: blockwise gauge transforms assemble into a global block-diagonal gauge transform
- **Per-block SameMPV → global SameMPV** (`sameMPV_toTensorFromBlocks_of_blockSameMPV`)

## Project Statistics

| Metric | Value |
|--------|-------|
| Lean modules | 13 |
| Total lines of Lean | ~1,680 |
| `sorry` | 0 |
| `axiom` | 0 |
| Linter warnings | 0 |
| Mathlib version | v4.27.0 |

## File Structure

```
MPSLean/MPS/
├── Defs.lean              — MPSTensor, evalWord, mpv, GaugeEquiv, SameMPV
├── GaugeInvariance.lean   — GaugeEquiv implies SameMPV
├── Transfer.lean          — Transfer map, gauge covariance, positivity
├── Injective.lean         — IsInjective, IsNBlkInjective, IsNormal
├── TraceNondeg.lean       — Trace nondegeneracy: tr(MN)=0 ∀N ⟹ M=0
├── CanonicalForm.lean     — CanonicalForm structure, toTensor
├── TracePairing.lean      — Trace pairing bilinear form infrastructure
├── LinearExtension.lean   — Unique linear extension T with T(Aⁱ)=Bⁱ, multiplicativity
├── SkolemNoether.lean     — Simplicity of M_D(ℂ), Skolem–Noether theorem
├── FundamentalTheorem.lean — Single-block Fundamental Theorem assembly
├── MultiBlock.lean        — Block-diagonal MPV decomposition infrastructure
├── BasisNormal.lean       — Vandermonde separation of block MPVs
└── FundamentalTheoremMulti.lean — Multi-block gauge assembly + global theorem
```

## Key Design Decisions

- **Algebraic injectivity**: We define `IsInjective A` as the condition that the matrices `{A i}` span the full matrix algebra `M_D(ℂ)`. This is purely algebraic and avoids the need for completely positive maps or Perron–Frobenius theory.
- **`abbrev MPSTensor`**: The type `MPSTensor d D := Fin d → Matrix (Fin D) (Fin D) ℂ` is a reducible abbreviation, allowing direct use of Mathlib's `Matrix` API.
- **Parametric multi-block statements**: The multi-block theorem is stated with parameters `{r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}` rather than bundled into a `CanonicalForm` structure, avoiding cast difficulties.
- **Sigma-type indices**: Block-diagonal proofs work on `(k : Fin r) × Fin (dim k)` and reindex to `Fin (∑ k, dim k)` only at the boundary.
- **`GL (Fin D) ℂ`**: Gauge transforms are elements of the general linear group, ensuring invertibility by construction.

## The Remaining Gap

The multi-block theorem currently takes per-block `SameMPV` as a *hypothesis*. In the physics literature, this is derived from total MPV equality using the spectral theory of mixed transfer operators (requiring quantum Perron–Frobenius, which is not available in Mathlib). An alternative algebraic approach via semisimple ring homomorphism theory may be possible but has not yet been formalized. The theorem as stated is still highly nontrivial: it includes the full single-block proof and the complete block-diagonal assembly machinery.

## Building

```bash
# Install elan (Lean version manager) if needed
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build
lake build
```

Requires Lean 4 v4.27.0 (managed via `lean-toolchain`).

## References

- J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, [arXiv:2011.12127](https://arxiv.org/abs/2011.12127)
- [Mathlib4](https://github.com/leanprover-community/mathlib4) — the Lean 4 mathematics library
- M. Fannes, B. Nachtergaele, R. F. Werner, *Finitely correlated states on quantum spin chains*, Commun. Math. Phys. **144**, 443–490 (1992)
