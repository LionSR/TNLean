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

### Block Permutation Decomposition

```lean
theorem algEquiv_pi_matrix_decomposition (φ : (∀ k, Matrix (Fin (D k)) (Fin (D k)) ℂ) ≃ₐ[ℂ]
    (∀ k, Matrix (Fin (D k)) (Fin (D k)) ℂ)) :
    ∃ (σ : Equiv.Perm (Fin r)) (hσ : ∀ k, D (σ k) = D k)
      (X : ∀ k, GL (Fin (D k)) ℂ), …
```

**Statement:** Any ℂ-algebra automorphism of `∏_k M_{D_k}(ℂ)` decomposes as a block permutation `σ` (preserving dimensions) composed with per-block inner automorphisms (Skolem–Noether). This factors automorphisms of products of simple algebras into a combinatorial part (which blocks map to which) and a continuous part (conjugation within each block).

**Proof chain:**
1. **Block ideal characterization** → the block ideals of `∏ M_{D_k}(ℂ)` are precisely the coordinate projections
2. **Ring equivalences permute simple factors** → any `≃+*` sends block ideals to block ideals, inducing a permutation `σ`
3. **Dimension preservation** → the permutation satisfies `D(σ k) = D k` (from the algebra structure)
4. **Skolem–Noether per block** → the restricted automorphism on each block is inner

### Additional Results

- **Gauge invariance** (`GaugeEquiv.sameMPV`): gauge-equivalent tensors generate the same MPVs
- **MPV decomposition** (`mpv_toTensor_eq_sum`): the MPV of a block-diagonal tensor decomposes as `mpv(⊕_k μ_k A_k)(σ) = Σ_k μ_k^N · mpv(A_k)(σ)`
- **Vandermonde separation** (`block_mpvs_lin_indep_at_fixed_size`): block MPVs with distinct eigenvalues are linearly independent
- **Block-diagonal gauge assembly**: blockwise gauge transforms assemble into a global block-diagonal gauge transform
- **Per-block SameMPV → global SameMPV** (`sameMPV_toTensorFromBlocks_of_blockSameMPV`)

## Project Statistics

| Metric | Value |
|--------|-------|
| Lean modules | 14 |
| Total lines of Lean | 2,221 |
| Build jobs | 2,095 |
| `sorry` | 0 |
| `axiom` | 0 |
| Linter warnings | 0 |
| Mathlib version | v4.27.0 |

> **Note (Feb 2026):** A simplification pass (commit `b86cdb4`) consolidated
> `Injective.lean` and `GaugeInvariance.lean` into `Defs.lean`, merged duplicate
> lemmas, and added `PiAlgebraExtension.lean` — reducing the codebase by ~20%
> (from 2,816 → 2,221 lines, 15 → 14 modules) with zero loss of proven results.

## File Structure

```
MPSLean/MPS/
├── Defs.lean                    — MPSTensor, IsInjective, GaugeEquiv, SameMPV, gauge invariance (128 l)
├── Transfer.lean                — Transfer map, gauge covariance, positivity (45 l)
├── TraceNondeg.lean             — Trace nondegeneracy: tr(MN)=0 ∀N ⟹ M=0 (22 l)
├── TracePairing.lean            — Trace pairing bilinear form infrastructure (98 l)
├── LinearExtension.lean         — Unique linear extension T with T(Aⁱ)=Bⁱ, multiplicativity (159 l)
├── SkolemNoether.lean           — Simplicity of M_D(ℂ), Skolem–Noether theorem (149 l)
├── FundamentalTheorem.lean      — Single-block Fundamental Theorem assembly (78 l)
├── CanonicalForm.lean           — CanonicalForm structure, toTensor (51 l)
├── MultiBlock.lean              — Block-diagonal MPV decomposition infrastructure (163 l)
├── BasisNormal.lean             — Vandermonde separation of block MPVs (162 l)
├── FundamentalTheoremMulti.lean — Multi-block gauge assembly + global theorem (237 l)
├── BlockPermutation.lean        — Automorphisms of ∏ simple rings permute factors (223 l)
├── BlockPermutationMPS.lean     — Per-block decomposition via Skolem–Noether (336 l)
└── PiAlgebraExtension.lean      — Linear extension on ∏ M_{D_k}(ℂ) from SameMPV₂ (370 l)
```

## Key Design Decisions

- **Algebraic injectivity**: We define `IsInjective A` as the condition that the matrices `{A i}` span the full matrix algebra `M_D(ℂ)`. This is purely algebraic and avoids the need for completely positive maps or Perron–Frobenius theory.
- **`abbrev MPSTensor`**: The type `MPSTensor d D := Fin d → Matrix (Fin D) (Fin D) ℂ` is a reducible abbreviation, allowing direct use of Mathlib's `Matrix` API.
- **Parametric multi-block statements**: The multi-block theorem is stated with parameters `{r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}` rather than bundled into a `CanonicalForm` structure, avoiding cast difficulties.
- **Sigma-type indices**: Block-diagonal proofs work on `(k : Fin r) × Fin (dim k)` and reindex to `Fin (∑ k, dim k)` only at the boundary.
- **`GL (Fin D) ℂ`**: Gauge transforms are elements of the general linear group, ensuring invertibility by construction.

## Proof Architecture

The formalization is organized into three layers:

**Layer 1 — Single-Block Fundamental Theorem** (7 modules, ~679 lines)
`Defs → Transfer → TraceNondeg → TracePairing → LinearExtension → SkolemNoether → FundamentalTheorem`

**Layer 2 — Multi-Block Assembly** (4 modules, ~613 lines)
`CanonicalForm → MultiBlock → BasisNormal → FundamentalTheoremMulti`

**Layer 3 — Block Permutation + Pi-Algebra Extension** (3 modules, ~929 lines)
`BlockPermutation → BlockPermutationMPS → PiAlgebraExtension`
Factors automorphisms of `∏ M_{D_k}(ℂ)` into block permutations + per-block inner automorphisms, and constructs the linear extension on the product algebra.

## The Remaining Gap

The gap has **narrowed significantly**. We now have:

- ✅ Full single-block Fundamental Theorem (SameMPV → GaugeEquiv)
- ✅ Multi-block gauge assembly (per-block SameMPV → global GaugeEquiv)
- ✅ Block permutation decomposition (any algebra automorphism of `∏ M_{D_k}(ℂ)` = permutation + per-block inner automorphisms)

**What remains:** constructing the linear extension `T` on the Pi algebra `∏_k M_{D_k}(ℂ)` from `SameMPV₂` (total MPV equality at the block-diagonal level). This follows the same mathematical pattern as the single-block proof — extending a linear map from generators, showing multiplicativity via trace nondegeneracy — but on the product algebra rather than a single matrix ring. Once `T` is constructed as a ring automorphism, the block permutation decomposition theorem applies directly to decompose it into a permutation of blocks plus per-block gauge transforms.

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
