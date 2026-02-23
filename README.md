# TNLean

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

### Quantum Perron–Frobenius Theory

```lean
theorem IsChannel.exists_posSemidef_fixedPoint
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hE : IsChannel E) (hD : 0 < D) :
    ∃ ρ : Matrix (Fin D) (Fin D) ℂ, ρ.PosSemidef ∧ ρ ≠ 0 ∧ E ρ = ρ
```

**Statement:** Every quantum channel (trace-preserving positive map) on `M_D(ℂ)` has a nonzero positive semidefinite fixed point.

**Proof:** Cesàro mean / Markov–Kakutani argument. The key steps are:
1. Density matrices form a compact convex nonempty set (Heine–Borel via entry norm bounds)
2. Cesàro means `σ_N = (1/N) Σ_{n=0}^{N-1} E^n(ρ₀)` stay in the density matrices
3. Sequential compactness gives a convergent subsequence `σ_{φ(k)} → ρ`
4. Telescoping identity: `E(σ_N) - σ_N = (1/N)(E^N(ρ₀) - ρ₀) → 0`
5. Continuity: `E(ρ) = ρ`

### Additional Results

- **Gauge invariance** (`GaugeEquiv.sameMPV`): gauge-equivalent tensors generate the same MPVs
- **MPV decomposition** (`mpv_toTensor_eq_sum`): the MPV of a block-diagonal tensor decomposes as `mpv(⊕_k μ_k A_k)(σ) = Σ_k μ_k^N · mpv(A_k)(σ)`
- **Vandermonde separation** (`block_mpvs_lin_indep_at_fixed_size`): block MPVs with distinct eigenvalues are linearly independent
- **Block-diagonal gauge assembly**: blockwise gauge transforms assemble into a global block-diagonal gauge transform
- **Per-block SameMPV → global SameMPV** (`sameMPV_toTensorFromBlocks_of_blockSameMPV`)
- **Single-block closure** (`sameMPV₂_single_block`): for single-block canonical forms (`r = 1`), `SameMPV₂` with `μ₀ ≠ 0` immediately gives per-block `SameMPV`
- **End-to-end pipeline** (`fundamentalTheorem_multiBlock_fromSameMPV₂`): complete multi-block FT from `SameMPV₂` with explicit separation hypothesis
- **Injectivity → irreducibility** (`injective_implies_irreducibleCP`): injective MPS tensors have irreducible transfer maps
- **Spectral convergence** (`pow_tendsto_zero_of_spectralRadius_lt_one`): Gelfand formula gives `a^n → 0` when spectral radius < 1
- **Cross-correlation decay** (`cross_correlation_tendsto_zero`): mixed transfer iterates vanish for non-equivalent blocks

## Project Statistics

| Metric | Value |
|--------|-------|
| Lean modules | 18 |
| Total lines of Lean | 4,502 |
| Theorems / lemmas | 167 |
| Definitions | 40 |
| `sorry` | 4 (spectral theory; see below) |
| `axiom` | 0 |
| Mathlib version | v4.27.0 |

## File Structure

```
TNLean/MPS/
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
├── FundamentalTheoremMulti.lean — Multi-block gauge assembly + global theorem (232 l)
├── BlockPermutation.lean        — Automorphisms of ∏ simple rings permute factors (223 l)
├── BlockPermutationMPS.lean     — Per-block decomposition via Skolem–Noether (334 l)
├── PiAlgebraExtension.lean      — Linear extension on ∏ M_{D_k}(ℂ), single-block closure (541 l)
├── CPPrimitive.lean             — Irreducibility of CP maps, injectivity→irreducibility (257 l)
├── PositiveMapSpectral.lean     — Positive maps, density matrices, Cesàro fixed point (483 l)
├── QuantumPerronFrobenius.lean  — Quantum Perron–Frobenius: uniqueness, positivity (885 l)
└── TransferSpectral.lean        — Mixed transfer operator, spectral convergence (489 l)
```

## Key Design Decisions

- **Algebraic injectivity**: We define `IsInjective A` as the condition that the matrices `{A i}` span the full matrix algebra `M_D(ℂ)`. This is purely algebraic and avoids the need for completely positive maps or Perron–Frobenius theory.
- **`abbrev MPSTensor`**: The type `MPSTensor d D := Fin d → Matrix (Fin D) (Fin D) ℂ` is a reducible abbreviation, allowing direct use of Mathlib's `Matrix` API.
- **Parametric multi-block statements**: The multi-block theorem is stated with parameters `{r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}` rather than bundled into a `CanonicalForm` structure, avoiding cast difficulties.
- **Sigma-type indices**: Block-diagonal proofs work on `(k : Fin r) × Fin (dim k)` and reindex to `Fin (∑ k, dim k)` only at the boundary.
- **`GL (Fin D) ℂ`**: Gauge transforms are elements of the general linear group, ensuring invertibility by construction.

## Proof Architecture

The formalization is organized into four layers:

**Layer 1 — Single-Block Fundamental Theorem** (7 modules, ~679 lines)
`Defs → Transfer → TraceNondeg → TracePairing → LinearExtension → SkolemNoether → FundamentalTheorem`

**Layer 2 — Multi-Block Assembly** (4 modules, ~613 lines)
`CanonicalForm → MultiBlock → BasisNormal → FundamentalTheoremMulti`

**Layer 3 — Block Permutation + Pi-Algebra Extension** (3 modules, ~1,098 lines)
`BlockPermutation → BlockPermutationMPS → PiAlgebraExtension`
Factors automorphisms of `∏ M_{D_k}(ℂ)` into block permutations + per-block inner automorphisms, and constructs the linear extension on the product algebra.

**Layer 4 — Quantum Perron–Frobenius + Spectral Theory** (4 modules, ~2,114 lines)
`CPPrimitive → PositiveMapSpectral → QuantumPerronFrobenius → TransferSpectral`
Develops positive map theory, proves existence/uniqueness of PSD fixed points via Cesàro means, and establishes spectral convergence for mixed transfer operators.

## The Remaining Gap

The gap has **narrowed significantly**. We now have:

- ✅ Full single-block Fundamental Theorem (SameMPV → GaugeEquiv)
- ✅ Multi-block gauge assembly (per-block SameMPV → global GaugeEquiv)
- ✅ Block permutation decomposition (any algebra automorphism of `∏ M_{D_k}(ℂ)` = permutation + per-block inner automorphisms)
- ✅ Pi-algebra automorphism from per-block SameMPV, with full decomposition
- ✅ **Single-block case closed**: `sameMPV₂_single_block` proves that for `r = 1`, `SameMPV₂` directly gives per-block `SameMPV` (no PF theory needed)
- ✅ **Transfer operator spectral theory**: Mixed transfer operator, Gelfand spectral radius convergence, cross-correlation decay, block separation
- ✅ **CP map theory**: Injectivity implies irreducibility of the transfer operator (complete proof via PSD cone argument)
- ✅ **Positive map spectral theory**: Density matrices are compact/convex/nonempty, Cesàro mean fixed-point theorem for channels (Markov–Kakutani argument)
- ✅ **Quantum Perron–Frobenius existence**: Every trace-preserving positive map (channel) has a nonzero PSD fixed point
- ✅ **Quantum Perron–Frobenius uniqueness**: Injective MPS tensors have unique PSD fixed point up to scaling, and it is positive definite

**What remains for `r ≥ 2` (4 `sorry`):**

| # | Location | Statement | Status |
|---|----------|-----------|--------|
| 1 | `PositiveMapSpectral.lean:307` | Wolf Prop 6.8: Hermitian fixed points decompose into PSD fixed points | Nice-to-have, unused |
| 2 | `TransferSpectral.lean:256` | Vectorization: spectral radius of End ↔ Kronecker matrix | Standalone, unused |
| 3 | `TransferSpectral.lean:292` | **Spectral gap**: `spectralRadius(F_{AB}) < 1` for non-equivalent blocks | **KEY BLOCKER** |
| 4 | `PiAlgebraExtension.lean:520` | Block separation: `SameMPV₂ ⟹ per-block SameMPV` | Depends on #3 |

The single critical sorry is `spectralRadius_mixedTransfer_lt_one` (#3): for injective MPS tensors A, B that are not gauge-phase equivalent, the mixed transfer operator F_{AB} has spectral radius < 1. This is the quantum Perron–Frobenius theorem applied to cross-block channels. Everything downstream (convergence, block separation, per-block SameMPV) follows from this single result.

See the detailed analysis in `PiAlgebraExtension.lean` and `TransferSpectral.lean`.

## Building

```bash
# Install elan (Lean version manager) if needed
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Build
lake build
```

Requires Lean 4 v4.27.0 (managed via `lean-toolchain`).

## References

- J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) — primary source for the Fundamental Theorem
- M. M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012) — Chapter 6 for positive map spectral theory
- [Mathlib4](https://github.com/leanprover-community/mathlib4) — the Lean 4 mathematics library
- M. Fannes, B. Nachtergaele, R. F. Werner, *Finitely correlated states on quantum spin chains*, Commun. Math. Phys. **144**, 443–490 (1992)
