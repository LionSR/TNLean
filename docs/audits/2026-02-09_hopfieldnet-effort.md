---
title: "HopfieldNet classical PF: effort analysis for TNLean integration"
date: 2026-02-09
author: AI research assistant (search agent)
purpose: >
  Deep dive into mkaratarakis/HopfieldNet — the Cipollina, Karatarakis,
  Wiedijk (arXiv:2512.07766) Perron–Frobenius formalization.  File-by-file
  inventory of 8,302 lines / 416 theorems.  Version compatibility
  assessment (identical Lean+Mathlib), import instructions, and the
  classical-to-quantum bridge strategy with effort estimates.
---

# HopfieldNet Perron-Frobenius: Effort Analysis for TNLean Integration

**Date:** 2026-02-09
**Repository:** https://github.com/mkaratarakis/HopfieldNet
**Authors:** Ioannis Karatarakis, Michele Cipollina, Freek Wiedijk (Radboud University)
**Paper:** arXiv:2512.07766 ("Formalized Hopfield Networks and Boltzmann Machines in Lean 4")

---

## 1. Executive Summary

The HopfieldNet repository contains a **complete, essentially sorry-free formalization of the classical Perron-Frobenius theorem** for general irreducible and primitive nonneg real matrices — far more comprehensive than what the paper abstract suggested (which emphasized stochastic matrices). Critically, the repo uses **the exact same Lean and Mathlib versions as TNLean**, making integration frictionless.

### Key Numbers

| Metric | Value |
|--------|-------|
| Total PF code | 8,302 lines in `MCMC/PF/` |
| Theorems/lemmas | 416 |
| Definitions | 40 |
| Sorries | 1 (minor path lemma in quiver infrastructure) |
| Lean version | v4.27.0-rc1 (TNLean: v4.27.0) |
| Mathlib revision | `910dac3f` (identical to TNLean) |
| License | MIT |

### Bottom Line

Importing the classical PF theorem from HopfieldNet is **trivially easy** (same versions, same Mathlib). However, applying it to our quantum problem requires a **non-trivial bridge** between classical PF (real nonneg matrices) and quantum PF (completely positive maps). Estimated total effort: **5–8 weeks**, saving **50–60%** compared to building everything from scratch.

---

## 2. What HopfieldNet Actually Proves

### Contrary to our earlier understanding, this is NOT limited to stochastic matrices.

The `MCMC/PF/` module proves the full Perron-Frobenius theorem for:

#### For Irreducible Nonneg Real Matrices (`pft_irreducible`)
- **Existence**: There exists a positive eigenvalue `r > 0` with a strictly positive eigenvector `v ∈ stdSimplex ℝ n` such that `A *ᵥ v = r • v`.
- **Uniqueness**: This eigenvector in the standard simplex is unique.
- **Spectral bound**: `|μ| ≤ r` for all eigenvalues μ (proven via Collatz-Wielandt).
- **Perron root = spectral radius**: `r` is the spectral radius of `A`.

#### For Primitive Nonneg Real Matrices (Dominance)
- **Spectral dominance**: If `μ ≠ r`, then `|μ| < r` (strict inequality) — `spectral_dominance_of_primitive'`.
- **Unique positive eigenvector**: Up to positive scaling — `uniqueness_of_positive_eigenvector`.

#### For Column-Stochastic Matrices (Special Case)
- **Unique stationary distribution**: `exists_positive_eigenvector_of_irreducible_stochastic`.

### Proof Architecture

```
CollatzWielandt.lean (888 lines)
  └── Collatz-Wielandt function, compactness, existence of maximizer on simplex

Primitive.lean (308 lines)
  └── Maximizer is eigenvector for primitive matrices, existence theorem

Uniqueness.lean (97 lines)
  └── Positive eigenvector unique up to scaling (primitive case)

Irreducible.lean (622 lines)
  └── Full PFT for irreducible via reduction to primitive (1+A trick)
  └── Uniqueness generalized to irreducible case

Dominance.lean (1,242 lines) — THE MAIN FILE
  └── |μ| ≤ r (subinvariance argument)
  └── Perron root = spectral radius
  └── Phase alignment argument for primitive spectral dominance
  └── spectral_dominance_of_primitive': μ ≠ r ⟹ |μ| < r

Stochastic.lean (81 lines)
  └── Specialization to column-stochastic matrices

Spectrum.lean (696 lines)
  └── Spectral infrastructure connecting Matrix, toLin', spectrum
```

### Supporting Infrastructure (3,551 lines)

| File | Lines | Content |
|------|-------|---------|
| `aux.lean` | 850 | General utilities (nonneg sums, products, etc.) |
| `Quiver/Path.lean` | 1,113 | Graph path infrastructure for irreducibility |
| `Quiver/Cyclic.lean` | 287 | Cyclic path/aperiodicity |
| `Data/List.lean` | 679 | List lemmas for paths |
| `CstarAlgebra/Classes.lean` | 418 | Ordered algebra, positivity classes |
| `ExtremeValueUSC.lean` | 204 | Upper semicontinuous extreme value theorem |

---

## 3. Compatibility Assessment

### Version Compatibility: PERFECT ✅

```
                    HopfieldNet         TNLean
Lean version:       v4.27.0-rc1        v4.27.0
Mathlib revision:   910dac3f6e...      910dac3f6e...  (IDENTICAL)
Build system:       lakefile.lean       lakefile.toml
Only dependency:    Mathlib             Mathlib
License:            MIT                 (our project)
```

The Lean version difference (rc1 vs release) is cosmetic — the rc1 is the release candidate that became v4.27.0. The Mathlib revisions are **byte-identical**. This means:

- **Zero version conflicts**
- **Shared Mathlib cache** (no rebuild needed)
- **Import with a single `require` statement in lakefile**

### How to Import

**Option A: Lake Dependency (Recommended)**
```lean
-- In lakefile.toml:
[[require]]
name = "HopfieldNet"
git = "https://github.com/mkaratarakis/HopfieldNet.git"
rev = "master"
```
Then: `import MCMC.PF.LinearAlgebra.Matrix.PerronFrobenius.Dominance`

**Option B: Copy the PF Module**
Copy `MCMC/PF/` (16 files, 8,302 lines) directly into TNLean. Rename the module prefix. MIT license allows this.

**Recommendation**: Option A for development, Option B for a self-contained release.

---

## 4. The Quantum Bridge Problem

### Why Classical PF Doesn't Directly Apply

Our transfer operator `E_A(X) = Σᵢ Aᵢ X Aᵢ†` is a completely positive (CP) map on the space of D×D complex matrices. It is **not** a nonneg real matrix acting on a real vector space.

The vectorization `vec(E_A(X)) = T · vec(X)` where `T = Σᵢ Aᵢ ⊗ conj(Aᵢ)` gives a D²×D² **complex** matrix. Its entries are `Σᵢ (Aᵢ)ₐᵦ · conj((Aᵢ)_{cd})` — complex numbers in general, not nonneg reals. So HopfieldNet's PF theorems cannot be applied to T directly.

### What We Actually Need

For the block separation lemma, we need:

1. **The transfer operator `E_A` has spectral radius 1** (follows from canonical form: `E_A(I) = I`).
2. **The eigenvalue 1 has multiplicity 1** (this is the quantum PF claim: irreducibility of `E_A` implies the fixed point is unique).
3. **All other eigenvalues satisfy `|λ| < 1`** (spectral gap).

These together imply that as N → ∞, the N-th power of `E_A` converges to the rank-1 projector onto the fixed point, which is precisely what block separation needs.

### The Bridge Strategy

The key mathematical insight is that `E_A` restricted to the subspace of **Hermitian matrices** is a **real** linear operator that maps the **cone of PSD matrices** into itself. The matrix representation of this restricted operator (in a suitable basis) connects to the classical PF setting.

Specifically:
- Let `{H₁, ..., H_{D²}}` be an orthonormal basis of `Herm(D)` w.r.t. the Hilbert-Schmidt inner product.
- Define the real matrix `M_{jk} = ⟨Hⱼ, E_A(Hₖ)⟩_{HS} = tr(Hⱼ · E_A(Hₖ))`.
- `M` is a D²×D² real matrix.
- The eigenvalues of `M` include all real eigenvalues of `E_A` (and the real parts of complex conjugate pairs appear as 2×2 blocks).
- `E_A` maps PSD matrices to PSD matrices, but `M` is NOT necessarily entry-wise nonneg (the HS-basis elements are not all PSD).

**The gap**: Connecting "CP map irreducibility" (no nontrivial face of the PSD cone is invariant) to classical "matrix irreducibility" (no nontrivial subset of indices is invariant in the graph sense) requires careful formalization.

### Possible Approaches to Bridge

**Approach A: Direct Quantum PF via Compactness (Recommended)**
- Prove the quantum PF directly using the compactness of the quantum state space and the Brouwer fixed-point theorem (already in Mathlib).
- Irreducibility of `E_A` implies the fixed point is in the interior of the state space (i.e., strictly positive definite).
- Uniqueness follows from a convexity/contraction argument.
- **Does not need** the classical PF at all.
- Estimated effort: **3–4 weeks, 600–1000 LoC**.
- Risk: Medium (needs careful Lean formalization of cone-positive maps).

**Approach B: Vectorization + Classical PF**
- Formalize the vec/Choi correspondence.
- Show that E_A's spectral properties are captured by a real matrix in HS basis.
- Establish the irreducibility bridge.
- Apply HopfieldNet's `spectral_dominance_of_primitive'`.
- Estimated effort: **5–8 weeks, 1100–1800 LoC**.
- Risk: Medium-high (the irreducibility bridge is technically involved).

**Approach C: Axiomatize + Use Classical PF for Future Work**
- Axiomatize the quantum PF result as a hypothesis (current approach).
- Import HopfieldNet's classical PF for independent use.
- Plan the full bridge as a separate project.
- Estimated effort: **1 day** (import), **0 additional LoC** (keep axiom).
- Risk: None (already done).

---

## 5. Detailed Effort Estimates

### Importing HopfieldNet PF (All Approaches)

| Task | Effort | LoC |
|------|--------|-----|
| Add Lake dependency | 0.5 days | 5 |
| Verify build with MCMC.PF imports | 0.5 days | 0 |
| **Total** | **1 day** | **5** |

### Approach A: Direct Quantum PF (Recommended)

| Step | Effort | LoC | Dependencies |
|------|--------|-----|-------------|
| Define CP map irreducibility | 1 week | 100–150 | Mathlib PSD cones |
| Prove fixed point existence (Brouwer) | 1 week | 150–250 | Mathlib fixed-point theorems |
| Prove fixed point uniqueness | 1 week | 200–300 | Irreducibility definition |
| Prove spectral gap | 1 week | 150–300 | Fixed point + Gelfand formula |
| **Total** | **3–4 weeks** | **600–1000** | |

### Approach B: Vectorization + Classical PF Bridge

| Step | Effort | LoC | Dependencies |
|------|--------|-----|-------------|
| Vectorization/Choi formalization | 1–2 weeks | 300–500 | Mathlib Kronecker |
| Eigenvalue correspondence | 1 week | 200–300 | Vectorization |
| Irreducibility bridge | 2–4 weeks | 500–800 | **Hardest part** |
| Apply HopfieldNet PF | 1 week | 100–200 | Bridge + HopfieldNet |
| **Total** | **5–8 weeks** | **1100–1800** | |

### End-to-End: From Import to Closed Gap

| Phase | Approach A | Approach B |
|-------|-----------|-----------|
| Import HopfieldNet | 1 day | 1 day |
| Bridge formalization | 3–4 weeks | 5–8 weeks |
| Block separation proof | 1 week | 1 week |
| Testing/cleanup | 1 week | 1 week |
| **Total** | **5–6 weeks** | **7–10 weeks** |

---

## 6. Comparison: With vs Without HopfieldNet

| Scenario | Effort | LoC |
|----------|--------|-----|
| **Without HopfieldNet** (PF from scratch + quantum PF) | 4–6 months | 3000–5000 |
| **With HopfieldNet, Approach A** (direct quantum PF, classical PF available) | 5–6 weeks | 600–1000 |
| **With HopfieldNet, Approach B** (full vectorization bridge) | 7–10 weeks | 1100–1800 |
| **Current axiomatic approach** (production status quo) | Done ✅ | 0 |

**Savings from HopfieldNet**: 50–70% depending on approach, primarily because:
1. Classical PF infrastructure (8,302 lines) is completely available if needed.
2. The spectral infrastructure (spectrum ↔ toLin' ↔ Matrix) they built is reusable.
3. The Collatz-Wielandt framework provides tools for eigenvalue bounds.
4. Even for Approach A (which doesn't directly use classical PF), having the classical PF as a reference and potential fallback reduces risk.

---

## 7. Recommendations

### Immediate Actions (This Week)

1. **Add HopfieldNet as a Lake dependency** to TNLean. Cost: 1 day. Even if we don't use PF immediately, this makes the classical PF available for future work and validates the integration.

2. **Update `COMMUNITY_RESOURCES_REPORT.md`** with the finding that the repo is now public and uses identical versions.

### Short-Term (Next 1–2 Months)

3. **Pursue Approach A** (direct quantum PF) as the primary path to closing the gap. The classical PF from HopfieldNet serves as insurance and reference.

4. **Cherry-pick the Choi-Jamiołkowski definitions** from Lean-QuantumInfo (~200 lines, MIT licensed) as the quantum channel foundation.

### Medium-Term (2–4 Months)

5. **If Approach A stalls**, pivot to **Approach B** using the full classical PF bridge. The HopfieldNet infrastructure makes this viable.

6. **Consider contributing** the quantum PF to HopfieldNet or Mathlib as a follow-up.

---

## 8. File-by-File Map of What We'd Use

### Definitely Useful (Import Immediately)

| HopfieldNet File | What It Gives Us |
|-----------------|------------------|
| `Dominance.lean` | `eigenvalue_abs_le_perron_root`, `spectral_dominance_of_primitive'` |
| `Irreducible.lean` | `pft_irreducible` — the main PF theorem |
| `Spectrum.lean` | `spectrum.Matrix_toLin'_eq_spectrum` — spectral bridge |

### Useful for Bridge (Import When Needed)

| HopfieldNet File | What It Gives Us |
|-----------------|------------------|
| `CollatzWielandt.lean` | Eigenvalue bounds via Collatz-Wielandt |
| `Primitive.lean` | Existence of positive eigenvector |
| `Uniqueness.lean` | Eigenvector uniqueness |
| `Lemmas.lean` | `positive_mul_vec_of_nonneg_vec`, irreducibility lemmas |
| `Stochastic.lean` | Template for our trace-preserving map specialization |

### Not Directly Needed

| HopfieldNet File | Why |
|-----------------|-----|
| `Aperiodic.lean` | We work with primitive directly |
| `Multiplicity.lean` | Not needed for our spectral gap argument |
| Support files | Only needed transitively |

---

## 9. Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| HopfieldNet repo becomes unavailable | Low | High | Fork immediately, or copy MIT-licensed code |
| Version drift (they update Lean/Mathlib) | Medium | Low | Pin to specific commit in Lake require |
| The 1 sorry in Path.lean causes issues | Very Low | None | It's in a quiver path lemma not on our critical path |
| Irreducibility bridge harder than estimated | Medium | Medium | Fall back to Approach A (direct quantum PF) |
| Build time increases significantly | Low | Low | Only ~8K new lines; Mathlib cache shared |
