---
title: "Spectral gap analysis: quantum Perron–Frobenius & transfer operators"
date: 2026-02-09
author: AI research assistant (search agent)
purpose: >
  Feasibility study for closing the multi-block (r≥2) gap.  Maps the
  6-step physics proof (transfer operator → CP → irreducibility →
  quantum PF → spectral gap → block separation) against Mathlib v4.27.0
  and external Lean 4 projects.  Provides effort estimates for five
  alternative approaches.
---

# Spectral Gap Analysis Report
## Quantum Perron-Frobenius & Transfer Operator Theory for MPSLean

**Date:** 2026-02-09  
**Scope:** Mathlib v4.27.0 + MPSLean current codebase  
**Author:** Gap analysis for closing the multi-block (r≥2) Fundamental Theorem of MPS

---

## 1. Executive Summary

### The problem
The MPSLean formalization of the Fundamental Theorem of Matrix Product States is **complete and sorry-free for single-block (r=1) canonical forms**. For multi-block (r≥2) canonical forms, one gap remains: proving that a global weighted-sum equality (`SameMPV₂` on block-diagonal tensors) implies per-block equality (`SameMPV` on each block). This is the **block separation lemma**.

### What exists
- **MPSLean** already defines the transfer operator `E_A(X) = Σ_i A_i X A_i†` in `Transfer.lean`, with a proof that it preserves positive semidefiniteness.
- **Mathlib v4.27.0** has definitions of matrix irreducibility/primitivity, a mature spectral theory (spectrum, eigenvalues, characteristic polynomials, spectral radius, Gelfand formula), completely positive map definitions, positive semidefinite matrix ordering, and Kronecker/vectorization identities.
- **External Lean 4 projects** include a classical Perron-Frobenius theorem formalization (Cipollina et al., arXiv:2512.07766, Dec 2025, for Hopfield/Boltzmann machines), and the Lean-QuantumInfo library (Meiburg, ~1059 theorems on quantum states/channels/entropy).
- **Isabelle/AFP** has a complete classical Perron-Frobenius formalization (Divasón, Kunčar, Thiemann, Yamada, 2016).

### What's missing
- **No quantum Perron-Frobenius theorem** in any proof assistant (Lean, Isabelle, Coq).
- **No classical Perron-Frobenius eigenvalue theorem** in Mathlib itself (only the definitions; the eigenvalue/eigenvector result is external).
- **No Choi-Jamiołkowski isomorphism** or Kraus representation theorem in Mathlib.
- **No Stinespring dilation** in Mathlib.

### Feasibility estimate
| Approach | Effort | Risk |
|----------|--------|------|
| Full quantum PF from scratch | 3000–5000 LoC, 3–6 months | High: requires substantial new infrastructure |
| Classical PF + Choi reduction | 1500–2500 LoC, 2–4 months | Medium: Choi isomorphism is the bottleneck |
| Direct finite-dimensional algebraic argument | 800–1500 LoC, 1–2 months | Medium: avoids general PF but needs careful spectral argument |
| Axiomatize the separation lemma | 0 LoC, 0 time | None: already done in current code |

**Recommendation:** Pursue the **direct finite-dimensional algebraic argument** (Approach 3) as the primary path, while keeping the current axiomatic separation (Approach 4) as the production interface. See §6 for details.

---

## 2. The Mathematical Pathway

### 2.1 The block separation problem

**Given:** For all system sizes N and configurations σ : Fin N → Fin d:
```
∑_k μ_k^N · tr(A_k^{σ₁} · A_k^{σ₂} · ⋯ · A_k^{σ_N}) = ∑_k μ_k^N · tr(B_k^{σ₁} · B_k^{σ₂} · ⋯ · B_k^{σ_N})
```

**Want:** For each block k, for all N and σ:
```
tr(A_k^{σ₁} · ⋯ · A_k^{σ_N}) = tr(B_k^{σ₁} · ⋯ · B_k^{σ_N})
```

**Obstacle:** The "coefficients" `mpv(A_k, σ) - mpv(B_k, σ)` depend on σ ∈ Fin N → Fin d, whose type varies with N. A direct Vandermonde argument requires fixed coefficients at different powers of N.

### 2.2 The physics approach: transfer operator spectral theory

The standard physics proof (Pérez-García et al., arXiv:quant-ph/0608197; Cirac et al., arXiv:2011.12127) proceeds via:

#### Step 1: Transfer operator
For each block k, define the transfer operator:
```
E_k(X) = ∑_σ A_k^σ · X · (A_k^σ)†
```
This is already formalized in `Transfer.lean` as `transferMap`.

#### Step 2: Complete positivity
`E_k` is a completely positive (CP) map: it has a Kraus decomposition {A_k^σ}_σ. The CP property implies it maps the positive semidefinite cone to itself. This positivity is already proved in `Transfer.lean` (`transferMap_pos`).

#### Step 3: Irreducibility and quantum PF
When the block tensor A_k is *injective* (the matrices {A_k^σ} span the full matrix algebra), the transfer operator E_k is *irreducible* as a positive map. The **quantum Perron-Frobenius theorem** then gives:

> **Theorem (Quantum PF for irreducible CP maps).**
> Let E : M_D(ℂ) → M_D(ℂ) be an irreducible completely positive map. Then:
> 1. The spectral radius ρ(E) is an eigenvalue of E.
> 2. The corresponding eigenspace is one-dimensional.
> 3. The unique eigenvector (up to scaling) is positive definite.
> 4. No other eigenvalue of modulus ρ(E) has a positive semidefinite eigenvector.

**Reference:** Evans & Høegh-Krohn (1978); Wolf, "Quantum Channels & Operations" Lecture Notes, Theorem 6.2; Sanz, Pérez-García, Wolf, Cirac, arXiv:0909.5347.

#### Step 4: Normalization and spectral gap
After normalizing each block so that ρ(E_k) = 1 (absorbing the spectral radius into μ_k), the dominant eigenvector Λ_k of E_k is the unique positive definite fixed point. The other eigenvalues of E_k have modulus strictly less than 1 (for primitive/irreducible channels).

#### Step 5: Mixed transfer operator decay
The "mixed" transfer operator `E_{k,l}(X) = ∑_σ A_k^σ · X · (B_l^σ)†` for k ≠ l has spectral radius strictly less than 1 (by orthogonality of distinct blocks). This means:
```
(1/N) ∑_{σ : Fin N → Fin d} A_k^{σ₁}···A_k^{σ_N} ⊗ conj(B_l^{σ₁}···B_l^{σ_N}) → 0 as N → ∞
```

#### Step 6: Separation via distinct leading eigenvalues
The μ_k weights in canonical form have distinct absolute values (or, after grouping by |μ_k|, the blocks with the same |μ_k| can be separated using phase arguments). For large N, the term with largest |μ_k|^N dominates, and induction (or a Vandermonde-type argument on the phases) separates the blocks.

### 2.3 Precise theorem chain needed

```
                ┌──────────────┐
                │  Definitions │
                └──────┬───────┘
                       │
         ┌─────────────┼─────────────┐
         │             │             │
    Transfer Op    CP map def    Irreducibility
    E_A(X) =      (Kraus ⇒ CP)   of E_A
    Σ A_i X A_i†                  (from injectivity)
         │             │             │
         └─────────────┼─────────────┘
                       │
              ┌────────┴────────┐
              │  Quantum PF     │
              │  theorem        │
              └────────┬────────┘
                       │
         ┌─────────────┼─────────────┐
         │             │             │
    Unique PD      Spectral gap   Mixed transfer
    fixed point    |λ| < ρ(E)     spectral radius
    of E_A         for other      < ρ(E_k) for
                   eigenvalues    k ≠ l
         │             │             │
         └─────────────┼─────────────┘
                       │
              ┌────────┴────────┐
              │  Block          │
              │  separation     │
              │  lemma          │
              └────────┬────────┘
                       │
              ┌────────┴────────┐
              │  SameMPV₂ ⟹     │
              │  per-block      │
              │  SameMPV        │
              └─────────────────┘
```

---

## 3. Mathlib v4.27.0 Inventory

### 3.1 What exists

| Component | Status | Location | Maturity |
|-----------|--------|----------|----------|
| **Spectrum / eigenvalues** | ✅ Complete | `Mathlib.Algebra.Algebra.Spectrum.Basic`, `Mathlib.LinearAlgebra.Eigenspace.Basic` | Mature; spectrum ↔ eigenvalues for finite-dim |
| **Characteristic polynomial** | ✅ Complete | `Mathlib.LinearAlgebra.Charpoly.*` | Mature; Cayley-Hamilton, roots ↔ eigenvalues |
| **Spectral radius** | ✅ Complete | `Mathlib.Analysis.Normed.Algebra.Spectrum` | Mature; `spectralRadius`, Gelfand formula |
| **Matrix irreducibility** | ✅ Definitions | `Mathlib.LinearAlgebra.Matrix.Irreducible.Defs` | New (2025); `IsIrreducible`, `IsPrimitive`, graph-theoretic equivalence |
| **CP map definition** | ✅ Definition | `Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap` | Recent; `CompletelyPositiveMap`, `CompletelyPositiveMapClass` |
| **Positive linear maps** | ✅ Basic | `Mathlib.Analysis.CStarAlgebra.PositiveLinearMap` | Positive maps are bounded |
| **PosDef / PosSemidef** | ✅ Complete | `Mathlib.LinearAlgebra.Matrix.PosDef`, `Mathlib.Analysis.Matrix.PosDef` | Mature |
| **Matrix ordering** | ✅ Complete | `Mathlib.Analysis.Matrix.Order` | PSD ordering: `Matrix.le_iff`, `nonneg_iff_posSemidef` |
| **Kronecker product** | ✅ Complete | `Mathlib.LinearAlgebra.Matrix.Kronecker` | `kroneckerMap`, mixed product property |
| **Vectorization** | ✅ Complete | `Mathlib.LinearAlgebra.Matrix.Vec` | `vec`, `kronecker_mulVec_vec` = key identity |
| **Block diagonal** | ✅ Complete | `Mathlib.Data.Matrix.Block` | `blockDiagonal'`, multiplication, trace |
| **Vandermonde** | ✅ Complete | `Mathlib.LinearAlgebra.Vandermonde` | `det_vandermonde`, linear independence |
| **Artin-Wedderburn** | ✅ Existence | `Mathlib.RingTheory.SimpleModule.WedderburnArtin` | Semisimple ring ≃ ∏ M_n(D); no uniqueness |
| **Banach fixed point** | ✅ Complete | `Mathlib.Topology.MetricSpace.Contracting` | `ContractingWith.exists_fixedPoint` |
| **Invariant subspaces** | ✅ Basic | `Mathlib.Algebra.Module.Submodule.Invariant` | `invtSubmodule` |
| **Star algebra hom** | ✅ Complete | `Mathlib.Algebra.Star.StarAlgHom` | Algebra homomorphisms preserving * |

### 3.2 What's missing

| Component | Status | What's needed | Est. effort |
|-----------|--------|---------------|-------------|
| **PF eigenvalue theorem** | ❌ Not in Mathlib | For nonneg irreducible matrix: spectral radius is eigenvalue, unique PD eigenvector | 500–1000 LoC |
| **Quantum PF theorem** | ❌ Not anywhere | For irreducible CP map: spectral radius eigenvalue, uniqueness, PD eigenvector | 1000–2000 LoC |
| **Choi-Jamiołkowski** | ❌ Not in Mathlib | CP map ↔ PSD matrix correspondence | 300–600 LoC |
| **Kraus representation** | ❌ Not in Mathlib | CP map ↔ {A_i} Kraus operators | 300–500 LoC |
| **Stinespring dilation** | ❌ Not in Mathlib | CP map ↔ *-homomorphism + compression | 500–1000 LoC |
| **Irreducibility of E_A** | ❌ Not in Mathlib | Injective MPS ⟹ transfer operator irreducible | 200–400 LoC |
| **Trace-preserving maps** | ❌ Not in Mathlib | `tr(E(X)) = tr(X)` for normalized channels | 100–200 LoC |
| **Mixed transfer decay** | ❌ Not in Mathlib | Cross-block transfer spectral radius < 1 | 300–600 LoC |
| **PF for stochastic matrices** | ⚠️ External only | Cipollina et al. (2025) have it in Lean 4, not yet in Mathlib | 0 if imported |
| **`spectralRadius = max |eigenvalue|`** | ⚠️ Missing convenience | Need to assemble from existing pieces | 100–300 LoC |

### 3.3 External Lean 4 resources

| Project | Relevance | Status |
|---------|-----------|--------|
| **Cipollina et al. (arXiv:2512.07766)** | Classical PF for nonneg irreducible matrices in Lean 4 + Mathlib | Exists (Dec 2025); uses `Matrix.IsIrreducible`; proves existence/uniqueness of Perron eigenvector |
| **Lean-QuantumInfo (Timeroot)** | CPTPMap, MState, quantum entropy, Stein's Lemma | ~1059 theorems; no quantum PF; finite-dim only |
| **QFormal Initiative** | Broader quantum formalization initiative | Early stage |
| **Isabelle AFP: Perron_Frobenius** | Complete classical PF with spectral radius analysis | Mature; not directly portable to Lean |
| **Isabelle AFP: Stochastic_Matrices** | PF applied to Markov chains | Builds on above |

---

## 4. Formalization Roadmap

### 4.1 Dependency graph of missing pieces

```
Level 0 (already done):
  transferMap, transferMap_pos (MPSLean/Transfer.lean)
  spectrum, eigenvalue, spectralRadius (Mathlib)
  PosSemidef, matrix ordering (Mathlib)
  Matrix.IsIrreducible (Mathlib)
  Kronecker, vectorization (Mathlib)

Level 1 (foundational, independently useful):
  A. spectralRadius = max |eigenvalue| for fin-dim      [100-300 LoC]
  B. Classical PF eigenvalue theorem                     [500-1000 LoC]
     (import/adapt from Cipollina et al.?)
  C. Choi-Jamiołkowski isomorphism                       [300-600 LoC]

Level 2 (quantum-specific):
  D. Irreducibility of E_A from injectivity of A        [200-400 LoC]
     Depends on: Level 0
  E. Quantum PF (via Choi + classical PF)               [500-1000 LoC]
     Depends on: B, C, D
  F. Trace-preserving / unital channel theory            [100-200 LoC]

Level 3 (MPS-specific):
  G. Mixed transfer operator spectral radius bound      [300-600 LoC]
     Depends on: E
  H. Block separation lemma                              [200-400 LoC]
     Depends on: E, G, Vandermonde

Level 4 (integration):
  I. SameMPV₂ → per-block SameMPV                       [100-200 LoC]
     Depends on: H
```

### 4.2 Estimated total effort

**Minimum path (using Choi reduction):** ~1500–2500 LoC, 2–4 months  
**Full quantum information path:** ~3000–5000 LoC, 3–6 months

### 4.3 What could be contributed to Mathlib

| Piece | Mathlib-worthiness | Priority |
|-------|-------------------|----------|
| Classical PF eigenvalue theorem | ⭐⭐⭐⭐⭐ | On the "100 theorems" wish list |
| Choi-Jamiołkowski isomorphism | ⭐⭐⭐⭐ | Fundamental to quantum info |
| Spectral radius = max eigenvalue | ⭐⭐⭐⭐ | Common convenience lemma |
| Quantum PF theorem | ⭐⭐⭐ | Important but niche |
| Transfer operator / quantum channel API | ⭐⭐⭐ | Builds on existing CP map def |
| Block separation lemma | ⭐⭐ | Very MPS-specific |

---

## 5. Alternative Approaches

### 5.1 Approach A: Full quantum PF machinery

**Path:** Define CP maps with Kraus form → prove Choi isomorphism → reduce quantum PF to classical PF → apply to transfer operator → derive spectral gap → prove block separation.

**Pros:** Most general; produces Mathlib-worthy infrastructure; follows the physics literature exactly.

**Cons:** Highest effort; requires substantial new infrastructure; overkill for the specific problem.

### 5.2 Approach B: Choi-Jamiołkowski reduction to classical PF

**Key idea:** The transfer operator `E_A(X) = Σ_i A_i X A_i†` can be "vectorized" via the Choi-Jamiołkowski isomorphism. The vec-Kronecker identity (already in Mathlib!) gives:
```
vec(E_A(X)) = (Σ_i A_i ⊗ conj(A_i)) · vec(X)
```
The matrix `C_A = Σ_i A_i ⊗ conj(A_i)` is a nonneg matrix (in fact, PSD), and its spectral properties correspond exactly to those of E_A. Classical PF applied to C_A gives quantum PF for E_A.

**Pros:** Avoids developing abstract quantum PF; directly uses existing Mathlib vectorization.

**Cons:** Still needs classical PF; the nonneg/PSD structure of C_A needs careful handling; Choi matrix is D²×D² which creates type-level complications.

**This is the recommended primary approach.**

### 5.3 Approach C: Direct finite-dimensional algebraic argument

**Key idea:** For the specific MPS block separation problem, we don't need the full PF theorem. We need a weaker statement:

> If {A_k^σ}_σ spans M_D(ℂ) (injectivity), and `∑_k μ_k^N · tr(W_k · A_k^{σ₁}···A_k^{σ_N}) = 0` for all N and σ, then W_k = 0 for all k.

This can potentially be proved by:
1. Taking N large enough that each block's word evaluations span the full matrix algebra (this is the normality/injectivity condition).
2. Using trace non-degeneracy to extract W_k from the traced products.
3. Separating the μ_k contributions by exploiting distinct |μ_k| values.

**The key insight:** For fixed N ≥ D², the map `σ ↦ evalWord(A_k, σ)` ranges over a spanning set of M_D(ℂ). So `tr(W_k · M) = 0` for all M implies W_k = 0. The challenge is disentangling the μ_k weights.

**Direct argument for distinct |μ_k|:** If |μ_1| > |μ_2| > ⋯ > |μ_r|, then for large N, dividing by μ_1^N and taking N → ∞ isolates the k=1 term. By induction, each block separates.

**Pros:** Avoids all PF machinery; shorter; more self-contained.

**Cons:** Requires analysis-style limit arguments (which are available in Mathlib); may not handle the case of equal |μ_k| with different phases cleanly; less general.

### 5.4 Approach D: Restrict to the generic case

**Key idea:** Assume that the μ_k are all distinct (not just |μ_k| distinct). Then a Vandermonde argument works if we can produce equations with *fixed* coefficients at different powers.

**Trick:** For a fixed word w of length L, consider the family of equations indexed by N:
```
∑_k μ_k^N · tr(A_k^{w₁}···A_k^{w_L}) = ∑_k μ_k^N · tr(B_k^{w₁}···B_k^{w_L})
```
These are NOT directly available from SameMPV₂, because SameMPV₂ gives equations for words of length N, not length L with an extra μ^N factor.

**However:** If we define `c_k(w) = mpv(A_k, w) - mpv(B_k, w)`, then SameMPV₂ gives:
```
∑_k μ_k^N · c_k(σ) = 0    for all σ : Fin N → Fin d
```
The problem is that c_k(σ) depends on σ through words of length N, and N varies.

**Possible workaround:** Consider the generating function / z-transform approach. For each pair of physical indices (i,j), the sequence `N ↦ ∑_k μ_k^N · (Δ_k)_{ij}^{(N)}` where `(Δ_k)_{ij}^{(N)} = tr(M_{ij} · (E_k)^N(·))` has a specific analytic structure determined by the spectrum of E_k. The spectral decomposition of E_k then separates the contributions.

This circles back to needing some spectral theory of the transfer operator.

### 5.5 Approach E: Axiomatize and move on

**Status quo:** The current MPSLean code takes `hSep : ∀ k, SameMPV (A k) (B k)` as an explicit hypothesis. Everything else is proved. This is already a valid mathematical statement:

> "If two canonical-form MPS have the same MPV family, and the block-separation property holds, then they are related by per-block gauge transforms."

**Pros:** Already done; zero additional effort; the formalization is still valuable.

**Cons:** The separation hypothesis is not proved from `SameMPV₂`; the result is conditional.

---

## 6. Recommendations

### 6.1 Short-term (current project)

**Keep the current axiomatic approach.** The formalization is already sorry-free and the gap is clearly documented. The conditional theorem is mathematically correct and useful.

### 6.2 Medium-term (1–3 months)

**Pursue Approach C (direct algebraic argument) for the case of distinct |μ_k|.**

The argument would be:
1. Show that for injective block tensors, there exists N₀ such that the N₀-blocked tensors span the full matrix algebra (this is `IsNormal` / `IsNBlkInjective`).
2. For N ≥ N₀, the map `σ ↦ evalWord(A_k, List.ofFn σ)` has its range spanning `M_D(ℂ)`.
3. Define `Δ_k^{(N)} : M_{D_k} → ℂ` by `Δ_k^{(N)}(M) = ∑_{σ:Fin N→Fin d} tr(M · evalWord(A_k, σ)) · (tr(evalWord(A_k, σ)) - tr(evalWord(B_k, σ)))`.
4. Show that SameMPV₂ implies `∑_k μ_k^N · Δ_k^{(N)} = 0` as a linear functional.
5. For distinct |μ_k|, use a limit argument (N → ∞, dividing by the dominant μ^N) to isolate each block.
6. Conclude Δ_k = 0 for all k, which gives per-block SameMPV.

**Estimated effort:** 800–1500 LoC.  
**Dependencies:** Requires formalization of the normality condition and basic limit arguments.  
**Risk:** The limit argument needs careful handling in Lean; the case of equal |μ_k| with different phases requires a secondary Vandermonde argument on the unit circle.

### 6.3 Long-term (3–6 months)

**Contribute classical PF to Mathlib.** The Cipollina et al. (arXiv:2512.07766) formalization provides a model. Key goals:
- Formalize the classical PF eigenvalue theorem for irreducible nonneg matrices.
- Build the Choi-Jamiołkowski isomorphism.
- Derive quantum PF as a consequence.

This would be a significant Mathlib contribution (PF is on the "100 theorems" wish list) and would close the MPSLean gap in full generality.

### 6.4 Decision matrix

| Scenario | Recommendation |
|----------|---------------|
| Need to publish/share MPSLean now | Use current axiomatic approach (Approach E) |
| Want to close gap for distinct μ_k | Pursue Approach C (1–2 months) |
| Want full generality + Mathlib contribution | Pursue Approach B (3–6 months) |
| Want to maximize impact | Combine: close distinct-μ case now + contribute PF to Mathlib later |

---

## Appendix A: Key Definitions in MPSLean

### Transfer operator (from `Transfer.lean`)
```lean
noncomputable def transferMap (A : MPSTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  ∑ i : Fin d,
    (LinearMap.mulLeft ℂ (A i)).comp (LinearMap.mulRight ℂ (A i)ᴴ)
```

### Block separation hypothesis (from `PiAlgebraExtension.lean`)
```lean
theorem fundamentalTheorem_multiBlock_fromSameMPV₂
    (μ : Fin r → ℂ)
    (A B : (k : Fin r) → MPSTensor d (dim k))
    (hA : ∀ k, IsInjective (A k))
    (hSame₂ : SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B))
    -- ↓↓↓ THIS IS THE GAP ↓↓↓
    (hSep : ∀ k, SameMPV (A k) (B k)) :
    ...
```

### What SameMPV₂ gives (from `PiAlgebraExtension.lean`)
```lean
theorem sameMPV₂_summed_blocks ...
    ∑ k, (μ k) ^ N • mpv (A k) σ = ∑ k, (μ k) ^ N • mpv (B k) σ
```

## Appendix B: Precise Statement of Quantum PF

**Theorem (Quantum Perron-Frobenius, Evans-Høegh-Krohn 1978).**
Let E : M_D(ℂ) → M_D(ℂ) be a positive linear map (maps PSD to PSD). Say E is **irreducible** if the only E-invariant faces of the PSD cone are {0} and the full cone.

If E is irreducible, then:
1. ρ(E) > 0 and ρ(E) is an eigenvalue of E.
2. There exists a unique (up to scalar) eigenvector X > 0 (positive definite) with E(X) = ρ(E) · X.
3. If E(Y) = λY with |λ| = ρ(E) and Y ≥ 0, then Y is a scalar multiple of X.

**For CP maps with Kraus form E(X) = Σ_i A_i X A_i†:**
Irreducibility of E is equivalent to: the only subspace V ⊆ ℂ^D such that A_i(V) ⊆ V for all i is V = {0} or V = ℂ^D. This is closely related to the injectivity/normality condition on MPS tensors.

**Connection to classical PF:** Via the Choi-Jamiołkowski isomorphism, E is CP iff its Choi matrix `C_E = Σ_i |A_i⟩⟩⟨⟨A_i|` (where |A_i⟩⟩ = vec(A_i)) is PSD. The spectral properties of E correspond to those of C_E as a nonneg Hermitian matrix. The quantum PF theorem for irreducible CP maps can thus be derived from the classical PF theorem applied to C_E.

## Appendix C: The Choi-Jamiołkowski Shortcut

The key identity (already in Mathlib as `Matrix.kronecker_mulVec_vec`):
```
vec(A X B^T) = (B ⊗ₖ A) *ᵥ vec(X)
```

For the transfer operator:
```
vec(E_A(X)) = vec(Σ_i A_i X A_i†)
            = Σ_i vec(A_i X (A_i†))
            = Σ_i (conj(A_i) ⊗ₖ A_i) *ᵥ vec(X)
            = (Σ_i conj(A_i) ⊗ₖ A_i) *ᵥ vec(X)
```

So the "Choi matrix" of E_A is:
```
C_A = Σ_i conj(A_i) ⊗ₖ A_i
```

This is a D²×D² matrix, and:
- C_A is PSD (since it's a sum of rank-1 PSD terms)
- Eigenvalues of C_A = eigenvalues of E_A (as a linear map on M_D)
- C_A is irreducible (as a nonneg matrix) iff E_A is irreducible (as a positive map)

**This reduction is the most practical path:** classical PF for the D²×D² nonneg matrix C_A immediately gives quantum PF for E_A.

## Appendix D: References

1. D. Pérez-García, F. Verstraete, M. M. Wolf, J. I. Cirac, "Matrix Product State Representations," arXiv:quant-ph/0608197 (2006).
2. M. Sanz, D. Pérez-García, M. M. Wolf, J. I. Cirac, "A quantum version of Wielandt's inequality," arXiv:0909.5347 (2009).
3. J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, "Matrix product states and projected entangled pair states: Concepts, symmetries, theorems," Rev. Mod. Phys. 93, 045003 (2021); arXiv:2011.12127.
4. D. E. Evans, R. Høegh-Krohn, "Spectral properties of positive maps on C*-algebras," J. London Math. Soc. 17, 345–355 (1978).
5. M. M. Wolf, "Quantum Channels & Operations: Guided Tour," Lecture Notes, TU Munich (2012).
6. M. Cipollina, M. Karatarakis, F. Wiedijk, "Formalized Hopfield Networks and Boltzmann Machines," arXiv:2512.07766 (2025). [Lean 4 classical PF]
7. J. Divasón, O. Kunčar, R. Thiemann, A. Yamada, "Perron-Frobenius Theorem for Spectral Radius Analysis," Isabelle AFP (2016).
8. R. Thiemann, "Stochastic Matrices and the Perron-Frobenius Theorem," Isabelle AFP (2017).
9. A. Meiburg et al., "A Formalization of the Generalized Quantum Stein's Lemma in Lean," arXiv:2510.08672 (2025). [Lean-QuantumInfo]
