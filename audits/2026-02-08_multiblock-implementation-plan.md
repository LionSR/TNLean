---
title: "Multi-block implementation plan: toward the full Fundamental Theorem"
date: 2026-02-08
author: AI research assistant (search agent)
purpose: >
  Research and implementation plan for extending MPSLean from the
  single-block injective Fundamental Theorem to the multi-block
  canonical-form version (arXiv:2011.12127, Thm 4.1).  Covers phased
  execution plan, Vandermonde separation strategy, and effort estimates.
---

# Toward the *full* Fundamental Theorem (multi-block / canonical form) as stated in `2011.12127`

_Date_: 2026-02-08

This note is a “research + implementation plan” for extending **MPSLean** from the current
**single-block (injective) Fundamental Theorem** to the **multi-block / canonical-form**
version presented in the tensor-network review contained in this repo:

- `2011.12127/TN-Review-main.tex` (Section 4, “The Fundamental Theorem of Matrix Product Vectors”).

The goal is to mirror the structure in that review (canonical form, normal tensors, basis of normal tensors,
Fundamental Theorem for proportional MPVs, etc.), but in a Lean-friendly way.

---

## 1. What `2011.12127` actually states (where to look)

All references below are to **`2011.12127/TN-Review-main.tex`**.

### 1.1 MPVs
- MPV definition is Eq. (MPV) around lines ~1731–1735.

### 1.2 Canonical form + normal tensors
- Block-diagonal / canonical decomposition is Eq. (II\_Aiplusk1) around ~1799–1802:
  \(A^i = \bigoplus_{k=1}^r \mu_k A_k^i\).
- Transfer operator is Eq. (Ek) around ~1804–1808:
  \(\mathcal E_k(X) = \sum_i A_k^i X A_k^{i\dagger}\).
- “Normal tensor” and “canonical form” are Definition 4.1 around ~1827–1837:
  normal := transfer operator primitive; canonical form := direct sum of normal blocks.

### 1.3 Basis of normal tensors
- Definition 4.2 around ~1846–1850: basis of normal tensors is a set of normal tensors
  which spans all MPVs and is eventually linearly independent.
- Proposition ~1852–1859 characterizes such bases via gauge+phase equivalence and minimality.
- They rewrite canonical form in terms of a basis and obtain a decomposition of MPVs
  (Eq. (decBSV), around ~1883–1885):
  \(|V^N(A)\rangle = \sum_j (\sum_q \mu_{j,q}^N)\, |V^N(A_j)\rangle\).

### 1.4 Fundamental Theorem statements
- Theorem “Fundamental Theorem for proportional MPVs” (label `thm1`) around ~1891–1894:
  if canonical-form tensors generate MPVs proportional for all N, then the bases match up
  (same number of basis blocks) and blocks are related by gauge + phase.
- Corollary “Fundamental Theorem for equal MPVs” (label `II_cor2`) around ~1896–1899:
  if canonical-form tensors generate the same MPV for all N, then bond dimensions match
  and there is a single global similarity transform.
- Additional generalization without blocking: Theorem `thm:fundamental-general` around ~1911–1918.

---

## 2. Where MPSLean currently is

### 2.1 Already done (single-block)
- `MPSLean/MPS/FundamentalTheorem.lean` proves the **injective/single-block** statement:
  `IsInjective A ∧ SameMPV A B → GaugeEquiv A B`.

### 2.2 Already scaffolded (multi-block data)
- `MPSLean/MPS/CanonicalForm.lean` defines
  - `CanonicalForm` with blocks `blockTensor k`, scalars `μ k`, injectivity per block, etc.
  - `CanonicalForm.toTensor` builds the block-diagonal tensor using `Matrix.blockDiagonal'`
    and a `Matrix.reindex` along `finSigmaFinEquiv`.

### 2.3 Important mismatch with the paper
The review’s “normal tensor” is defined via **primitive CP maps** (transfer operators).  
MPSLean currently defines “normal” algebraically as “injective after blocking”:

- `IsNormal A := ∃ N, IsNBlkInjective A N` (in `Injective.lean`).

This is closer to the *injectivity after blocking* notion; the paper states equivalence using
(quantum) Wielandt, which is *not* formalized in Mathlib.

**Recommendation:** for the multi-block Fundamental Theorem, keep the algebraic notion
(`IsNormal`) as the working definition. If later you want to match the paper literally,
add a separate CP-map layer and prove the equivalence as an optional refinement.

---

## 3. First refactor needed: allow comparing tensors of different bond dimension

In the paper, Corollary `II_cor2` *concludes* that bond dimensions match.
So the statement must allow starting with

- `A : MPSTensor d D₁`, `B : MPSTensor d D₂`.

Right now, `SameMPV` and `GaugeEquiv` are defined only for a fixed `D`.

### 3.1 Add dimension-polymorphic MPV equality
Suggested new definition (do **not** delete the old one yet):

```lean
/-- MPV equality for possibly different bond dimensions. -/
def SameMPV₂ {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) : Prop :=
  ∀ (N : ℕ) (σ : Fin N → Fin d), MPSTensor.mpv A σ = MPSTensor.mpv B σ
```

Similarly for “proportional MPVs” (needed for Theorem `thm1`):

```lean
/-- Proportionality of MPVs: for each N there exists c_N with V_N(A)=c_N V_N(B). -/
def ProportionalMPV₂ {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) : Prop :=
  ∀ N, ∃ c : ℂ, ∀ σ : Fin N → Fin d, MPSTensor.mpv A σ = c * MPSTensor.mpv B σ
```

### 3.2 Generalize “gauge equivalence” across dimensions
A natural notion is “gauge up to reindexing”.

```lean
/-- Gauge equivalence allowing different bond dimensions (via reindexing along an equivalence). -/
def GaugeEquiv₂ {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂) : Prop :=
  ∃ e : (Fin D₁ ≃ Fin D₂), ∃ X : GL (Fin D₂) ℂ,
    ∀ i : Fin d,
      B i = X * (Matrix.reindex e e (A i)) * X⁻¹
```

This uses Mathlib’s `Matrix.reindex` / `Matrix.reindexAlgEquiv`.

---

## 4. Multi-block core lemma you need first: MPV of a block diagonal tensor

This is the formal version of Eq. (decBSV) but *without* grouping identical blocks.

### 4.1 Target lemma (direct sum expansion)
For `C : CanonicalForm d` and `σ : Fin N → Fin d`:

\[
  mpv\,(C.toTensor)\,σ
  = \sum_{k : Fin C.numBlocks} (C.μ k)^N \cdot mpv\,(C.blockTensor k)\,σ.
\]

This is the workhorse for *everything* multi-block.

### 4.2 Proof strategy (Lean-friendly)
Avoid entrywise `Fin totalDim` reasoning.

1. Work on the Sigma index type (the one used by `Matrix.blockDiagonal'`).
2. Prove an induction lemma:
   `evalWord` of a blockDiagonal is blockDiagonal of `evalWord`s.
   Use `Matrix.blockDiagonal'_mul` and `Matrix.blockDiagonal'_smul`.
3. Turn `trace (blockDiagonal' ...)` into `∑ trace ...` using `Matrix.trace_blockDiagonal'`.
4. Only at the very end use a lemma `trace (reindex e e M) = trace M`.

This matches the advice in `MultiBlockAudit.md`.

---

## 5. Add the “phase + gauge” relation (needed for the proportional theorem)

Theorem `thm1` uses relations of the form
\(B^i = e^{i\phi} X A^i X^{-1}\).

### 5.1 Define blockwise gauge+phase
Add a predicate:

```lean
/-- Gauge equivalence up to a global phase factor (per tensor). -/
def GaugePhaseEquiv {d D : ℕ} (A B : MPSTensor d D) : Prop :=
  ∃ (X : GL (Fin D) ℂ) (ζ : ℂ),
    (∀ i, B i = ζ • (X * A i * X⁻¹))
```

(You can restrict `ζ` to `Complex.abs ζ = 1` later.)

### 5.2 Show gauge+phase ⇒ proportional MPVs
Lemma to prove:

```lean
GaugePhaseEquiv A B → ProportionalMPV₂ A B
```

and the proportionality scalar for length `N` is exactly `ζ^N`.
This is a short induction using `evalWord`.

---

## 6. Formalizing “basis of normal tensors” (paper Definition 4.2)

The paper’s definition has two parts:

1. For each N, the MPV generated by A lies in the span of the basis MPVs.
2. For N > N0, the basis MPVs become linearly independent.

### 6.1 How to represent MPVs as vectors in Lean
For each `N`, your “Hilbert space” can be represented as the function space

- `((Fin N → Fin d) → ℂ)`

and the MPV vector is exactly

- `fun σ => mpv A σ`.

So you can use Mathlib’s `LinearIndependent ℂ` on those functions.

### 6.2 A minimal Lean structure
Suggested structure for a “basis of normal tensors” associated to a canonical form `C`:

- data: indices `g : ℕ`, and a map `rep : Fin g → Fin C.numBlocks`
- properties:
  - every block is gauge+phase equivalent to some representative;
  - representatives are pairwise *not* gauge+phase equivalent;
  - eventual linear independence of the representative MPVs.

This matches the *spirit* of Proposition `prop:char-BNT` without importing the mixed transfer operator.

---

## 7. Proportional theorem (`thm1`) in Lean: what it really needs

To prove the paper’s Theorem `thm1` (for proportional MPVs) you will need:

1. The block-diagonal MPV expansion (Section 4).
2. A basis notion and its eventual linear independence.
3. A way to “identify blocks” from proportionality.

A clean proof route is:

- Expand both MPVs as a linear combination of basis MPVs.
- Use linear independence for large N to identify basis elements up to permutation.
- Reduce each matched pair of basis tensors to the **single-block fundamental theorem**
  (your existing Lean result), possibly after blocking to reach injectivity.
- Account for the phase by comparing proportionality scalars as N varies.

This avoids the CP-map spectral theory used in the physics proof.

---

## 8. Equal theorem (Corollary `II_cor2`) and what changes

Once `thm1` is available, Corollary `II_cor2` is a special case where the proportionality scalar is 1.
Key consequences you will formalize:

1. **Same bond dimension**: `D₁ = D₂` (or at least `Fin D₁ ≃ Fin D₂`).
2. **Single global similarity**: `∃ X, ∀ i, A i = X * B i * X⁻¹` (up to reindexing).

This will require a lemma that a block permutation + blockwise conjugations assemble into a single
conjugation on the full block-diagonal matrix (construct a block-permutation matrix).

---

## 9. About the “no blocking” theorem (`thm:fundamental-general`)

Theorem `thm:fundamental-general` introduces an extra diagonal matrix `Z` commuting with `A` to
account for periodic eigenvalues on the unit circle.

Formalizing this *faithfully* will likely require some spectral theory of the transfer operator
(or at least the periodic decomposition), so it’s best treated as a **Phase 2** goal.

A practical compromise is:

- first formalize the blocked/normal case (primitive or injective-after-blocking),
- then add periodicity later (root-of-unity phases).

---

## 10. Concrete file plan for MPSLean

1. **Defs upgrade** (`MPSLean/MPS/Defs.lean`):
   - add `SameMPV₂`, `ProportionalMPV₂`, and `GaugeEquiv₂`.

2. **Canonical form computations** (`MPSLean/MPS/CanonicalForm.lean` + new `MultiBlock.lean`):
   - prove `mpv_toTensor_eq_sum`.
   - prove permutation invariance lemmas up to reindex/gauge.

3. **Basis layer** (new file `BasisNormal.lean`):
   - define “basis of normal tensors” in a Lean-usable way.
   - prove basic closure lemmas (span, independence stability under gauge-phase).

4. **Main theorems** (new file `FundamentalTheoremMulti.lean`):
   - prove a Lean version of `thm1` (proportional MPVs) under your basis hypotheses.
   - derive equal case / global gauge equivalence.

---

## 11. If you *really* want the CP-map/Perron–Frobenius route

You would need to build a separate library for

- CP maps on `Matrix (Fin D) (Fin D) ℂ` in Mathlib’s C⋆-algebra framework,
- primitivity/irreducibility of CP maps,
- quantum Perron–Frobenius (full-rank positive eigenvectors, uniqueness, peripheral spectrum).

The `or4nge19/MCMC` repository has an extensive PF development **for entrywise nonnegative real matrices**;
it is an excellent blueprint for the *topology + variational characterization* style proof, but it is
not directly applicable to completely positive maps.

So unless your goal is explicitly to formalize quantum PF, the algebraic normality approach is the
fastest path to a complete multi-block theorem.

