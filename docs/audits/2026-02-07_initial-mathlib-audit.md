---
title: Initial Mathlib Audit for MPS Formalization
date: 2026-02-07
author: AI research assistant (search agent)
purpose: >
  Systematic audit of Mathlib v4.27.0 for the building blocks needed to
  formalize the Fundamental Theorem of Matrix Product States.  Covers
  matrix algebras, simple rings, Skolem–Noether, trace, block diagonals,
  and proposes the initial TNLean architecture.
---

I set up the Lean/Mathlib workspace as requested:

- Created a Lean package `TNLean` (Mathlib template) with `mathlib` pinned to `v4.27.0` in `lakefile.toml`.
- Fetched the precompiled cache and verified `lake build` succeeds.

Below is a systematic audit of Mathlib w.r.t. the building blocks you listed, followed by an architecture proposal aimed at being maintainable and extensible (e.g. toward PEPS).

---

## A. Linear algebra foundations

### A1. `Matrix.trace` (trace + cyclicity)
**Exists**: Yes.  
**Main import**: `Mathlib.LinearAlgebra.Matrix.Trace`

**What’s there**
- `Matrix.trace : Matrix n n R → R`
- Cyclicity / commutation under trace:
  - `Matrix.trace_mul_comm : (A * B).trace = (B * A).trace`
  - `Matrix.trace_mul_cycle : (A * B * C).trace = (C * A * B).trace`
- Useful extras:
  - `Matrix.trace_conjTranspose`
  - trace as linear map: `Matrix.traceLinearMap`
  - trace over block diagonal: `Matrix.trace_blockDiagonal`, `Matrix.trace_blockDiagonal'`

**Maturity**: High; this is standard Mathlib linear algebra with many simp lemmas.

**Likely gap for MPV work**
- You’ll want a convenient lemma for the cyclicity of `trace (M₁ * … * M_N)` for arbitrary `N` (can be done by induction using the existing 2–3 factor cycle lemmas).

---

### A2. Block diagonal matrices
**Exists**: Yes.  
**Main import**: `Mathlib.Data.Matrix.Block`

**What’s there**
- Homogeneous blocks: `Matrix.blockDiagonal : (o → Matrix m n α) → Matrix (m×o) (n×o) α`
- Dependent block sizes: `Matrix.blockDiagonal' : (∀ i, Matrix (m i) (n i) α) → Matrix (Σ i, m i) (Σ i, n i) α`
- Many “apply” lemmas and injectivity theorems, transpose lemmas, plus ring/additive hom versions.

**Maturity**: Good; widely usable for canonical-form-style “direct sum” decompositions.

**Gap**
- Canonical form for MPS usually wants “block diagonal up to similarity” plus bookkeeping of block dimensions and embeddings. Mathlib gives the raw block-diagonal construction; you’ll still build higher-level “canonical decomposition” structures yourself.

---

### A3. Invertible matrices / units / `GL`
**Exists**: Yes.  
**Imports**
- Units/`GL`: `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`
- Inverses from det / nonsingular inverse: `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- Various invertibility lemmas: `Mathlib.Data.Matrix.Invertible`, `Mathlib.LinearAlgebra.Matrix.SemiringInverse`

**What’s there**
- Invertibles as units: `(Matrix n n R)ˣ`
- Alias notation: `GL n R` is literally `(Matrix n n R)ˣ` (see `Matrix.GeneralLinearGroup`).
- Many lemmas around `IsUnit`, existence of inverses, etc.

**Maturity**: High.

**Good practice for gauge transforms**
- Represent the gauge as `X : GL (Fin D) ℂ` (or `(Matrix (Fin D) (Fin D) ℂ)ˣ`) so you get `X⁻¹` without side conditions.

---

### A4. Similarity / conjugation by an invertible matrix
**Exists**: Partially (not as “matrix similarity” API, but as general conjugacy).  
**Imports**
- Conjugacy: `Mathlib.Algebra.Group.Conj` (`IsConj`)
- `GL` as units: `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`

**What’s there**
- `IsConj a b` in a monoid means “∃ unit c, c * a * c⁻¹ = b”.
  - This directly applies to `a b : Matrix n n R` since units are invertible matrices.

**Maturity**: The group-theoretic infrastructure is mature.

**Gap**
- There’s no dedicated `Matrix.IsSimilar` wrapper, and nothing out-of-the-box for *simultaneous* similarity of a family `i ↦ A i`. You’ll define your own “gauge equivalence” predicate:
  \[
  \exists X \in GL(D),\; \forall i,\; B^i = X A^i X^{-1}.
  \]

---

### A5. Invariant subspaces (for one map and for families)
**Exists**: Yes (and nicer than expected).  
**Imports**
- Single endomorphism invariant submodules: `Mathlib.Algebra.Module.Submodule.Invariant`
- A “family” pattern via representations: `Mathlib.RepresentationTheory.Submodule`

**What’s there**
- `Module.End.invtSubmodule (f : End R M) : Sublattice (Submodule R M)`
- Characterizations:
  - `p ∈ f.invtSubmodule ↔ p ≤ p.comap f`
  - `↔ p.map f ≤ p`
  - `↔ ∀ x ∈ p, f x ∈ p`
- For families, the pattern is: take an infimum over the index set (as `Representation.invtSubmodule` does).

**Maturity**: Good, and scalable for block decomposition arguments.

---

### A6. Tensor products of matrices
**Exists**: Yes.  
**Imports**
- Kronecker: `Mathlib.LinearAlgebra.Matrix.Kronecker`
- Module tensor product: `Mathlib.LinearAlgebra.TensorProduct.Basic`

**What’s there**
- `Matrix.kronecker` and notation `⊗ₖ`
- Also tensoring entries into an actual `TensorProduct`: `Matrix.kroneckerTMul` / `⊗ₖₜ`

**Maturity**: Good.

**Gap**
- The “vectorization” bridge (turning `X ↦ A X B` into a Kronecker action on `vec X`) is not a standard packaged result; you’ll likely write that yourself if you want to use Kronecker to analyze the transfer operator.

---

## B. Functional analysis / operator theory

### B1. Completely positive maps on matrices
**Exists**: Yes (but seems isolated/young).  
**Imports**
- CP maps: `Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap`
- C⋆-matrices: `Mathlib.Analysis.CStarAlgebra.CStarMatrix`

**What’s there**
- `CompletelyPositiveMap A₁ A₂` for (non-unital) C⋆-algebras.
- Positivity is defined via positivity of entrywise application on `CStarMatrix (Fin k) (Fin k) A`.

**Maturity**
- The definitions exist, but the file appears “standalone”: it is not (yet) broadly used elsewhere in Mathlib, and I could not find Kraus/Stinespring/Choi-style lemmas.

**Gap**
- No ready lemma of the form “a map `X ↦ ∑ i, V_i X V_i†` is completely positive”. You would likely need to develop that.

---

### B2. Quantum channels (CPTP)
**Exists**: No (as a packaged concept).  
**Gap shape**
- You’d want something like:
  - `QuantumChannel A := CompletelyPositiveMap A A ∧ TracePreserving`
  - or a structure bundling CP + unital/trace-preserving depending on the convention.
- There is no standard `trace` functional on `CStarMatrix` wired into a “trace-preserving” predicate in the CP-map file.

---

### B3. Positive semidefinite / positive definite matrices
**Exists**: Yes.  
**Import**: `Mathlib.LinearAlgebra.Matrix.PosDef`

**What’s there**
- `Matrix.PosSemidef`, `Matrix.PosDef`, many closure properties.
- Trace nonnegativity, etc.

**Maturity**: Solid and broadly useful.

**Gap**
- The bridge between this matrix positivity and the C⋆-algebra positivity used in `CompletelyPositiveMap` is not “one click”; you may need glue lemmas if you mix the two worlds (`Matrix` vs `CStarMatrix`).

---

### B4. Spectral radius of a linear map
**Exists**: Yes (in the general spectrum framework).  
**Imports**
- `Mathlib.Analysis.Normed.Algebra.Spectrum` (spectral radius in normed algebras)
- `Mathlib.Algebra.Algebra.Spectrum.Basic`
- Eigenvalue theory: `Mathlib.LinearAlgebra.Eigenspace.Basic`

**What’s there**
- `spectralRadius 𝕜 a` for `a : A` in a normed algebra.
- `spectrum 𝕜 a` applies to endomorphisms since `Module.End` is an algebra.

**Maturity**: High for general spectral theory.

**Gap for your use-case**
- The “quantum Perron–Frobenius” facts you need (simple peripheral eigenvalue, full-rank positive eigenvectors) are not present for CP maps.

---

### B5–B6. Perron–Frobenius + primitivity/irreducibility for positive maps
**Exists**:
- For *entrywise nonnegative matrices*: definitions of irreducible/primitive exist.
  - `Mathlib.LinearAlgebra.Matrix.Irreducible.Defs` defines `Matrix.IsIrreducible`, `Matrix.IsPrimitive` (graph-theoretic characterization).
- For *Perron–Frobenius eigenvector/eigenvalue theorems*: I did **not** find them.
- For *primitive/irreducible CP maps (quantum channels)*: **not present**.

**Gap shape**
- You’ll need substantial new theory to go from “primitive CP map” to the spectral properties used in the paper’s “normal tensor” definition.

---

## C. Tensor network specific
**Exists**: I found no existing formalization of MPS / tensor networks / finitely correlated states in Mathlib.

So you’re essentially starting from scratch at the “tensor network layer”.

---

## D. Supporting infrastructure

### D1. `Fin n → Matrix` as tensor representation
**Exists**: Trivially yes; this is just a function type.
- MPS tensor can be `A : Fin d → Matrix (Fin D) (Fin D) ℂ`.

**Maturity**: Core Lean/Mathlib.

---

### D2. Big operators (sums/products over indices)
**Exists**: Yes.  
**Imports**
- Notation: `Mathlib.Algebra.BigOperators.Group.Finset.Defs` (and typically `open scoped BigOperators`)

**Maturity**: Very high.

---

### D3. Finite-dimensional Hilbert spaces
**Exists**: Yes; mature.  
**Imports**
- `Mathlib.Analysis.InnerProductSpace.Defs` etc.
- Inner-product tensor products: `Mathlib.Analysis.InnerProductSpace.TensorProduct`

**Important nuance**
- The inner product structure on `TensorProduct` is available (recent, 2025), and the file itself notes TODOs like a general “complete space of tensor products”.
- For **finite-dimensional** spaces (your MPV spaces are finite-dimensional), completeness can be obtained via general `FiniteDimensional` ⇒ `CompleteSpace` lemmas, so this is likely workable.

---

### D4. Working over `ℂ`
**Exists**: Yes.
- `ℂ` is a `NormedField`, `RCLike`, `IsROrC`, etc.
- `Fin n → ℂ` is a standard finite-dimensional inner product space.

---

# What’s missing (high-level)
The dominant gap is the operator-theoretic part of the paper’s “normal tensor = primitive quantum channel” story:

1. a Mathlib-level notion of “quantum channel” (CPTP / CPU, etc),
2. definitions of irreducible/primitive for CP maps,
3. Perron–Frobenius–type theorems for CP maps on finite-dimensional matrix algebras,
4. bridges between CP-map positivity and `Matrix.PosSemidef` / `Matrix.PosDef`.

---

## Proposed scalable project architecture (MPS now, PEPS later)

### Guiding design principle
Separate **(i) tensor-network combinatorics and algebra** from **(ii) analytic/positivity theory**. Then you can:
- prove the *Fundamental Theorem* first for an algebraic “injective/minimal” interface (linear algebra only),
- later prove that the paper’s “primitive transfer operator” implies that interface (operator theory).

This is the best way to stay productive while keeping the project mathematically faithful and future-proof.

---

## 1) Layered modules (suggested file structure)

### Layer 0: Mathlib imports only
No project code yet; just rely on Mathlib.

### Layer 1: Core MPS algebra (`Matrix`-first)
**Goal**: define MPVs as coefficient functions, gauge actions, and basic lemmas.
- `TNLean/MPS/Tensor.lean`
  - `MPSTensor d D := Fin d → Matrix (Fin D) (Fin D) ℂ`
  - gauge action by `GL (Fin D) ℂ`
- `TNLean/MPS/Words.lean`
  - represent index strings as `List (Fin d)` or as `Fin N → Fin d`
  - define product evaluation `evalWord : List (Fin d) → Matrix …`
- `TNLean/MPS/MPV.lean`
  - define coefficients \(c_A(w) := \mathrm{tr}(\prod A^{i})\)
  - define “same MPVs for all \(N\)” as `∀ N, ∀ i : Fin N → Fin d, coeffA i = coeffB i`
  - (optionally) prove equivalence with equality of coefficients on all words

This avoids Hilbert-space tensor products until you actually need them.

### Layer 2: Transfer operator as a linear map (and optionally as CP map)
- `TNLean/MPS/Transfer.lean`
  - `E_A : Matrix D D ℂ →ₗ[ℂ] Matrix D D ℂ` via `X ↦ ∑ i, A i * X * (A i)ᴴ`
  - show linearity, basic identities, gauge covariance `E_{XAX⁻¹} = conj … (E_A)` etc.

Keep this purely linear-algebraic at first.

### Layer 3: “Normal / injective” interface (two options)
**Option (A): paper-faithful but heavy**
- Define `Normal` using “primitive CP map” and then build PF theory locally.
- This is a *large* development effort.

**Option (B): algebraic interface first (recommended)**
- Define an `Injective`/`Minimal` property that is sufficient to prove gauge equivalence.
  - E.g. a spanning property of products `span { A^{i₁}⋯A^{i_L} } = ⊤` (a standard injectivity criterion).
  - Or a control/observe minimality formulation (weighted automata / linear representations style).
- Later prove: `primitive transfer operator` ⇒ `Injective` (requires operator theory, but can come later).

This makes the Fundamental Theorem tractable early.

### Layer 4: Canonical form / block decomposition
- Define a structure encapsulating:
  - a finite index type of blocks `K`,
  - block sizes `Dk : K → ℕ`,
  - an identification of the total virtual space with a sigma type (`Σ k, Fin (Dk k)`)
  - `A^i` is block diagonal w.r.t. that decomposition (`Matrix.blockDiagonal'`)
  - each block is injective/normal, plus scalars `μ_k`.

You can start by **assuming** canonical form as an input structure, instead of proving existence.

### Layer 5: Fundamental theorem proofs
Prove in increasing generality:
1. **Single-block injective case**: same MPVs ⇒ ∃ invertible `X` s.t. `B^i = X A^i X⁻¹`.  
2. **Block case**: identify block correspondence, gauge transforms blockwise, permutation of blocks, scalars, etc.  
3. Package “basis of normal tensors” as a quotient/modulo similarity + minimality.

---

## 2) What to upstream vs keep local

### Strong candidates to upstream
- A clean definition of “quantum channel” building on `CompletelyPositiveMap`, once it stabilizes.
- Lemmas about Kraus-form CP maps, if written generally.
- Any general “primitive positive map on finite-dimensional C⋆-algebra ⇒ PF spectral structure” results (but this is big, likely a long-term upstream effort).

### Keep local initially
- MPS/PEPS-specific canonical-form structures and gauge theorems.
- Any “blocking” combinatorics (joining tensors, reindexing, periodicity issues).

This division keeps Mathlib PRs small and reusable, while your project remains focused.

---

## 3) `Matrix` vs `LinearMap` (recommendation)
Use **both**, but with a clear policy:

- Use `Matrix` for:
  - the literal tensor data \(A^i\),
  - trace expressions,
  - block diagonals,
  - explicit gauge conjugations.

- Use `LinearMap` for:
  - invariant submodule lattices (`Module.End.invtSubmodule`),
  - abstract linear algebra (kernels, ranges, spans),
  - spectrum/eigenspaces when needed.

Bridge them via `Matrix.toLin'` / `LinearMap.toMatrix` on `Fin`-indexed spaces when necessary, but don’t force everything into one representation.

---

## 4) Generalizing to PEPS later
Design your tensor definitions so that:
- “virtual indices” are an explicit *tuple of spaces* (for PEPS: 4 virtual legs),
- “gauge group” is a product of `GL` actions, one per virtual leg,
- “contraction” is expressed via a generic “network evaluation” that reduces to trace/product in 1D.

If you keep MPS as a special case of “tensor with two virtual legs + periodic contraction = trace”, then the PEPS fundamental theorem will feel like a natural extension rather than a rewrite.

---

If you want, next I can produce a concrete dependency graph (nodes = Lean files/definitions/lemmas) for the **injective single-block** proof path vs the **primitive CP map** path, so you can decide which route to implement first.