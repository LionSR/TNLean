---
title: "Multi-block MPS audit: Mathlib support & gaps"
date: 2026-02-08
author: AI research assistant (search agent)
purpose: >
  Assess Mathlib readiness for formalizing multi-block / canonical-form
  versions of the Fundamental Theorem of MPS.  Inventories block-diagonal,
  Kronecker, Vandermonde, CP map, and spectral theory APIs; identifies
  critical gaps (Perron–Frobenius, Choi, Kraus).
---

# Multi-block MPS audit: Mathlib support & gaps

_Date_: 2026-02-08

**Goal.** Assess how ready Mathlib is (as used by this repo) for formalizing *multi-block / canonical-form* versions of the Fundamental Theorem of Matrix Product States (MPS), with an emphasis on:

* dependent block-diagonal constructions (`Matrix.blockDiagonal'`),
* semisimple algebra decompositions / direct products of matrix algebras,
* commutants/centralizers,
* positivity / completely positive (CP) maps and Perron–Frobenius-style results for transfer operators.

**Environment scanned (this workspace):**

* Lean: `leanprover/lean4:v4.27.0`
* Mathlib: `v4.27.0` (`.lake/packages/mathlib` commit `a3a10db0e9d66acbebf76c5e6a135066525ac900`)
* Scan date: 2026-02-08

---

## Topic 1 — Block-diagonal matrices (including dependent blocks) and mixed block operations

### Present in Mathlib
Core API lives in `Mathlib/Data/Matrix/Block.lean`.

**(A) 2×2 block matrices**

* `Matrix.fromBlocks` plus projections `Matrix.toBlocks₁₁`, `toBlocks₁₂`, `toBlocks₂₁`, `toBlocks₂₂`.
* Useful lemmas:
  * `Matrix.fromBlocks_multiply` (block multiplication formula)
  * `Matrix.fromBlocks_diagonal_pow` (powers of block-diagonal 2×2 matrices)
  * `Matrix.fromBlocks_mulVec`, `Matrix.vecMul_fromBlocks` (vector action)
  * transpose and adjoint structure: `Matrix.fromBlocks_transpose`, `Matrix.fromBlocks_conjTranspose`

**(B) Homogeneous block diagonal (`blockDiagonal`)**

* `Matrix.blockDiagonal : (o → Matrix m n α) → Matrix (m × o) (n × o) α`
* Algebraic structure:
  * `Matrix.blockDiagonalAddMonoidHom`
  * `Matrix.blockDiagonalRingHom`
  * lemmas: `Matrix.blockDiagonal_mul`, `Matrix.blockDiagonal_pow`, …
* Extraction: `Matrix.blockDiag` is left-inverse to `blockDiagonal`, with `Matrix.blockDiag_blockDiagonal`.

**(C) Dependent block diagonal (`blockDiagonal'`)**

* `Matrix.blockDiagonal' : (∀ i, Matrix (m' i) (n' i) α) → Matrix (Σ i, m' i) (Σ i, n' i) α`
* Key lemmas and structure:
  * elementwise control: `Matrix.blockDiagonal'_apply_eq`, `Matrix.blockDiagonal'_apply_ne`
  * functoriality: `Matrix.blockDiagonal'_map`, `Matrix.blockDiagonal'_transpose`, `Matrix.blockDiagonal'_conjTranspose`
  * additive/multiplicative structure:
    * `Matrix.blockDiagonal'_add`, `Matrix.blockDiagonal'_mul`, `Matrix.blockDiagonal'_pow`
    * `Matrix.blockDiagonal'AddMonoidHom`, `Matrix.blockDiagonal'RingHom`
  * extraction: `Matrix.blockDiag'` and `Matrix.blockDiag'_blockDiagonal'` (left-inverse), plus injectivity `Matrix.blockDiagonal'_injective`.

**(D) General-purpose “extract a block” tools**

Still in `Mathlib/Data/Matrix/Block.lean`:

* `Matrix.toBlock` and `Matrix.toSquareBlockProp` / `Matrix.toSquareBlock` (submatrix extraction based on a predicate or block label).
* Mixed-block multiplication lemmas:
  * `Matrix.toBlock_mul_eq_mul`
  * `Matrix.toBlock_mul_eq_add`

### Relevance to multi-block MPS

This repo already uses `blockDiagonal'` exactly as intended. See `MPSLean/MPS/CanonicalForm.lean`:

* `CanonicalForm.toTensor` builds a block-diagonal tensor using `Matrix.blockDiagonal'` and then `Matrix.reindex` along `finSigmaFinEquiv`.

This is a strong sign that the *data representation* aspect of multi-block canonical forms is well-supported.

### Gaps / friction points

* There are **no convenience lemmas** for `mulVec`/`vecMul` for `blockDiagonal'` analogous to the 2×2 `fromBlocks_mulVec` lemmas.
* `blockDiag`/`blockDiag'` are only `AddMonoidHom`s in Mathlib (no bundled `RingHom`), which makes ring-level rewriting slightly more manual.
* There is no out-of-the-box API for common “block diagonal + permutation reindexing” patterns (common in canonical-form uniqueness up to block permutation).

---

## Topic 2 — Determinant / invertibility facts for block structures

### Present in Mathlib

**(A) Block-triangular determinant theorems** (`Mathlib/LinearAlgebra/Matrix/Block.lean`)

* Predicate: `Matrix.BlockTriangular`.
* Determinant factorization:
  * `Matrix.BlockTriangular.det`
  * `Matrix.BlockTriangular.det_fintype` (nice form when the block-index type is a `Fintype`).

Mathlib also proves `blockDiagonal'` is block-triangular:

* `Matrix.blockTriangular_blockDiagonal'` (and the homogeneous version `blockTriangular_blockDiagonal`).

So **a `det (blockDiagonal' …)` formula is derivable**, though not provided as a dedicated lemma.

**(B) Invertibility and inverses of block-triangular matrices** (`Mathlib/LinearAlgebra/Matrix/Block.lean`)

There is a nontrivial API for invertible block-triangular matrices, e.g.

* `Matrix.BlockTriangular.inv_toBlock`
* `Matrix.BlockTriangular.invertibleToBlock`
* `Matrix.blockTriangular_inv_of_blockTriangular` (inverse of a block-triangular matrix is block-triangular)

**(C) Determinant of homogeneous block diagonal** (`Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`)

* `Matrix.det_blockDiagonal`:
  
  ```lean
  theorem det_blockDiagonal (M : o → Matrix n n R) :
    (blockDiagonal M).det = ∏ k, (M k).det
  ```

### Gaps / friction points

* No dedicated lemma `det_blockDiagonal'` (dependent blocks). Users must combine:
  * `blockTriangular_blockDiagonal'` + `BlockTriangular.det_fintype`
  * and prove that each diagonal block `toSquareBlock Sigma.fst k` is definitionaly `M k`.
* No lemma characterizing **units/invertibility** of `blockDiagonal'` in terms of per-block units.
* No lemma stating that the inverse of a block-diagonal matrix is block-diagonal:
  
  ```lean
  (blockDiagonal' M)⁻¹ = blockDiagonal' (fun k => (M k)⁻¹)
  ```

These are “quick wins”: they are true and would make multi-block proofs substantially cleaner.

---

## Topic 3 — Direct products of matrix algebras (Wedderburn–Artin)

### Present in Mathlib

Mathlib has strong semisimple algebra structure theorems.

**(A) General Wedderburn–Artin** (`Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean`)

Highlights:

* `IsSimpleRing.exists_algEquiv_matrix_divisionRing` / `..._end_mulOpposite`
* `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing`

**(B) Specialization to algebraically closed fields** (`Mathlib/RingTheory/SimpleModule/IsAlgClosed.lean`)

This is especially relevant for MPS over `ℂ`:

* `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`
* `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`

### Relevance to multi-block MPS

Multi-block canonical forms often amount to saying that some finite-dimensional algebra generated by the tensors decomposes into a product of full matrix algebras; this is exactly the territory of Wedderburn–Artin.

### Gaps / friction points

* Bridging from “concrete span of a set of matrices is the whole algebra / is semisimple” to the hypotheses of `IsSemisimpleRing` can be nontrivial.
* Wedderburn–Artin gives *existence* of an isomorphism to a product of matrix algebras; multi-block canonical forms frequently need a *more explicit*, computational block-diagonal model, and to track how specific elements map.

---

## Topic 4 — Commutants / centralizers (for uniqueness & intertwiner arguments)

### Present in Mathlib

**(A) Star-subalgebra centralizers / commutants** (`Mathlib/Algebra/Star/Subalgebra.lean`)

* `StarSubalgebra.centralizer` (docstring: “centralizer, or commutant”).
* Useful lemmas:
  * `StarSubalgebra.mem_centralizer_iff`
  * `StarSubalgebra.adjoin_le_centralizer_centralizer` (bicommutant-style inclusion)

**(B) Von Neumann algebras** (`Mathlib/Analysis/VonNeumannAlgebra/Basic.lean`)

* `VonNeumannAlgebra.commutant` and `VonNeumannAlgebra.commutant_commutant`.

### Relevance to multi-block MPS

A standard multi-block uniqueness argument uses “Schur’s lemma”-style statements:

* intertwiners between inequivalent irreducible blocks vanish,
* the commutant of a full matrix block is just scalars.

Mathlib has the *definitions* (centralizers/commutants), but not many “matrix-algebra-specific” commutant computations.

### Gaps / friction points

* Missing “ready-to-use” lemmas computing commutants of standard embeddings such as:
  * `Matrix n n ℂ` acting on itself or on `ℂ^n`;
  * products `Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ`.
* There is no direct “finite-dimensional bicommutant theorem” in the style used in operator algebra proofs (though `VonNeumannAlgebra` bundles the double-commutant property by definition).

---

## Topic 5 — Completely positive maps / operator-algebra interface for transfer operators

### Present in Mathlib

Mathlib has begun building C⋆-algebraic positivity infrastructure:

* `Mathlib/Analysis/CStarAlgebra/CompletelyPositiveMap.lean`
  * defines `CompletelyPositiveMap` and `CompletelyPositiveMapClass`
  * scoped notation: `A₁ →CP A₂`
* `Mathlib/Analysis/CStarAlgebra/PositiveLinearMap.lean`
  * shows positive maps between C⋆-algebras are bounded/continuous

### Relevance to multi-block MPS

The transfer operator/channel

\[E_A(X) = \sum_i A_i X A_i^{\dagger}\]

is completely positive. Many canonical-form arguments are naturally phrased in CP-map language.

### Gaps / friction points

* No bundled notion of a **quantum channel** (e.g. CP + trace-preserving or CP + unital).
* No Kraus/Choi/Stinespring API in Mathlib (at least under this toolchain):
  * “Kraus representation exists” for CP maps on matrix algebras is not available.
* No Perron–Frobenius-style results for CP maps (“primitive channel ⇒ unique faithful fixed point”).

---

## Topic 6 — Perron–Frobenius theory (nonnegative matrices)

### Present in Mathlib

Mathlib currently has **graph-theoretic irreducibility/primitivity definitions** for nonnegative matrices:

* `Mathlib/LinearAlgebra/Matrix/Irreducible/Defs.lean`
  * `Matrix.IsIrreducible` (nonneg + strongly connected positive-entry quiver)
  * `Matrix.IsPrimitive` (some power strictly positive)
  * key equivalences:
    * `Matrix.pow_apply_pos_iff_nonempty_path`
    * `Matrix.isIrreducible_iff_exists_pow_pos`
    * `Matrix.IsPrimitive.isIrreducible`

### Gaps / friction points

* There is **no spectral Perron–Frobenius theorem** in Mathlib for matrices:
  * existence of an eigenvalue equal to spectral radius,
  * existence/uniqueness of positive eigenvectors,
  * spectral gap / peripheral spectrum for primitive matrices.

For multi-block MPS, these spectral statements are typically the backbone of:

* canonical form existence/uniqueness,
* asymptotics of transfer powers,
* “injective/primitive ⇒ unique fixed point” results.

---

## Topic 7 — Jordan / nilpotent decompositions and non-diagonalizable behavior

### Present in Mathlib

* `Mathlib/LinearAlgebra/JordanChevalley.lean`:
  * `Module.End.exists_isNilpotent_isSemisimple` (Jordan–Chevalley–Dunford decomposition over perfect fields).

There is also broad infrastructure for eigenvalues/triangularization scattered across `LinearAlgebra/…` (e.g. `LinearAlgebra/Eigenspace/Triangularizable.lean`).

### Gaps / friction points

* No “turnkey” **Jordan normal form** for matrices over algebraically closed fields.
* For transfer operators/channels, one often needs explicit control of generalized eigenspaces (e.g. peripheral spectrum); this is not yet packaged at the level commonly used in quantum information / MPS proofs.

---

## Topic 8 — Fixed points, ergodic limits, and projections onto invariants

### Present in Mathlib

* Fixed point subspace for a linear map is `LinearMap.eqLocus f 1`.
* `Mathlib/Analysis/InnerProductSpace/MeanErgodic.lean` proves the von Neumann mean ergodic theorem:
  * `ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection` (Cesàro averages converge to the orthogonal projection onto fixed points for contractions on Hilbert spaces).

### Gaps / friction points

* No “fixed point algebra of a unital CP map is a *-subalgebra” (Choi–Effros type results).
* No conditional expectations onto fixed points for CP/unital maps.

These results become relevant in multi-block settings where one studies asymptotics and projections onto peripheral eigenspaces.

---

## Topic 9 — How this repo currently uses Mathlib (and what multi-block will likely need)

### Present in this repo

* **Single-block Fundamental Theorem**: `MPSLean/MPS/FundamentalTheorem.lean`
  * uses linear extension + simplicity + a Skolem–Noether result (`MPSLean/MPS/SkolemNoether.lean`).
* **Canonical-form scaffolding**: `MPSLean/MPS/CanonicalForm.lean`
  * already models a multi-block tensor as dependent block diagonal (`Matrix.blockDiagonal'`) with reindexing via `finSigmaFinEquiv`.
* **Transfer operator**: `MPSLean/MPS/Transfer.lean`
  * defines `transferMap` as a `LinearMap` on matrices and proves positivity with `Matrix.PosSemidef`.

### Likely upcoming requirements for multi-block FT

1. **Blockwise reasoning about the transfer map** (show it decomposes across blocks for block-diagonal tensors).
2. **Centralizer/commutant computations** to show intertwiners between different blocks vanish / are scalar.
3. **Spectral/Perron–Frobenius results** (at least in finite dimension over `ℂ`) to pin down canonical blocks and their scaling factors.
4. **Permutation/block-reindexing lemmas** to express uniqueness “up to block permutation” cleanly.

---

## Topic 10 — Strategic recommendations (Mathlib PR roadmap + local workarounds)

### A. High-impact, low-effort Mathlib additions (“quick wins”)

1. **Determinant of dependent block diagonal**

   Provide a lemma (under the standard `Fintype`/`DecidableEq` hypotheses) of the form:

   ```lean
   theorem det_blockDiagonal' (M : ∀ k, Matrix (Fin (d k)) (Fin (d k)) R) :
     (Matrix.blockDiagonal' M).det = ∏ k, (M k).det
   ```

   This can likely be proved via `Matrix.blockTriangular_blockDiagonal'` + `Matrix.BlockTriangular.det_fintype`.

2. **Invertibility/unit lemmas for blockDiagonal'**

   Add equivalences like:

   * `IsUnit (blockDiagonal' M) ↔ ∀ k, IsUnit (M k)`
   * `Invertible (blockDiagonal' M)` given `∀ k, Invertible (M k)`
   * formula for inverse as another `blockDiagonal'`.

3. **Bundled `RingHom` for `blockDiag` / `blockDiag'` (square-block case)**

   These exist as `AddMonoidHom`s; making them `RingHom`s when appropriate would reduce boilerplate in algebraic proofs.

4. **`mulVec` / `vecMul` lemmas for `blockDiagonal'`**

   Analogues of `fromBlocks_mulVec` and `vecMul_fromBlocks` would help with transfer-operator computations.

### B. Medium-term Mathlib contributions

5. **Centralizer/commutant computations for matrix algebras**

   Add lemmas capturing “commutant of a full matrix algebra is scalars” in the relevant algebraic setting (`Subalgebra.centralizer`, `StarSubalgebra.centralizer`, etc.).

6. **Better API around reindexing/permutation matrices**

   Canonical-form uniqueness is naturally expressed as “equal up to permutation of blocks”; having a small API for block-permutation matrices would help.

### C. Long-term foundational work (bigger projects)

7. **Spectral Perron–Frobenius theorem in Mathlib**

   Build on `Matrix.IsIrreducible` / `Matrix.IsPrimitive` to prove classical PF spectral results for (finite) nonnegative matrices.

8. **Finite-dimensional quantum channel theory**

   On `Matrix n n ℂ`, develop at least:

   * Kraus representation,
   * unital/trace-preserving CP maps,
   * fixed-point algebra and primitive-channel fixed point uniqueness.

### Suggested local workarounds (if upstreaming is too slow)

* For determinant/invertibility: derive specialized lemmas in this repo using `BlockTriangular.det_fintype` and existing block APIs.
* For PF/spectral properties: initially restrict to finite-dimensional linear algebra over `ℂ` and prove the needed spectral results directly for the concrete transfer map `Matrix →ₗ Matrix`, avoiding C⋆-algebra abstractions.

---

## Web/GitHub scan — related Lean projects (tensor networks / quantum information)

Scan method: GitHub Search API queries (unauthenticated, rate-limited), run on 2026-02-08. This is not exhaustive.

### Repos found

**Quantum information / quantum computing (Lean):**

* `Timeroot/Lean-QuantumInfo` — https://github.com/Timeroot/Lean-QuantumInfo — “Quantum information theory in Lean 4” (~101★)
* `duckki/lean-quantum` — https://github.com/duckki/lean-quantum — “Formalized quantum computing in Lean theorem prover” (~34★)
* `Maokami/vqc_in_lean` — https://github.com/Maokami/vqc_in_lean — “Lean 4 port of the Verified Quantum Computing” (~6★)
* `tannerduve/zxLean` — https://github.com/tannerduve/zxLean — “zx calculus for quantum computing” (~2★)
* `bjoernkjoshanssen/kraus` — https://github.com/bjoernkjoshanssen/kraus — “Kraus operators in Lean” (0★ at scan time)
* `Stavan-Jain/QuantumErrorCorrectionLean` — https://github.com/Stavan-Jain/QuantumErrorCorrectionLean (few★)
* `jtriley2p/quantum-lean` — https://github.com/jtriley2p/quantum-lean (few★)
* `guest2180/lean4-quantum` — https://github.com/guest2180/lean4-quantum (few★)
* `BalandinIlia/quantum_computer_3_qubits` — https://github.com/BalandinIlia/quantum_computer_3_qubits (0★ at scan time)

**Tensor networks:**

* `KVerv/TensorNetworkForm` — https://github.com/KVerv/TensorNetworkForm (~2★)

**C⋆-algebra / operator algebra adjacent:**

* `ewittlich/Categories-CStarAlgebras` — https://github.com/ewittlich/Categories-CStarAlgebras (0★ at scan time)

### Notable negative result

* Query `matrix product state language:Lean` returned **0 results** at scan time.

---

*End of audit.*
