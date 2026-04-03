# Wedderburn Scouting Report for Wolf Thm 6.14 / Issue #360

## Executive summary

This is feasible, but not by a short direct application of existing Mathlib Wedderburn-Artin theorems.

The current state is:

- TNLean already has the Heisenberg-picture fixed-point `*`-algebra as a concrete `StarSubalgebra ℂ (Matrix (Fin D) (Fin D) ℂ)`.
- TNLean already identifies that algebra with a concrete Kraus commutant.
- Mathlib already has the abstract semisimple/simple algebra decomposition theorems:
  - `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`
  - `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`
- Mathlib also has the matrix block API, star-subalgebra API, tensor/matrix equivalences, and unitary conjugation API needed for the concrete matrix side.

The missing bridge is the hard part:

- there is no ready-made theorem turning a concrete finite-dimensional `*`-subalgebra of `M_D(ℂ)` into a unitary block-diagonal matrix algebra,
- and there is no ready-made theorem showing TNLean's fixed-point `StarSubalgebra` is semisimple in the precise sense needed by the abstract Wedderburn-Artin theorem.

So the theorem is viable, but the cleanest route is likely a staged development:

1. formalize the Heisenberg-picture algebra structure first,
2. prove a concrete block decomposition inside matrices,
3. only then derive the Schrödinger-picture formula with the `ρ_k`.

I would not expect the full theorem

`Fix(T) = U (0 ⊕ ⊕_k M_{d_k} ⊗ ρ_k) U†`

to be a small, near-term patch unless the proof is split into several preparatory lemmas or Mathlib-side infrastructure is added first.

## Scope clarification

The displayed formula with `ρ_k` is the Schrödinger-picture fixed-point space. It is not literally a `*`-subalgebra under ordinary matrix multiplication.

What TNLean currently formalizes as a `StarSubalgebra` is the Heisenberg-picture fixed-point set of `adjointMap K`, i.e. `Fix(T*)`. The algebraic statement to target first is therefore the Heisenberg version:

`Fix(T*) = U (⊕_k M_{d_k} ⊗ 1_{m_k}) U†`.

Once that is in place, the Schrödinger-picture formula with the `ρ_k` should be derived as a second step using a faithful stationary state and the existing gauge/unitalization machinery.

This distinction already shows up in TNLean:

- `TNLean/Channel/FixedPoint/Algebra.lean` works in the Heisenberg picture.
- `TNLean/Channel/FixedPoint/ConditionalExpectation.lean` explicitly says the general conditional expectation case needs the Wedderburn block decomposition from Wolf Thm 6.14.

## 1. TNLean infrastructure

### 1a. `TNLean/Channel/FixedPoint/Algebra.lean`

Note: the issue prompt says `TNLean/Channel/Semigroup/FixedPoint/Algebra.lean`, but the file in this worktree is actually:

- `TNLean/Channel/FixedPoint/Algebra.lean`

What already exists there:

- `fixedPointsStarSubalgebra` at line 175:
  fixed points of `map K` form a `StarSubalgebra` under unitality plus a positive-definite fixed point of the adjoint.
- `adjointFixedPointsStarSubalgebra` at line 237:
  Heisenberg-picture fixed points form a `StarSubalgebra`.
- `fixedPoints_starSubalgebra` at line 277:
  wrapper using the prompt's naming convention.
- `krausCommutantStarSubalgebra` at line 363:
  the commutant of `K_i` and `K_i†` is a concrete `StarSubalgebra`.
- `adjointFixedPointsStarSubalgebra_eq_krausCommutantStarSubalgebra` at line 476:
  the Heisenberg fixed-point algebra coincides with the Kraus commutant.

Assessment:

- This is the strongest existing starting point for Wolf 6.14.
- Step (1) from the prompt, "show `Fix(T)` is a finite-dimensional `*`-subalgebra", is essentially already done for `Fix(T*)`, and it is done concretely inside matrices.
- The commutant description is especially valuable because Wolf 6.14 is really a structure theorem for a concrete matrix `*`-subalgebra.

Related file:

- `TNLean/Channel/FixedPoint/ConditionalExpectation.lean` at lines 18 and 197-198 explicitly marks Wedderburn decomposition as the missing ingredient for the general conditional expectation theorem.

### 1b. `TNLean/Channel/Peripheral/CyclicDecomposition.lean`

This file does not contain a Wedderburn decomposition, but it does contain useful corner/block infrastructure:

- `PreservesCorner` at line 43
- `cornerSubmodule` at line 48
- `cornerRestriction` at line 66
- `IsIrreducibleOnCorner` at line 84
- `exists_cyclic_projections_of_peripheral_unitary` at line 519
- `preserves_corner_pow_of_cyclic_decomp` at line 1158
- `preserves_corner_pow_orderOf_of_perm_decomp` at line 1352

Assessment:

- This gives a good pattern for restricting channels to corners `P M_D P`.
- It does not yet provide the concrete "sum of simple blocks inside matrices" theorem needed for Wedderburn.
- Still, it is likely reusable when proving that central projections split the fixed-point algebra into corners.

### 1c. `TNLean/Channel/Semigroup/ReducibleQDS/`

Relevant declarations:

- `Defs.lean`
  - `IsNontrivialProjection` line 54
  - `HasInvariantCompression` line 90
  - `HasBlockUpperTriangularLindblad` line 100
  - `GeneratorPreservesCompression` line 112
- `GeneratorCompression.lean`
  - `generatorPreservesCompression_of_semigroupPreservesCompression` line 34
  - `hasBlockUpperTriangularLindblad_of_hasInvariantCompression` line 86
  - `generator_preserves_compression_of_blockUpperTriangular` line 167
  - `semigroup_preserves_compression_of_generator` line 262
- `Equivalence.lean`
  - `IsReducibleQDS` line 38
  - `wolf_prop_7_6_full_equivalence` line 98

Assessment:

- This is strong "one projection gives one block split" infrastructure.
- It is semigroup-focused and mostly upper-triangular/invariant-compression oriented, not yet `*`-algebra decomposition.
- Still, it provides reusable projection language and good proofs for turning invariant subspaces into concrete matrix decompositions.

### 1d. Extra TNLean infrastructure that is not in the prompt but is directly relevant

These files look very reusable for the matrix-realization step:

- `TNLean/Channel/FixedPoint/CanonicalGauge.lean`
  - `gauged_unital` line 29
  - `gauged_tracePreserving` line 78

This is important because Wolf 6.14 as stated for `Fix(T)` should probably be derived from the unital/Heisenberg case by conjugating with a square root of a faithful stationary state.

- `TNLean/MPS/Structure/InvariantSubspaceDecomp.lean`
  - `sameMPV_conj_unitary` line 164
  - `exists_twoBlock_decomp_of_lowerZero` line 235
  - `orthProj_spectral_eq'` line 595
  - `exists_twoBlock_decomp_of_lowerZero_strict` line 614

This file already shows a concrete pattern:

- diagonalize an orthogonal projection with `eigenvectorUnitary`,
- split indices by `Equiv.sumCompl`,
- reindex the matrix space into a block sum,
- obtain an explicit block decomposition.

That is extremely close in spirit to the matrix part of Wedderburn.

## 2. Mathlib infrastructure

### 2a. Abstract Wedderburn-Artin

Pinned Mathlib source located from a local checkout at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`, matching this repo's `lake-manifest.json`.

Main declarations:

- `Mathlib/RingTheory/SimpleModule/IsAlgClosed.lean`
  - `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed` line 22
  - `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` line 33

Also relevant:

- `Mathlib/RingTheory/SimpleModule/WedderburnArtin.lean`
  - `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite` line 183
  - `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing` line 193
  - `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite` line 202

Assessment:

- The abstract algebra theorem is present.
- It gives an `AlgEquiv`, not a `StarAlgEquiv`.
- It says nothing by itself about how the algebra sits inside `M_D(ℂ)`.

### 2b. `StarSubalgebra`

Main file:

- `Mathlib/Algebra/Star/Subalgebra.lean`

Useful declarations:

- `StarSubalgebra.subtype` line 173
- `StarSubalgebra.map` line 216
- `StarSubalgebra.comap` line 251
- `StarSubalgebra.centralizer` line 297
- `StarSubalgebra.mem_centralizer_iff` line 306
- `StarSubalgebra.range` line 788
- `StarSubalgebra.rangeRestrict` line 821

Assessment:

- The general `StarSubalgebra` API is solid.
- There is commutant/centralizer infrastructure.
- I did not locate a theorem in pinned Mathlib giving a decomposition of a `StarSubalgebra` of matrices into blocks or tensor factors.

### 2c. Finite-dimensionality of subalgebras

- `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`
  - `Subalgebra.finiteDimensional_toSubmodule` line 586
  - `FiniteDimensional.finiteDimensional_subalgebra` line 593

Assessment:

- Once TNLean has a `Subalgebra` or `StarSubalgebra` inside `M_D(ℂ)`, finite-dimensionality is easy.
- This part is not a blocker.

### 2d. Matrix block-diagonal API

- `Mathlib/Data/Matrix/Block.lean`
  - `Matrix.fromBlocks` line 46
  - `Matrix.toBlocks₁₁` line 72
  - `Matrix.fromBlocks_toBlocks` line 90
  - `Matrix.blockDiagonal` line 329
  - `Matrix.blockDiag` line 463
  - `Matrix.blockDiagonal'` line 570
  - `Matrix.blockDiagonal'_eq_blockDiagonal` line 581
  - `Matrix.blockDiag'` line 721

Assessment:

- The concrete block-diagonal matrix layer exists.
- This should be enough to represent `⊕_k` blocks once the index decomposition is available.
- What is missing is the theorem packaging the direct product algebra `Π_k M_{d_k}` as a concrete star-subalgebra of one large matrix algebra in the exact form needed downstream.

### 2e. Tensor-product / matrix-algebra equivalences

- `Mathlib/RingTheory/MatrixAlgebra.lean`
  - `matrixEquivTensor` line 212
  - `Matrix.kroneckerTMulStarAlgEquiv` line 266
  - `Matrix.kroneckerTMulStarAlgEquiv_apply` line 277
  - `Matrix.kroneckerStarAlgEquiv` line 305
  - `Matrix.kroneckerStarAlgEquiv_apply` line 315

Assessment:

- This is the right API for the `M_{d_k} ⊗ M_{m_k}` side.
- It makes the tensor-factor presentation realistic.
- But it does not by itself isolate subalgebras of the form `M_{d_k} ⊗ 1` or `M_{d_k} ⊗ ρ_k`.

### 2f. Unitary conjugation and spectral tools

- `Mathlib/LinearAlgebra/UnitaryGroup.lean`
  - `Matrix.unitaryGroup` line 60
  - `Matrix.mem_unitaryGroup_iff'` line 76
  - `Matrix.UnitaryGroup.star_mul_self` line 130
  - `Matrix.UnitaryGroup.toLinearEquiv` line 170

- `Mathlib/Algebra/Star/UnitaryStarAlgAut.lean`
  - `Unitary.conjStarAlgAut` line 32
  - `Unitary.conjStarAlgAut_apply` line 42
  - `Unitary.toAlgEquiv_conjStarAlgAut` line 67

- `Mathlib/Analysis/Matrix/Spectrum.lean`
  - `eigenvectorUnitary` line 87
  - `conjStarAlgAut_star_eigenvectorUnitary` line 125
  - `spectral_theorem` line 144

Assessment:

- This is enough for "choose a unitary basis and conjugate the algebra".
- TNLean already uses exactly this pattern in `MPS/Structure/InvariantSubspaceDecomp.lean`.

### 2g. What I did not find in Mathlib

I did not find a pinned Mathlib theorem of the following form:

- a structure theorem for finite-dimensional complex `StarSubalgebra`s of matrices,
- a theorem upgrading an abstract Wedderburn `AlgEquiv` to a `StarAlgEquiv` for a concrete matrix `*`-subalgebra,
- a theorem saying a finite-dimensional complex `*`-subalgebra of `M_D(ℂ)` is unitarily conjugate to block-diagonal matrix factors,
- a packaged equivalence between `Π_k Matrix (Fin d_k) (Fin d_k) ℂ` and a block-diagonal `StarSubalgebra` inside one matrix algebra.

## 3. The actual gap

The prompt's step list is almost right, but the key obstruction is stronger than it first looks.

### Gap A. Step 1 is basically done, but for `Fix(T*)`

This is already available in TNLean:

- `Fix(T*)` is a concrete `StarSubalgebra` inside matrices.
- it is identified with a commutant.

So the algebraic object exists.

### Gap B. Step 2 is nontrivial: semisimplicity is not automatic

This is the main abstract blocker.

The tempting route

- finite-dimensional algebra
- therefore Artinian
- therefore semisimple

does not work.

Reason:

- finite-dimensional implies Artinian,
- but Artinian does not imply semisimple,
- and being a subalgebra of a semisimple ring does not imply semisimple either.

Also, proving `IsReduced` would not solve it:

- `M_n(ℂ)` itself is semisimple but not reduced,
- so reducedness is the wrong criterion here.

What is really needed is a genuinely C*-algebraic or `*`-algebraic argument:

- finite-dimensional complex `*`-subalgebras of matrix algebras are semisimple,
- and their structure is controlled by orthogonal projections and unitary conjugation.

Pinned Mathlib does not appear to already package that theorem.

### Gap C. Step 3 only gives an abstract algebra isomorphism

Even after semisimplicity, Mathlib gives only

`S ≃ₐ[ℂ] Π_k M_{d_k}(ℂ)`.

That is still not Wolf 6.14.

Missing from there:

- preservation of `star`,
- realization inside the ambient matrix algebra,
- unitary conjugation,
- identification of multiplicity spaces and tensor factors.

### Gap D. Step 4 is the real matrix-classification theorem

To reach Wolf's form, one needs a theorem of the shape:

- if `S ⊆ M_D(ℂ)` is a finite-dimensional `*`-subalgebra,
- then there is a unitary `U` and a decomposition
  `ℂ^D = ⊕_k (ℂ^{d_k} ⊗ ℂ^{m_k})`
- such that
  `U† S U = ⊕_k (M_{d_k}(ℂ) ⊗ 1_{m_k})`.

This is not provided by the abstract Wedderburn theorem alone.

### Gap E. The formula with `ρ_k` is a second theorem, not the first theorem

Wolf 6.14 as stated for `Fix(T)` should be derived after the Heisenberg algebra structure is known.

The expected flow is:

1. classify `Fix(T*)` as a concrete `*`-algebra:
   `Fix(T*) = U (⊕_k M_{d_k} ⊗ 1_{m_k}) U†`
2. use a faithful stationary state to identify `Fix(T)`:
   `Fix(T) = U (0 ⊕ ⊕_k M_{d_k} ⊗ ρ_k) U†`

TNLean already has the unitalization/gauge ingredients that point toward this route:

- `TNLean/Channel/FixedPoint/CanonicalGauge.lean`
- `TNLean/Channel/Semigroup/Primitivity/Helpers.lean`

## 4. Recommended formalization plan

### Plan A. Recommended route: concrete matrix decomposition first

This looks more realistic than trying to force the abstract Wedderburn theorem all the way through.

#### Stage 1. Formalize the Heisenberg fixed-point algebra cleanly

Goal:

- use `adjointFixedPointsStarSubalgebra_eq_krausCommutantStarSubalgebra`,
- work entirely with the concrete `StarSubalgebra` / commutant in `M_D(ℂ)`.

Status:

- mostly already done.

Difficulty:

- low.

#### Stage 2. Prove one nontrivial central projection gives a two-block decomposition

Goal:

- if the fixed-point algebra contains a nontrivial central orthogonal projection `P`,
  then after unitary conjugation every element becomes block diagonal.

Likely ingredients:

- `eigenvectorUnitary` / spectral theorem
- `Unitary.conjStarAlgAut`
- `Matrix.fromBlocks`, `toBlocks`, `blockDiagonal'`
- the proof pattern in `TNLean/MPS/Structure/InvariantSubspaceDecomp.lean`

Status:

- most of the linear algebra infrastructure is already present.

Difficulty:

- medium.

#### Stage 3. Recursively split by central projections

Goal:

- show the fixed-point algebra is a finite direct sum of simple matrix blocks.

Likely proof style:

- induct on ambient dimension or on algebra dimension,
- use finite-dimensionality to obtain strict descent,
- each nontrivial center gives a central projection,
- split into two corners and recurse.

Missing lemma family:

- existence of nontrivial central projections when the center is nontrivial,
- compatibility of the corner algebra with the fixed-point algebra / commutant description.

Difficulty:

- medium-high.

#### Stage 4. Handle the simple case

This is the hardest local step.

Target:

- if a concrete `*`-subalgebra of `M_D(ℂ)` is simple, then it is unitarily conjugate to
  `M_d(ℂ) ⊗ 1_m`.

Possible approaches:

- abstract Wedderburn-Artin plus a separate matrix-realization theorem,
- Burnside/double-commutant style argument,
- representation-theoretic decomposition of the `S`-module `ℂ^D`.

TNLean hint:

- there is already matrix/commutant and invariant-subspace infrastructure,
- but I did not find a ready-made theorem in the repo that closes this step.

Difficulty:

- high.

#### Stage 5. Package the Heisenberg theorem

Target statement:

- `Fix(T*) = U (⊕_k M_{d_k} ⊗ 1_{m_k}) U†`

Once Stage 4 exists, this packaging step should be straightforward.

Difficulty:

- low-medium.

#### Stage 6. Derive the Schrödinger-picture fixed-point formula with `ρ_k`

Target:

- `Fix(T) = U (0 ⊕ ⊕_k M_{d_k} ⊗ ρ_k) U†`

Likely ingredients:

- faithful stationary state,
- `CanonicalGauge.gauged_unital`,
- the existing conditional expectation story in `FixedPoint/ConditionalExpectation.lean`,
- possibly Wolf's Proposition 1.5 style form of positive projections onto `*`-algebras.

Difficulty:

- medium after the Heisenberg theorem,
- very high if attempted first.

### Plan B. Abstract Wedderburn-Artin first

This route is theoretically elegant but practically blocked by missing bridges.

Needed steps:

1. show the fixed-point algebra is semisimple,
2. apply `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`,
3. upgrade `AlgEquiv` to the correct `StarAlgEquiv`,
4. realize the abstract algebra as a concrete unitary block decomposition in matrices.

This route likely needs new Mathlib theorems, not just TNLean code.

## 5. Near-term feasibility assessment

### What is feasible in the near term

Feasible in-repo, without upstream work:

- a preparatory development for the Heisenberg-picture fixed-point algebra,
- projection-based splitting lemmas,
- explicit block-diagonalization lemmas using unitaries and `Equiv.sumCompl`,
- a theorem reducing Wolf 6.14 to a finite-dimensional matrix `*`-subalgebra structure theorem.

Possibly feasible in-repo but substantial:

- a custom proof of the concrete finite-dimensional matrix `*`-subalgebra structure theorem,
- then the Heisenberg fixed-point classification,
- then the Schrödinger `ρ_k` form.

### What likely needs upstream work for a clean route

At least one of the following would make the formalization much cleaner:

- a Mathlib theorem that finite-dimensional complex `*`-subalgebras of matrix algebras are
  unitarily conjugate to block-diagonal matrix algebras,
- a star-preserving version of the Wedderburn-Artin theorem for matrix `*`-subalgebras,
- a packaged star-algebra equivalence between direct products / tensor factors and concrete
  block-diagonal subalgebras of a matrix algebra.

### Bottom line

- Near-term full formalization of Wolf 6.14 exactly as stated: possible, but high effort.
- Near-term minimal milestone that seems realistic: formalize the Heisenberg fixed-point algebra
  decomposition first.
- If the goal is a clean short proof via existing theorems, upstream Mathlib work is probably needed.

## 6. Concrete recommendation for Issue #360

I would split the work into the following subgoals:

1. Formalize the Heisenberg target theorem first:
   `Fix(T*) = U (⊕_k M_{d_k} ⊗ 1_{m_k}) U†`.
2. Reuse the `InvariantSubspaceDecomp` projection-diagonalization template to build the concrete
   block machinery.
3. Delay the `ρ_k` Schrödinger-picture statement until after the Heisenberg theorem is available.
4. If the simple-block classification step becomes too painful locally, upstream the missing
   matrix `*`-subalgebra classification lemma to Mathlib.

## 7. Loogle note

I attempted to use Loogle, but exact Loogle retrieval was not reliable from this environment.
All declaration names above were therefore verified directly against the pinned local Mathlib source
at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
