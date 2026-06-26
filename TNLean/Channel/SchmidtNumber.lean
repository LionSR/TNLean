/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import TNLean.Channel.NPositivityChainStrict
import TNLean.Channel.ReductionCriterion
import TNLean.Channel.Separable
import TNLean.Channel.Schwarz.ChoiCompression

/-!
# The Schmidt number and the full reduction criterion

Wolf's Chapter 3, Section 3.2 (the paragraph *Detecting entanglement*) defines the
**Schmidt number** of a bipartite state ρ as the smallest `n` such that ρ has a
convex decomposition into pure states each of Schmidt rank at most `n`; separable
states are exactly those of Schmidt number one.  Using the maps
`T_n(X) = tr(X) • 1 − n⁻¹ • X`, which are `n`-positive, Wolf concludes the
**reduction criterion** (eq. (3.18)): a state of Schmidt number at most `n`
satisfies `n • (ρ₁ ⊗ 1) ≥ ρ` and `n • (1 ⊗ ρ₂) ≥ ρ`, with `ρ₁` and `ρ₂` the two
reduced density matrices.

This file introduces the Schmidt-number predicate for mixed states and completes
Wolf's two-step derivation of eq. (3.18), supplying the first step that the
operator-implication lemmas of `ReductionCriterion.lean` previously assumed.

## The Schmidt-number predicate

A bound on the Schmidt number is recorded by `Matrix.HasSchmidtNumberLE n ρ`:
the state ρ is a finite sum of pure-state projectors `|ψᵢ⟩⟨ψᵢ|`, each of Schmidt
rank at most `n`.  Up to normalization this is Wolf's "ρ has a convex
decomposition into pure states of Schmidt rank at most `n`": a positive coefficient
is absorbed into the vector by rescaling, which scales the Schmidt coefficient
matrix and so preserves the Schmidt rank.

At `n = 1` every pure summand `|ψᵢ⟩⟨ψᵢ|` has Schmidt rank at most one, hence ψᵢ is a
product vector and `|ψᵢ⟩⟨ψᵢ|` is a product of two positive semidefinite rank-one
matrices.  Thus Schmidt number one coincides with separability.

## The forward reduction step

The technical core is the **pure-state step**: for a pure state `|ψ⟩⟨ψ|` with ψ of
Schmidt rank at most `n`, the ampliation `(T_n ⊗ id)(|ψ⟩⟨ψ|)` is positive
semidefinite.  Writing ψ through the maximally entangled vector as
`ψ = (1 ⊗ X)|Ω⟩√D` with X of rank equal to the Schmidt rank of ψ, the ampliation
becomes the right-factor Choi compression of `T_n` by X, whose quadratic form is the
Choi quadratic form of `T_n` evaluated on a vector of Schmidt rank at most the rank
of X, hence at most `n`.  The `n`-positivity of `T_n` makes that Choi quadratic form
nonnegative, so the compression is positive semidefinite.  Summing over the pure
terms gives `(T_n ⊗ id)(ρ) ≥ 0` for any state of Schmidt number at most `n`.
Composing with the operator-implication lemmas of `ReductionCriterion.lean` yields
Wolf eq. (3.18) with its Schmidt-number premise.

## Main definitions

* `Matrix.HasSchmidtNumberLE`: a bipartite matrix is a finite sum of pure-state
  projectors of Schmidt rank at most `n`.

## Main results

* `Matrix.HasSchmidtNumberLE.posSemidef`: a state of bounded Schmidt number is
  positive semidefinite.
* `Matrix.HasSchmidtNumberLE.add`, `Matrix.HasSchmidtNumberLE.mono`: closure under
  addition and monotonicity in the bound.
* `Matrix.hasSchmidtNumberLE_one_iff_isSeparable`: **Schmidt number one is exactly
  separability** (Wolf §3.2).
* `Matrix.tensorMapId_posSemidef_of_hasSchmidtRankLE`: the **pure-state step of Wolf
  Prop 3.4 (only if)** — for ψ of Schmidt rank at most `n` and any `n`-positive map
  `T`, `(T ⊗ id)(|ψ⟩⟨ψ|) ≥ 0`.
* `Matrix.HasSchmidtNumberLE.tensorMapId_posSemidef`: **Wolf Prop 3.4 (only if)** — a
  state of Schmidt number at most `n` has `(T ⊗ id)(ρ) ≥ 0` for every `n`-positive
  map `T`.
* `Matrix.tensorMapId_posSemidef_of_hasSchmidtRankLE'` and
  `Matrix.HasSchmidtNumberLE.tensorMapId_posSemidef'`: the **differing-factors**
  forms of the only-if direction for second factor `d' ≤ d`, obtained from the square
  forms by padding the second factor up to `d` with zeros and restricting back to the
  `d × d'` corner.
* `Matrix.tensorMapId_posSemidef_of_hasSchmidtRankLE''` and
  `Matrix.HasSchmidtNumberLE.tensorMapId_posSemidef''`: the complementary
  differing-factors forms for second factor `d ≤ d'`, obtained by padding the first
  factor up to `d'` with zeros, extending `T` to the larger square by the corner
  sandwich `cornerExtendMap` (which preserves `n`-positivity,
  `Matrix.isNPositiveMap_cornerExtendMap`), and restricting back to the `d × d'`
  corner.
* `Matrix.tensorMapId_posSemidef_of_hasSchmidtRankLE_general` and
  `Matrix.HasSchmidtNumberLE.tensorMapId_posSemidef_general`: the **general bipartite
  forward step** of Wolf Prop 3.4 (only if), with no relation imposed between the two
  tensor factors, combining the two padding directions.
* `Matrix.tensorMapId_tEta_posSemidef_of_hasSchmidtRankLE`: the **pure-state step** at
  `T = T_n` — for ψ of Schmidt rank at most `n` (with `1 ≤ n < D`),
  `(T_n ⊗ id)(|ψ⟩⟨ψ|) ≥ 0`.
* `Matrix.HasSchmidtNumberLE.tensorMapId_tEta_posSemidef`: **step 1 of Wolf
  eq. (3.18)** — a state of Schmidt number at most `n` has `(T_n ⊗ id)(ρ) ≥ 0`.
* `Matrix.reductionCriterion_left_of_hasSchmidtNumberLE` and
  `Matrix.reductionCriterion_right_of_hasSchmidtNumberLE`: **the full Wolf reduction
  criterion (eq. (3.18))** with its Schmidt-number premise: a state of Schmidt
  number at most `n` satisfies `n • (1 ⊗ ρ₂) ≥ ρ` and `n • (ρ₁ ⊗ 1) ≥ ρ`.

## Scope

**Scope restriction (1 ≤ n < D):** the forward reduction step uses the
`n`-positivity threshold of `T_η` (Wolf eq. (3.11)), which is formalized for
`1 ≤ n < D` where `D` is the first-factor dimension; the omitted top index `n = D`
(complete positivity) is inherited through the maximal-overlap principle and is
documented in `docs/paper-gaps/wolf_t_eta_top_index_scope.tex`.

**Scope restriction (square system d = d' = D):** the `T_n`-specialized forward step
and the full reduction criterion fix both tensor factors to a common dimension `D`,
because the pure state is parametrized through the square maximally entangled vector;
Wolf states eq. (3.18) for a general bipartite system `ℂ^d ⊗ ℂ^{d'}`, and the
non-square case is documented in
`docs/paper-gaps/wolf_reduction_criterion_schmidt_premise.tex`.  The Schmidt-number
predicate itself and its equivalence with separability carry no such restriction.
The bare positive-semidefiniteness of the ampliation `(T ⊗ id)(ρ) ≥ 0` carries no
restriction relating the two factors: the general forms
`tensorMapId_posSemidef_of_hasSchmidtRankLE_general` and
`HasSchmidtNumberLE.tensorMapId_posSemidef_general` hold for any second factor `d'`,
padding the second factor when `d' ≤ d` and padding the first factor while extending
`T` when `d ≤ d'`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Section 3.2, the *Detecting entanglement* paragraph and Example 3.1,
  equation (3.18)][Wolf2012QChannels]
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace Matrix

variable {d d' D : ℕ}

/-! ## The Schmidt-number predicate -/

/-- **Bounded Schmidt number** (Wolf §3.2).  A bipartite matrix ρ on
`Fin d × Fin d'` has Schmidt number at most `n` when it is a finite sum of
pure-state projectors of Schmidt rank at most `n`,

  ρ = Σ_i |ψ_i⟩⟨ψ_i|,   Schmidt rank of ψ_i ≤ n.

Up to normalization this is Wolf's "ρ has a convex decomposition into pure states of
Schmidt rank at most `n`": a positive coefficient `p_i` is absorbed by rescaling
`ψ_i ↦ √p_i ψ_i`, which scales the Schmidt coefficient matrix and so leaves the
Schmidt rank unchanged.  The smallest such `n` is the Schmidt number; at `n = 1`
this is separability. -/
def HasSchmidtNumberLE (n : ℕ) (ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (ψ : ι → (Fin d × Fin d' → ℂ)),
    (∀ i, HasSchmidtRankLE n (ψ i)) ∧ ρ = ∑ i, vecMulVec (ψ i) (star (ψ i))

/-! ## Basic properties -/

/-- A pure-state projector of Schmidt rank at most `n` has Schmidt number at most
`n`: it is the one-term sum with a single index. -/
theorem hasSchmidtNumberLE_vecMulVec {n : ℕ} {ψ : Fin d × Fin d' → ℂ}
    (hψ : HasSchmidtRankLE n ψ) : HasSchmidtNumberLE n (vecMulVec ψ (star ψ)) := by
  refine ⟨PUnit, inferInstance, fun _ => ψ, fun _ => hψ, ?_⟩
  simp

/-- **A state of bounded Schmidt number is positive semidefinite.**  Each summand
`|ψ_i⟩⟨ψ_i|` is a rank-one positive semidefinite matrix, and a finite sum of
positive semidefinite matrices is positive semidefinite. -/
theorem HasSchmidtNumberLE.posSemidef {n : ℕ}
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ} (hρ : HasSchmidtNumberLE n ρ) :
    ρ.PosSemidef := by
  obtain ⟨ι, _, ψ, _, rfl⟩ := hρ
  exact posSemidef_sum Finset.univ fun i _ => posSemidef_vecMulVec_self_star (ψ i)

/-- **States of bounded Schmidt number are closed under addition.** Concatenating
the two pure-state families realizes the sum as a single sum of pure-state
projectors of Schmidt rank at most `n`. -/
theorem HasSchmidtNumberLE.add {n : ℕ} {ρ σ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hρ : HasSchmidtNumberLE n ρ) (hσ : HasSchmidtNumberLE n σ) :
    HasSchmidtNumberLE n (ρ + σ) := by
  obtain ⟨ι, _, ψ, hψ, rfl⟩ := hρ
  obtain ⟨κ, _, φ, hφ, rfl⟩ := hσ
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim ψ φ, ?_, ?_⟩
  · rintro (i | j)
    · exact hψ i
    · exact hφ j
  · rw [Fintype.sum_sum_type]
    simp [Sum.elim_inl, Sum.elim_inr]

/-- **A bound on the Schmidt number relaxes to any larger bound.** Each pure summand
of Schmidt rank at most `n` also has Schmidt rank at most `m` when `n ≤ m`. -/
theorem HasSchmidtNumberLE.mono {n m : ℕ}
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ} (hρ : HasSchmidtNumberLE n ρ)
    (hnm : n ≤ m) : HasSchmidtNumberLE m ρ := by
  obtain ⟨ι, _, ψ, hψ, rfl⟩ := hρ
  exact ⟨ι, inferInstance, ψ, fun i => (hψ i).mono hnm, rfl⟩

/-! ## Schmidt number one is separability -/

/-- A pure state of Schmidt rank at most one is a product state, so its projector
`|ψ⟩⟨ψ|` is a Kronecker product of two positive semidefinite rank-one matrices and
hence separable. -/
theorem isSeparable_vecMulVec_of_hasSchmidtRankLE_one {ψ : Fin d × Fin d' → ℂ}
    (hψ : HasSchmidtRankLE 1 ψ) : IsSeparable (vecMulVec ψ (star ψ)) := by
  classical
  -- A Schmidt rank ≤ 1 coefficient matrix factors as a product `u vᵀ`.
  have hrank : (schmidtCoeffMatrix ψ).rank ≤ 1 := hψ
  obtain ⟨B, C, hBC⟩ := exists_mul_eq_of_rank_le (schmidtCoeffMatrix ψ) hrank
  -- The factorization yields ψ (i, j) = u i * v j with u = B(·,0), v = C(0,·).
  set u : Fin d → ℂ := fun i => B i 0 with hu
  set v : Fin d' → ℂ := fun j => C 0 j with hv
  have hψuv : ∀ i j, ψ (i, j) = u i * v j := by
    intro i j
    have hentry : schmidtCoeffMatrix ψ i j = (B * C) i j := by rw [hBC]
    rw [schmidtCoeffMatrix_apply] at hentry
    rw [hentry, Matrix.mul_apply, Fin.sum_univ_one, hu, hv]
  -- |ψ⟩⟨ψ| = (|u⟩⟨u|) ⊗ (|v⟩⟨v|), a Kronecker product of PSD matrices.
  have hkron : vecMulVec ψ (star ψ)
      = vecMulVec u (star u) ⊗ₖ vecMulVec v (star v) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [vecMulVec_apply, kroneckerMap_apply, Pi.star_apply, hψuv]
    rw [star_mul']
    ring
  rw [hkron]
  exact isSeparable_kronecker (posSemidef_vecMulVec_self_star u) (posSemidef_vecMulVec_self_star v)

/-- **Schmidt number one implies separability** (Wolf §3.2).  A state of Schmidt
number at most one is a finite sum of pure-state projectors of Schmidt rank at most
one; each is a product state, hence separable, and separable matrices are closed
under addition. -/
theorem HasSchmidtNumberLE.isSeparable
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ} (hρ : HasSchmidtNumberLE 1 ρ) :
    IsSeparable ρ := by
  obtain ⟨ι, _, ψ, hψ, rfl⟩ := hρ
  exact isSeparable_sum Finset.univ fun i _ =>
    isSeparable_vecMulVec_of_hasSchmidtRankLE_one (hψ i)

/-- A finite sum of states of Schmidt number at most `n` itself has Schmidt number
at most `n`. -/
theorem hasSchmidtNumberLE_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hf : ∀ i ∈ s, HasSchmidtNumberLE n (f i)) :
    HasSchmidtNumberLE n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact ⟨PEmpty, inferInstance, fun i => i.elim, fun i => i.elim, by simp⟩
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- A Kronecker product of two positive semidefinite matrices has Schmidt number at
most one.  Each factor is a finite sum of rank-one projectors, the Kronecker product
distributes into a double sum of product-vector projectors, and a product vector has
Schmidt rank at most one. -/
theorem hasSchmidtNumberLE_one_kronecker {A : Matrix (Fin d) (Fin d) ℂ}
    {B : Matrix (Fin d') (Fin d') ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    HasSchmidtNumberLE 1 (A ⊗ₖ B) := by
  classical
  obtain ⟨p, a, rfl⟩ := posSemidef_iff_eq_sum_vecMulVec.mp hA
  obtain ⟨q, b, rfl⟩ := posSemidef_iff_eq_sum_vecMulVec.mp hB
  rw [sum_kronecker_sum]
  refine hasSchmidtNumberLE_sum Finset.univ fun i _ => ?_
  refine hasSchmidtNumberLE_sum Finset.univ fun j _ => ?_
  rw [vecMulVec_kronecker_vecMulVec]
  exact hasSchmidtNumberLE_vecMulVec (hasSchmidtRankLE_one_product (a i) (b j))

/-- **Separability implies Schmidt number one** (Wolf §3.2).  A separable state is a
finite sum of Kronecker products of positive semidefinite matrices, each of which
has Schmidt number at most one, and that bound is closed under addition. -/
theorem IsSeparable.hasSchmidtNumberLE_one
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ} (hρ : IsSeparable ρ) :
    HasSchmidtNumberLE 1 ρ := by
  obtain ⟨ι, _, A, B, hAB, rfl⟩ := hρ
  exact hasSchmidtNumberLE_sum Finset.univ fun i _ =>
    hasSchmidtNumberLE_one_kronecker (hAB i).1 (hAB i).2

/-- **Schmidt number one is exactly separability** (Wolf §3.2).  The two
formulations of the lowest level of the Schmidt-number filtration coincide: a
bipartite state is a sum of product-vector projectors if and only if it is a sum of
Kronecker products of positive semidefinite matrices. -/
theorem hasSchmidtNumberLE_one_iff_isSeparable
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ} :
    HasSchmidtNumberLE 1 ρ ↔ IsSeparable ρ :=
  ⟨HasSchmidtNumberLE.isSeparable, IsSeparable.hasSchmidtNumberLE_one⟩

/-! ## The forward reduction step -/

/-- The full `id`-ampliation `tensorMapId T` on `M_D ⊗ M_D` coincides with the
`D`-fold blockwise ampliation `nPositiveAmpliation D T`: both apply `T` to the
`(i₂, j₂)` block and read off the `(i₁, j₁)` entry. -/
theorem tensorMapId_eq_nPositiveAmpliation
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ) :
    tensorMapId T X = nPositiveAmpliation D T X := by
  -- Both sides unfold to `T` applied entrywise to the second tensor block while the
  -- first block index is carried through, so the two ampliations are definitionally
  -- the same matrix and the equality holds by `rfl`.
  rfl

/-- A sharper Schmidt-rank bound for the pull-back through the adjoint right tensor
factor: the pulled-back vector has Schmidt rank at most the rank of the right-factor
matrix `X` (not merely at most the number of its columns). -/
theorem rightTensorMatrix_conjTranspose_mulVec_hasSchmidtRankLE_rank {k : ℕ}
    (X : Matrix (Fin D) (Fin k) ℂ) (η : Fin D × Fin k → ℂ) :
    HasSchmidtRankLE X.rank
      ((ChoiJamiolkowski.rightTensorMatrix X)ᴴ *ᵥ η) := by
  have hrank :
      (schmidtCoeffMatrix ((ChoiJamiolkowski.rightTensorMatrix X)ᴴ *ᵥ η)).rank
        ≤ X.rank := by
    rw [ChoiJamiolkowski.schmidtCoeffMatrix_rightTensorMatrix_conjTranspose_mulVec]
    calc
      (schmidtCoeffMatrix η * Xᴴ).rank ≤ (Xᴴ).rank :=
        Matrix.rank_mul_le_right (schmidtCoeffMatrix η) Xᴴ
      _ = X.rank := Matrix.rank_conjTranspose X
  simpa [HasSchmidtRankLE, schmidtRank] using hrank

/-- **Positive maps and entanglement, only-if direction, pure-state step**
(Wolf §3.2, Prop 3.4).  For a pure state `|ψ⟩⟨ψ|` with ψ of Schmidt rank at most `n`
and any `n`-positive map `T`, the ampliation `(T ⊗ id)(|ψ⟩⟨ψ|)` is positive
semidefinite.

Writing ψ through the maximally entangled vector as a square right-factor matrix `X`
of rank equal to the Schmidt rank of ψ, the ampliation is the right-factor Choi
compression of `T` by `X`.  Its quadratic form on any vector is the Choi quadratic
form of `T` on a vector of Schmidt rank at most the rank of `X`, hence at most `n`;
the `n`-positivity of `T` makes that form nonnegative.

**Scope restriction (square system d = d' = D):** both tensor factors are fixed to a
common dimension `D`, because the pure state is parametrized through the square
maximally entangled vector (`ChoiJamiolkowski.exists_squareCompression_of_vector`).
Wolf states the criterion for a general bipartite system `ℂ^d ⊗ ℂ^{d'}`; the
non-square case is documented in
`docs/paper-gaps/wolf_reduction_criterion_schmidt_premise.tex`. -/
theorem tensorMapId_posSemidef_of_hasSchmidtRankLE [NeZero D] {n : ℕ}
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hTpos : IsNPositiveMap n T) {ψ : Fin D × Fin D → ℂ} (hψ : HasSchmidtRankLE n ψ) :
    (tensorMapId T (vecMulVec ψ (star ψ))).PosSemidef := by
  classical
  -- Express ψ as a square compression of the maximally entangled vector.
  obtain ⟨X, hXvec, hXrank⟩ :=
    ChoiJamiolkowski.exists_squareCompression_of_vector (D := D) ψ
  have hXrank_le : X.rank ≤ n := by rw [hXrank]; exact hψ
  -- The ampliation of the pure state is the right-factor Choi compression.
  have hcomp :
      tensorMapId T (vecMulVec ψ (star ψ)) = ChoiJamiolkowski.rightCompression T X := by
    rw [tensorMapId_eq_nPositiveAmpliation, ← hXvec,
      ChoiJamiolkowski.nPositiveAmpliation_rankOne_eq_rightCompression]
  rw [hcomp]
  -- Positivity via the Choi quadratic form on Schmidt-rank-≤n vectors.
  refine posSemidef_of_dotProduct_mulVec_nonneg_complex ?_
  intro η
  rw [ChoiJamiolkowski.rightCompression_quadraticForm_eq_choiMatrix_quadraticForm]
  have hrank :
      HasSchmidtRankLE n ((ChoiJamiolkowski.rightTensorMatrix X)ᴴ *ᵥ η) :=
    (rightTensorMatrix_conjTranspose_mulVec_hasSchmidtRankLE_rank X η).mono hXrank_le
  exact
    ChoiJamiolkowski.isNPositiveMap_iff_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg.mp
      hTpos _ hrank

/-- **Positive maps and entanglement, only-if direction** (Wolf §3.2, Prop 3.4).  A
bipartite state of Schmidt number at most `n` satisfies `(T ⊗ id)(ρ) ≥ 0` for every
`n`-positive map `T`.

The state is a finite sum of pure-state projectors of Schmidt rank at most `n`; the
ampliation is linear, the pure-state step makes each summand positive semidefinite,
and a finite sum of positive semidefinite matrices is positive semidefinite.

**Scope restriction (square system d = d' = D):** inherited from the pure-state step;
see `docs/paper-gaps/wolf_reduction_criterion_schmidt_premise.tex`. -/
theorem HasSchmidtNumberLE.tensorMapId_posSemidef [NeZero D] {n : ℕ}
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hTpos : IsNPositiveMap n T)
    {ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ} (hρ : HasSchmidtNumberLE n ρ) :
    (tensorMapId T ρ).PosSemidef := by
  obtain ⟨ι, _, ψ, hψ, rfl⟩ := hρ
  rw [tensorMapId_sum]
  exact posSemidef_sum Finset.univ fun i _ =>
    tensorMapId_posSemidef_of_hasSchmidtRankLE hTpos (hψ i)

/-! ### Padding to a square system

The square forward step above fixes both tensor factors to the map's dimension
`d`.  To reach Wolf's general bipartite system `ℂ^d ⊗ ℂ^{d'}` we pad the second
factor up to `d` by zeros (valid when `d' ≤ d`), apply the square result, and
restrict back to the `d × d'` corner with `Matrix.PosSemidef.submatrix`.  The
padding is the standard zero-border dilation; it preserves Schmidt rank because
appending zero columns to the coefficient matrix cannot raise its rank. -/

/-- **Pad the second tensor factor of a bipartite vector by zeros.**  A vector on
`Fin d × Fin d'` is extended to `Fin d × Fin d` (used with `d' ≤ d`) by setting the
new coordinates `d' ≤ j < d` to zero, keeping the `d × d'` block.  Its coefficient
matrix is the original coefficient matrix bordered by zero columns. -/
def padSecondFactor (ψ : Fin d × Fin d' → ℂ) : Fin d × Fin d → ℂ :=
  fun p => if hp : (p.2 : ℕ) < d' then ψ (p.1, ⟨(p.2 : ℕ), hp⟩) else 0

/-- The corner-index embedding `Fin d × Fin d' ↪ Fin d × Fin d` that fixes the
first factor and includes the second factor as the initial `d'` coordinates. -/
def cornerEmbed (h : d' ≤ d) : Fin d × Fin d' → Fin d × Fin d :=
  fun p => (p.1, Fin.castLE h p.2)

@[simp]
theorem padSecondFactor_cornerEmbed (h : d' ≤ d) (ψ : Fin d × Fin d' → ℂ)
    (p : Fin d × Fin d') : padSecondFactor (ψ) (cornerEmbed h p) = ψ p := by
  cases p with
  | mk i j =>
    have hj : ((Fin.castLE h j : Fin d) : ℕ) < d' := by simp [Fin.castLE]
    have hidx : (⟨((Fin.castLE h j : Fin d) : ℕ), hj⟩ : Fin d') = j := Fin.ext rfl
    simp only [cornerEmbed, padSecondFactor, hj, dif_pos, hidx]

/-- Padding the second factor by zeros preserves the Schmidt-rank bound: the
padded coefficient matrix is the original coefficient matrix right-multiplied by a
zero-bordered inclusion, so its rank cannot exceed that of the original. -/
theorem hasSchmidtRankLE_padSecondFactor {n : ℕ}
    {ψ : Fin d × Fin d' → ℂ} (hψ : HasSchmidtRankLE n ψ) :
    HasSchmidtRankLE n (padSecondFactor ψ) := by
  classical
  -- The padded coefficient matrix factors as `schmidtCoeffMatrix ψ * E`, with `E`
  -- the zero-bordered inclusion `Fin d' → Fin d`.
  set M : Matrix (Fin d) (Fin d') ℂ := schmidtCoeffMatrix ψ with hM
  set E : Matrix (Fin d') (Fin d) ℂ :=
    fun k j => if hj : (j : ℕ) < d' then (if k = ⟨(j : ℕ), hj⟩ then 1 else 0) else 0
    with hE
  have hfactor : schmidtCoeffMatrix (padSecondFactor ψ) = M * E := by
    ext i j
    simp only [schmidtCoeffMatrix_apply, padSecondFactor, Matrix.mul_apply, hM, hE]
    by_cases hj : (j : ℕ) < d'
    · simp only [hj, dif_pos]
      rw [Finset.sum_eq_single (⟨(j : ℕ), hj⟩ : Fin d')]
      · simp
      · intro b _ hb
        simp [if_neg hb]
      · intro hb; exact absurd (Finset.mem_univ _) hb
    · simp only [hj, dif_neg, not_false_iff]
      symm
      apply Finset.sum_eq_zero
      intro k _
      simp
  have hrank : (schmidtCoeffMatrix (padSecondFactor ψ)).rank ≤ n := by
    rw [hfactor]
    exact (Matrix.rank_mul_le_left M E).trans hψ
  simpa [HasSchmidtRankLE, schmidtRank] using hrank

/-- The ampliation on the padded square system restricts on the `d × d'` corner to
the ampliation of the original state: `tensorMapId T ρ` is the corner submatrix of
the ampliation of the zero-padded state, because `tensorMapId` carries the second
factor through untouched and the padded second-factor coordinates lie inside the
corner. -/
theorem tensorMapId_padSecondFactor_submatrix (h : d' ≤ d)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    {ι : Type} [Fintype ι] (ψ : ι → (Fin d × Fin d' → ℂ)) :
    tensorMapId T (∑ i, vecMulVec (ψ i) (star (ψ i)))
      = (tensorMapId T
          (∑ i, vecMulVec (padSecondFactor (ψ i)) (star (padSecondFactor (ψ i))))).submatrix
        (cornerEmbed h) (cornerEmbed h) := by
  classical
  -- The padded summand restricted to the corner is the original summand.
  have hsum :
      (∑ i, vecMulVec (ψ i) (star (ψ i)))
        = (∑ i, vecMulVec (padSecondFactor (ψ i))
            (star (padSecondFactor (ψ i)))).submatrix (cornerEmbed h) (cornerEmbed h) := by
    ext p q
    simp only [Matrix.submatrix_apply, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply,
      padSecondFactor_cornerEmbed]
  -- The ampliation commutes with the corner restriction of the second factor.
  ext p q
  obtain ⟨i₁, i₂⟩ := p
  obtain ⟨j₁, j₂⟩ := q
  simp only [Matrix.submatrix_apply, cornerEmbed, tensorMapId_apply]
  -- The relevant second-factor slice agrees on the corner.
  have hslice :
      bipartiteSlice (∑ i, vecMulVec (ψ i) (star (ψ i))) i₂ j₂
        = bipartiteSlice (∑ i, vecMulVec (padSecondFactor (ψ i))
            (star (padSecondFactor (ψ i)))) (Fin.castLE h i₂) (Fin.castLE h j₂) := by
    ext a b
    simp only [bipartiteSlice]
    have := congrFun (congrFun hsum (a, i₂)) (b, j₂)
    simpa [cornerEmbed, Matrix.submatrix_apply] using this
  rw [hslice]

/-- **Positive maps and entanglement, only-if direction, pure-state step, differing
factors** (Wolf §3.2, Prop 3.4).  For a pure state `|ψ⟩⟨ψ|` on `ℂ^d ⊗ ℂ^{d'}` with
ψ of Schmidt rank at most `n`, the first factor `d` equal to the dimension of the
`n`-positive map `T`, and the second factor `d' ≤ d`, the ampliation
`(T ⊗ id)(|ψ⟩⟨ψ|)` is positive semidefinite.

The vector is padded to the square system `ℂ^d ⊗ ℂ^d` by zero columns, which keeps
the Schmidt rank at most `n`; the square pure-state step makes the padded ampliation
positive semidefinite; and the original ampliation is the `d × d'` corner submatrix
of the padded one, hence positive semidefinite.

**Scope restriction (d' ≤ d):** the second factor is padded up to the first factor
`d`, which requires `d' ≤ d`; the complementary case `d' > d` (extending `T` to the
larger square) is documented in
`docs/paper-gaps/wolf_reduction_criterion_schmidt_premise.tex`. -/
theorem tensorMapId_posSemidef_of_hasSchmidtRankLE' [NeZero d] {n : ℕ} (h : d' ≤ d)
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTpos : IsNPositiveMap n T) {ψ : Fin d × Fin d' → ℂ} (hψ : HasSchmidtRankLE n ψ) :
    (tensorMapId T (vecMulVec ψ (star ψ))).PosSemidef := by
  classical
  -- Pad to the square system and restrict back to the corner.
  have hsq :
      (tensorMapId T (vecMulVec (padSecondFactor ψ)
        (star (padSecondFactor ψ)))).PosSemidef :=
    tensorMapId_posSemidef_of_hasSchmidtRankLE hTpos (hasSchmidtRankLE_padSecondFactor hψ)
  have hcorner :
      tensorMapId T (vecMulVec ψ (star ψ))
        = (tensorMapId T (vecMulVec (padSecondFactor ψ)
            (star (padSecondFactor ψ)))).submatrix (cornerEmbed h) (cornerEmbed h) := by
    have := tensorMapId_padSecondFactor_submatrix (ι := PUnit) h T (fun _ => ψ)
    simpa using this
  rw [hcorner]
  exact hsq.submatrix (cornerEmbed h)

/-- **Positive maps and entanglement, only-if direction, differing factors**
(Wolf §3.2, Prop 3.4).  A bipartite state on `ℂ^d ⊗ ℂ^{d'}` of Schmidt number at
most `n`, with first factor `d` equal to the dimension of the `n`-positive map `T`
and second factor `d' ≤ d`, satisfies `(T ⊗ id)(ρ) ≥ 0`.

The state is padded to the square system `ℂ^d ⊗ ℂ^d` by zero columns on each pure
summand, which preserves the Schmidt-number bound; the square forward step makes the
padded ampliation positive semidefinite; and the original ampliation is its `d × d'`
corner submatrix.

**Scope restriction (d' ≤ d):** inherited from the pure-state step; the
complementary case `d' > d` is documented in
`docs/paper-gaps/wolf_reduction_criterion_schmidt_premise.tex`. -/
theorem HasSchmidtNumberLE.tensorMapId_posSemidef' [NeZero d] {n : ℕ} (h : d' ≤ d)
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTpos : IsNPositiveMap n T)
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ} (hρ : HasSchmidtNumberLE n ρ) :
    (tensorMapId T ρ).PosSemidef := by
  classical
  obtain ⟨ι, _, ψ, hψ, rfl⟩ := hρ
  -- Pad each pure summand and restrict the padded square ampliation to the corner.
  have hsq :
      (tensorMapId T
        (∑ i, vecMulVec (padSecondFactor (ψ i))
          (star (padSecondFactor (ψ i))))).PosSemidef := by
    rw [tensorMapId_sum]
    exact posSemidef_sum Finset.univ fun i _ =>
      tensorMapId_posSemidef_of_hasSchmidtRankLE hTpos
        (hasSchmidtRankLE_padSecondFactor (hψ i))
  rw [tensorMapId_padSecondFactor_submatrix h T ψ]
  exact hsq.submatrix (cornerEmbed h)

/-! ### Padding the first factor and extending the map

When the second factor exceeds the first, `d < d'`, the roles reverse: we pad the
*first* factor up to `d'` by zeros to reach the square system `ℂ^{d'} ⊗ ℂ^{d'}`, and
extend the map `T` to the larger square by the corner-compression sandwich
`ι ∘ T ∘ π`, where `π` compresses to the `d × d` principal corner and `ι` pads with
zeros.  The extended map is again `n`-positive, the square forward step applies, and
the original ampliation is the principal-corner submatrix of the padded one. -/

/-- **A matrix supported on the corner of an injection, positive semidefinite on that
corner, is positive semidefinite.**  If `M` vanishes whenever a row or column index
lies outside the range of an injective `g`, and the corner submatrix `M.submatrix g g`
is positive semidefinite, then `M` is positive semidefinite: writing the corner as a
sum of rank-one projectors and extending each coefficient vector by zero off the range
of `g` realizes `M` itself as a sum of rank-one projectors. -/
theorem posSemidef_of_submatrix_corner {α β : Type*} [Finite α] [Finite β]
    {g : α → β} (hg : Function.Injective g) {M : Matrix β β ℂ}
    (hsupp : ∀ i j, ((∀ a, g a ≠ i) ∨ ∀ a, g a ≠ j) → M i j = 0)
    (hpsd : (M.submatrix g g).PosSemidef) : M.PosSemidef := by
  classical
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  obtain ⟨m, u, hu⟩ := posSemidef_iff_eq_sum_vecMulVec.mp hpsd
  -- Extend each corner coefficient vector by zero off the range of `g`.
  set ũ : Fin m → (β → ℂ) :=
    fun k b => if hb : ∃ a, g a = b then u k hb.choose else 0 with hũ
  have hũg : ∀ (k : Fin m) (a : α), ũ k (g a) = u k a := by
    intro k a
    have hex : ∃ a', g a' = g a := ⟨a, rfl⟩
    simp only [hũ, hex, dif_pos]
    rw [hg hex.choose_spec]
  have hũoff : ∀ (k : Fin m) (b : β), (∀ a, g a ≠ b) → ũ k b = 0 := by
    intro k b hb
    have : ¬ ∃ a, g a = b := fun ⟨a, ha⟩ => hb a ha
    simp [hũ, this]
  refine posSemidef_iff_eq_sum_vecMulVec.mpr ⟨m, ũ, ?_⟩
  ext i j
  simp only [Matrix.sum_apply, vecMulVec_apply, Pi.star_apply]
  by_cases hi : ∃ a, g a = i
  · by_cases hj : ∃ a, g a = j
    · obtain ⟨a, rfl⟩ := hi
      obtain ⟨b, rfl⟩ := hj
      have hMij : M (g a) (g b) = (M.submatrix g g) a b := by
        simp [Matrix.submatrix_apply]
      rw [hMij, hu]
      simp only [Matrix.sum_apply, vecMulVec_apply, Pi.star_apply, hũg]
    · simp only [not_exists] at hj
      rw [hsupp i j (Or.inr hj)]
      symm
      apply Finset.sum_eq_zero
      intro k _
      rw [hũoff k j hj, star_zero, mul_zero]
  · simp only [not_exists] at hi
    rw [hsupp i j (Or.inl hi)]
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [hũoff k i hi, zero_mul]

/-- **Pad the first tensor factor of a bipartite vector by zeros.**  A vector on
`Fin d × Fin d'` is extended to `Fin d' × Fin d'` (used with `d ≤ d'`) by setting the
new first-factor coordinates `d ≤ i < d'` to zero, keeping the `d × d'` block.  Its
coefficient matrix is the original coefficient matrix bordered by zero rows. -/
def padFirstFactor (ψ : Fin d × Fin d' → ℂ) : Fin d' × Fin d' → ℂ :=
  fun p => if hp : (p.1 : ℕ) < d then ψ (⟨(p.1 : ℕ), hp⟩, p.2) else 0

/-- The corner-index embedding `Fin d × Fin d' ↪ Fin d' × Fin d'` that includes the
first factor as the initial `d` coordinates and fixes the second factor. -/
def cornerEmbedFirst (h : d ≤ d') : Fin d × Fin d' → Fin d' × Fin d' :=
  fun p => (Fin.castLE h p.1, p.2)

theorem cornerEmbedFirst_injective (h : d ≤ d') :
    Function.Injective (cornerEmbedFirst h : Fin d × Fin d' → Fin d' × Fin d') := by
  intro p q hpq
  simp only [cornerEmbedFirst, Prod.mk.injEq] at hpq
  exact Prod.ext (Fin.castLE_injective h hpq.1) hpq.2

@[simp]
theorem padFirstFactor_cornerEmbedFirst (h : d ≤ d') (ψ : Fin d × Fin d' → ℂ)
    (p : Fin d × Fin d') : padFirstFactor (ψ) (cornerEmbedFirst h p) = ψ p := by
  cases p with
  | mk i j =>
    have hi : ((Fin.castLE h i : Fin d') : ℕ) < d := by simp [Fin.castLE]
    have hidx : (⟨((Fin.castLE h i : Fin d') : ℕ), hi⟩ : Fin d) = i := Fin.ext rfl
    simp only [cornerEmbedFirst, padFirstFactor, hi, dif_pos, hidx]

/-- Padding the first factor by zeros preserves the Schmidt-rank bound: the padded
coefficient matrix is the original coefficient matrix left-multiplied by a
zero-bordered inclusion, so its rank cannot exceed that of the original. -/
theorem hasSchmidtRankLE_padFirstFactor {n : ℕ}
    {ψ : Fin d × Fin d' → ℂ} (hψ : HasSchmidtRankLE n ψ) :
    HasSchmidtRankLE n (padFirstFactor ψ) := by
  classical
  -- The padded coefficient matrix factors as `F * schmidtCoeffMatrix ψ`, with `F`
  -- the zero-bordered inclusion `Fin d' → Fin d`.
  set M : Matrix (Fin d) (Fin d') ℂ := schmidtCoeffMatrix ψ with hM
  set F : Matrix (Fin d') (Fin d) ℂ :=
    fun i k => if hi : (i : ℕ) < d then (if k = ⟨(i : ℕ), hi⟩ then 1 else 0) else 0
    with hF
  have hfactor : schmidtCoeffMatrix (padFirstFactor ψ) = F * M := by
    ext i j
    simp only [schmidtCoeffMatrix_apply, padFirstFactor, Matrix.mul_apply, hM, hF]
    by_cases hi : (i : ℕ) < d
    · simp only [hi, dif_pos]
      rw [Finset.sum_eq_single (⟨(i : ℕ), hi⟩ : Fin d)]
      · simp
      · intro b _ hb
        simp [if_neg hb]
      · intro hb; exact absurd (Finset.mem_univ _) hb
    · simp only [hi, dif_neg, not_false_iff]
      symm
      apply Finset.sum_eq_zero
      intro k _
      simp
  have hrank : (schmidtCoeffMatrix (padFirstFactor ψ)).rank ≤ n := by
    rw [hfactor]
    exact (Matrix.rank_mul_le_right F M).trans hψ
  simpa [HasSchmidtRankLE, schmidtRank] using hrank

/-- **Compress a matrix to its `d × d` principal corner** (`d ≤ d'`), as a linear map
`M_{d'} → M_d`.  This is the submatrix along the corner inclusion `Fin.castLE`. -/
noncomputable def cornerCompress (h : d ≤ d') :
    Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun X := X.submatrix (Fin.castLE h) (Fin.castLE h)
  map_add' X Y := by ext; simp
  map_smul' c X := by ext; simp

/-- **Pad a `d × d` matrix to the `d × d` principal corner of `M_{d'}`** (`d ≤ d'`),
as a linear map `M_d → M_{d'}`: entries inside the corner are kept, all others are
zero. -/
noncomputable def cornerPad (_h : d ≤ d') :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ where
  toFun Z := Matrix.of fun a b =>
    if ha : (a : ℕ) < d then (if hb : (b : ℕ) < d then Z ⟨a, ha⟩ ⟨b, hb⟩ else 0) else 0
  map_add' X Y := by
    ext a b
    by_cases ha : (a : ℕ) < d <;> by_cases hb : (b : ℕ) < d <;>
      simp [ha, hb, Matrix.of_apply]
  map_smul' c X := by
    ext a b
    by_cases ha : (a : ℕ) < d <;> by_cases hb : (b : ℕ) < d <;>
      simp [ha, hb, Matrix.of_apply]

/-- **Extend a square map to a larger square by corner sandwich** (`d ≤ d'`).  The map
`cornerExtendMap h T : M_{d'} → M_{d'}` first compresses its argument to the `d × d`
principal corner, applies `T`, and pads the result back with zeros.  It coincides with
`cornerPad ∘ T ∘ cornerCompress`. -/
noncomputable def cornerExtendMap (h : d ≤ d')
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d') (Fin d') ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ :=
  (cornerPad h).comp (T.comp (cornerCompress h))

theorem cornerExtendMap_apply (h : d ≤ d')
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (Z : Matrix (Fin d') (Fin d') ℂ) (a b : Fin d') :
    cornerExtendMap h T Z a b =
      if ha : (a : ℕ) < d then
        (if hb : (b : ℕ) < d then
          T (Z.submatrix (Fin.castLE h) (Fin.castLE h)) ⟨a, ha⟩ ⟨b, hb⟩ else 0) else 0 :=
  rfl

/-- **The corner extension preserves `n`-positivity** (the crux of the `d < d'` step).
If `T` is `n`-positive then so is `cornerExtendMap h T`.  Given a positive
semidefinite ampliated input on `ℂ^{d'} ⊗ ℂ^n`, the extended map's output is supported
on the `d × d` principal corner of the first factor, where it equals the ampliation of
`T` on the corner-compressed input — a principal submatrix of the input, hence positive
semidefinite, made positive semidefinite by the `n`-positivity of `T`.  A matrix
supported on the corner with that corner positive semidefinite is itself positive
semidefinite. -/
theorem isNPositiveMap_cornerExtendMap (h : d ≤ d') {n : ℕ}
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hT : IsNPositiveMap n T) : IsNPositiveMap n (cornerExtendMap h T) := by
  classical
  intro X hX
  -- The first-factor corner inclusion at the ampliated level.
  set g : Fin d × Fin n → Fin d' × Fin n :=
    fun p => (Fin.castLE h p.1, p.2) with hg
  have hginj : Function.Injective g := by
    intro p q hpq
    simp only [hg, Prod.mk.injEq] at hpq
    exact Prod.ext (Fin.castLE_injective h hpq.1) hpq.2
  set Y : Matrix (Fin d' × Fin n) (Fin d' × Fin n) ℂ :=
    Matrix.of fun ip jq =>
      (cornerExtendMap h T (Matrix.of fun i j => X (i, ip.2) (j, jq.2))) ip.1 jq.1 with hY
  -- `Y` is supported on the corner image of `g`: outside the corner the extension is 0.
  have hsupp : ∀ ip jq,
      ((∀ a, g a ≠ ip) ∨ ∀ a, g a ≠ jq) → Y ip jq = 0 := by
    intro ip jq hor
    simp only [hY, Matrix.of_apply, cornerExtendMap_apply]
    -- If `ip.1 ≥ d` or `jq.1 ≥ d`, the corner padding outputs zero.
    rcases hor with hi | hj
    · have hip1 : ¬ (ip.1 : ℕ) < d := by
        intro hlt
        exact hi (⟨ip.1, hlt⟩, ip.2)
          (Prod.ext (Fin.ext (by simp [g, Fin.castLE])) rfl)
      simp [hip1]
    · have hjq1 : ¬ (jq.1 : ℕ) < d := by
        intro hlt
        exact hj (⟨jq.1, hlt⟩, jq.2)
          (Prod.ext (Fin.ext (by simp [g, Fin.castLE])) rfl)
      by_cases hip1 : (ip.1 : ℕ) < d
      · simp [hip1, hjq1]
      · simp [hip1]
  -- The corner submatrix of `Y` is the `n`-ampliation of `T` on the compressed input.
  set X' : Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ := X.submatrix g g with hX'
  have hcorner : Y.submatrix g g =
      Matrix.of fun (ip : Fin d × Fin n) (jq : Fin d × Fin n) =>
        (T (Matrix.of fun i j => X' (i, ip.2) (j, jq.2))) ip.1 jq.1 := by
    ext ip jq
    have hi : ((Fin.castLE h ip.1 : Fin d') : ℕ) < d := by simp [Fin.castLE]
    have hj : ((Fin.castLE h jq.1 : Fin d') : ℕ) < d := by simp [Fin.castLE]
    have hidx_i : (⟨((Fin.castLE h ip.1 : Fin d') : ℕ), hi⟩ : Fin d) = ip.1 := Fin.ext rfl
    have hidx_j : (⟨((Fin.castLE h jq.1 : Fin d') : ℕ), hj⟩ : Fin d) = jq.1 := Fin.ext rfl
    -- The compressed padded slice equals the `X'` slice.
    have harg :
        (Matrix.of fun i j => X (i, ip.2) (j, jq.2)).submatrix
            (Fin.castLE h) (Fin.castLE h)
          = Matrix.of fun i j => X' (i, ip.2) (j, jq.2) := by
      ext a b
      simp only [Matrix.submatrix_apply, hX', Matrix.of_apply, hg]
    simp only [Matrix.submatrix_apply, hY, Matrix.of_apply, cornerExtendMap_apply, hg,
      hi, dif_pos, hj, hidx_i, hidx_j]
    rw [harg]
  -- That corner is positive semidefinite by `n`-positivity of `T` on a PSD input.
  have hX'psd : X'.PosSemidef := hX.submatrix g
  have hcornerpsd : (Y.submatrix g g).PosSemidef := by
    rw [hcorner]; exact hT X' hX'psd
  -- Assemble.
  exact posSemidef_of_submatrix_corner hginj hsupp hcornerpsd

/-- The padded square ampliation restricts on the `d × d'` corner of the first factor
to the original ampliation: `tensorMapId T ρ` (on `Fin d × Fin d'`) is the principal
submatrix of `tensorMapId (cornerExtendMap h T) ρ̃` (on `Fin d' × Fin d'`), where `ρ̃`
is the first-factor zero-padding of `ρ`.  The extended map outputs zero off the corner
and reproduces `T` on it, and the padded state agrees with the original on the corner. -/
theorem tensorMapId_padFirstFactor_submatrix (h : d ≤ d')
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    {ι : Type} [Fintype ι] (ψ : ι → (Fin d × Fin d' → ℂ)) :
    tensorMapId T (∑ i, vecMulVec (ψ i) (star (ψ i)))
      = (tensorMapId (cornerExtendMap h T)
          (∑ i, vecMulVec (padFirstFactor (ψ i))
            (star (padFirstFactor (ψ i))))).submatrix
              (cornerEmbedFirst h) (cornerEmbedFirst h) := by
  classical
  ext p q
  obtain ⟨i₁, i₂⟩ := p
  obtain ⟨j₁, j₂⟩ := q
  simp only [Matrix.submatrix_apply, cornerEmbedFirst, tensorMapId_apply,
    cornerExtendMap_apply]
  have hi : ((Fin.castLE h i₁ : Fin d') : ℕ) < d := by simp [Fin.castLE]
  have hj : ((Fin.castLE h j₁ : Fin d') : ℕ) < d := by simp [Fin.castLE]
  have hidx_i : (⟨((Fin.castLE h i₁ : Fin d') : ℕ), hi⟩ : Fin d) = i₁ := Fin.ext rfl
  have hidx_j : (⟨((Fin.castLE h j₁ : Fin d') : ℕ), hj⟩ : Fin d) = j₁ := Fin.ext rfl
  -- The compressed padded slice equals the original slice.
  have hslice :
      (bipartiteSlice (∑ i, vecMulVec (padFirstFactor (ψ i))
          (star (padFirstFactor (ψ i)))) i₂ j₂).submatrix (Fin.castLE h) (Fin.castLE h)
        = bipartiteSlice (∑ i, vecMulVec (ψ i) (star (ψ i))) i₂ j₂ := by
    ext a b
    simp only [Matrix.submatrix_apply, bipartiteSlice, Matrix.sum_apply, vecMulVec_apply,
      Pi.star_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    have ha : padFirstFactor (ψ k) (Fin.castLE h a, i₂) = ψ k (a, i₂) :=
      padFirstFactor_cornerEmbedFirst h (ψ k) (a, i₂)
    have hb : padFirstFactor (ψ k) (Fin.castLE h b, j₂) = ψ k (b, j₂) :=
      padFirstFactor_cornerEmbedFirst h (ψ k) (b, j₂)
    rw [ha, hb]
  simp only [hi, dif_pos, hj, hslice, hidx_i, hidx_j]

/-- **Positive maps and entanglement, only-if direction, pure-state step, second
factor larger** (Wolf §3.2, Prop 3.4).  For a pure state `|ψ⟩⟨ψ|` on
`ℂ^d ⊗ ℂ^{d'}` with ψ of Schmidt rank at most `n`, the first factor `d` equal to the
dimension of the `n`-positive map `T`, and `d ≤ d'`, the ampliation
`(T ⊗ id)(|ψ⟩⟨ψ|)` is positive semidefinite.

The vector is padded on the first factor to the square system `ℂ^{d'} ⊗ ℂ^{d'}`, which
keeps the Schmidt rank at most `n`; the map `T` is extended to that square by the
corner sandwich, which stays `n`-positive; the square pure-state step makes the padded
ampliation positive semidefinite; and the original ampliation is its `d × d'`
principal-corner submatrix.

**Scope restriction (d ≤ d'):** the first factor is padded up to the second factor
`d'`; the complementary case `d' ≤ d` is `tensorMapId_posSemidef_of_hasSchmidtRankLE'`.
Both are combined without restriction in `tensorMapId_posSemidef_of_hasSchmidtRankLE_general`. -/
theorem tensorMapId_posSemidef_of_hasSchmidtRankLE'' [NeZero d'] {n : ℕ} (h : d ≤ d')
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTpos : IsNPositiveMap n T) {ψ : Fin d × Fin d' → ℂ} (hψ : HasSchmidtRankLE n ψ) :
    (tensorMapId T (vecMulVec ψ (star ψ))).PosSemidef := by
  classical
  -- Pad the first factor to the square system and restrict back to the corner.
  have hsq :
      (tensorMapId (cornerExtendMap h T) (vecMulVec (padFirstFactor ψ)
        (star (padFirstFactor ψ)))).PosSemidef :=
    tensorMapId_posSemidef_of_hasSchmidtRankLE (isNPositiveMap_cornerExtendMap h hTpos)
      (hasSchmidtRankLE_padFirstFactor hψ)
  have hcorner :
      tensorMapId T (vecMulVec ψ (star ψ))
        = (tensorMapId (cornerExtendMap h T) (vecMulVec (padFirstFactor ψ)
            (star (padFirstFactor ψ)))).submatrix (cornerEmbedFirst h) (cornerEmbedFirst h) := by
    have := tensorMapId_padFirstFactor_submatrix (ι := PUnit) h T (fun _ => ψ)
    simpa using this
  rw [hcorner]
  exact hsq.submatrix (cornerEmbedFirst h)

/-- **Positive maps and entanglement, only-if direction, second factor larger**
(Wolf §3.2, Prop 3.4).  A bipartite state on `ℂ^d ⊗ ℂ^{d'}` of Schmidt number at
most `n`, with first factor `d` equal to the dimension of the `n`-positive map `T`
and `d ≤ d'`, satisfies `(T ⊗ id)(ρ) ≥ 0`.

Each pure summand is padded on the first factor to the square system `ℂ^{d'} ⊗ ℂ^{d'}`,
which preserves the Schmidt-number bound; the corner extension of `T` stays
`n`-positive; the square forward step makes the padded ampliation positive
semidefinite; and the original ampliation is its `d × d'` principal-corner submatrix.

**Scope restriction (d ≤ d'):** inherited from the pure-state step; the complementary
case `d' ≤ d` is `HasSchmidtNumberLE.tensorMapId_posSemidef'`.  Both are combined
without restriction in `HasSchmidtNumberLE.tensorMapId_posSemidef_general`. -/
theorem HasSchmidtNumberLE.tensorMapId_posSemidef'' [NeZero d'] {n : ℕ} (h : d ≤ d')
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTpos : IsNPositiveMap n T)
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ} (hρ : HasSchmidtNumberLE n ρ) :
    (tensorMapId T ρ).PosSemidef := by
  classical
  obtain ⟨ι, _, ψ, hψ, rfl⟩ := hρ
  -- Pad each pure summand on the first factor and restrict to the corner.
  have hsq :
      (tensorMapId (cornerExtendMap h T)
        (∑ i, vecMulVec (padFirstFactor (ψ i))
          (star (padFirstFactor (ψ i))))).PosSemidef := by
    rw [tensorMapId_sum]
    exact posSemidef_sum Finset.univ fun i _ =>
      tensorMapId_posSemidef_of_hasSchmidtRankLE (isNPositiveMap_cornerExtendMap h hTpos)
        (hasSchmidtRankLE_padFirstFactor (hψ i))
  rw [tensorMapId_padFirstFactor_submatrix h T ψ]
  exact hsq.submatrix (cornerEmbedFirst h)

/-! ### The general bipartite forward step

Combining the two padding directions removes every restriction relating the two
tensor factors.  For a pure state or a state of bounded Schmidt number on a general
bipartite system `ℂ^d ⊗ ℂ^{d'}` with first factor `d` equal to the map's dimension,
the ampliation `(T ⊗ id)` of any `n`-positive map is positive semidefinite. -/

/-- **Positive maps and entanglement, only-if direction, pure-state step, general
bipartite second factor** (Wolf §3.2, Prop 3.4, eq. (3.18) step 1).  For a pure state
`|ψ⟩⟨ψ|` on a general bipartite system `ℂ^d ⊗ ℂ^{d'}` with ψ of Schmidt rank at most
`n` and first factor `d` equal to the dimension of the `n`-positive map `T`, the
ampliation `(T ⊗ id)(|ψ⟩⟨ψ|)` is positive semidefinite, with no relation imposed
between the two tensor factors.

The two padding directions cover the full range: when the second factor is the smaller,
`d' ≤ d`, the second factor is padded up to `d`; when it is the larger, `d ≤ d'`, the
first factor is padded up to `d'` and `T` is extended to the larger square. -/
theorem tensorMapId_posSemidef_of_hasSchmidtRankLE_general [NeZero d] [NeZero d'] {n : ℕ}
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTpos : IsNPositiveMap n T) {ψ : Fin d × Fin d' → ℂ} (hψ : HasSchmidtRankLE n ψ) :
    (tensorMapId T (vecMulVec ψ (star ψ))).PosSemidef := by
  rcases le_or_gt d' d with h | h
  · exact tensorMapId_posSemidef_of_hasSchmidtRankLE' h hTpos hψ
  · exact tensorMapId_posSemidef_of_hasSchmidtRankLE'' h.le hTpos hψ

/-- **Positive maps and entanglement, only-if direction, general bipartite second
factor** (Wolf §3.2, Prop 3.4, eq. (3.18) step 1).  A bipartite state on a general
system `ℂ^d ⊗ ℂ^{d'}` of Schmidt number at most `n`, with first factor `d` equal to the
dimension of the `n`-positive map `T`, satisfies `(T ⊗ id)(ρ) ≥ 0`, with no relation
imposed between the two tensor factors.

This is the faithful bipartite forward step of Wolf eq. (3.18): the two padding
directions of the pure-state step (`d' ≤ d` padding the second factor, `d ≤ d'` padding
the first factor and extending `T`) jointly cover all `d'`, and the ampliation is
linear over the finite pure-state decomposition. -/
theorem HasSchmidtNumberLE.tensorMapId_posSemidef_general [NeZero d] [NeZero d'] {n : ℕ}
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ}
    (hTpos : IsNPositiveMap n T)
    {ρ : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ} (hρ : HasSchmidtNumberLE n ρ) :
    (tensorMapId T ρ).PosSemidef := by
  rcases le_or_gt d' d with h | h
  · exact hρ.tensorMapId_posSemidef' h hTpos
  · exact hρ.tensorMapId_posSemidef'' h.le hTpos

/-- **The pure-state step of the reduction criterion (Wolf eq. (3.18), step 1).**
For a pure state `|ψ⟩⟨ψ|` with ψ of Schmidt rank at most `n` (and `1 ≤ n < D`),
the ampliation `(T_n ⊗ id)(|ψ⟩⟨ψ|)` is positive semidefinite.

Writing ψ through the maximally entangled vector as a square right-factor matrix `X`
of rank equal to the Schmidt rank of ψ, the ampliation is the right-factor Choi
compression of `T_n` by `X`.  Its quadratic form on any vector is the Choi quadratic
form of `T_n` on a vector of Schmidt rank at most the rank of `X`, hence at most `n`;
the `n`-positivity of `T_n` (Wolf eq. (3.11)) makes that form nonnegative.

**Scope restriction (1 ≤ n < D):** the `n`-positivity threshold of `T_η` is
formalized for `1 ≤ n < D`.  The omitted top index `n = D` (complete positivity) is
inherited through the maximal-overlap principle and documented in
`docs/paper-gaps/wolf_t_eta_top_index_scope.tex`.

**Scope restriction (square system d = d' = D):** both tensor factors are fixed to a
common dimension `D`, because the pure state is parametrized through the square
maximally entangled vector (`ChoiJamiolkowski.exists_squareCompression_of_vector`).
Wolf states the criterion for a general bipartite system `ℂ^d ⊗ ℂ^{d'}`; the
non-square case is documented in
`docs/paper-gaps/wolf_reduction_criterion_schmidt_premise.tex`. -/
theorem tensorMapId_tEta_posSemidef_of_hasSchmidtRankLE [NeZero D] {n : ℕ}
    (hn1 : 1 ≤ n) (hnD : n < D) {ψ : Fin D × Fin D → ℂ} (hψ : HasSchmidtRankLE n ψ) :
    (tensorMapId (tEta D (n : ℝ)) (vecMulVec ψ (star ψ))).PosSemidef :=
  -- `T_n` is `n`-positive (Wolf eq. (3.11)); the general only-if step applies.
  tensorMapId_posSemidef_of_hasSchmidtRankLE
    ((isNPositiveMap_tEta_iff (by positivity) hn1 hnD).mpr (le_refl _)) hψ

/-- **Step 1 of Wolf's reduction criterion (eq. (3.18)).**  A bipartite state of
Schmidt number at most `n` (with `1 ≤ n < D`) has `(T_n ⊗ id)(ρ) ≥ 0`.

The state is a finite sum of pure-state projectors of Schmidt rank at most `n`; the
ampliation is linear, the pure-state step makes each summand positive semidefinite,
and a finite sum of positive semidefinite matrices is positive semidefinite.

**Scope restriction (1 ≤ n < D; square system d = d' = D):** inherited from the
pure-state step; see `docs/paper-gaps/wolf_t_eta_top_index_scope.tex` and
`docs/paper-gaps/wolf_reduction_criterion_schmidt_premise.tex`. -/
theorem HasSchmidtNumberLE.tensorMapId_tEta_posSemidef [NeZero D] {n : ℕ}
    (hn1 : 1 ≤ n) (hnD : n < D)
    {ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ} (hρ : HasSchmidtNumberLE n ρ) :
    (tensorMapId (tEta D (n : ℝ)) ρ).PosSemidef :=
  -- `T_n` is `n`-positive (Wolf eq. (3.11)); the general only-if direction applies.
  hρ.tensorMapId_posSemidef
    ((isNPositiveMap_tEta_iff (by positivity) hn1 hnD).mpr (le_refl _))

/-! ## The full reduction criterion (Wolf eq. (3.18)) -/

/-- **Wolf's reduction criterion (eq. (3.18)), second form, with the Schmidt-number
premise.**  A bipartite state of Schmidt number at most `n` (with `1 ≤ n < D`)
satisfies `n • (1 ⊗ ρ₂) ≥ ρ`, where `ρ₂ = traceLeft ρ` is the reduced density on the
second factor.

This is Wolf's full two-step argument: the Schmidt-number premise gives
`(T_n ⊗ id)(ρ) ≥ 0` (step 1), and the operator inequality then yields the bound
(step 2).

**Scope restriction (1 ≤ n < D; square system d = d' = D):** inherited from step 1;
see `docs/paper-gaps/wolf_t_eta_top_index_scope.tex` and
`docs/paper-gaps/wolf_reduction_criterion_schmidt_premise.tex`. -/
theorem reductionCriterion_left_of_hasSchmidtNumberLE [NeZero D] {n : ℕ}
    (hn1 : 1 ≤ n) (hnD : n < D)
    {ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ} (hρ : HasSchmidtNumberLE n ρ) :
    ρ ≤ (n : ℂ) • ((1 : Matrix (Fin D) (Fin D) ℂ) ⊗ₖ traceLeft ρ) :=
  reductionCriterion_left (by omega) ρ (hρ.tensorMapId_tEta_posSemidef hn1 hnD)

/-- **Wolf's reduction criterion (eq. (3.18)), first form, with the Schmidt-number
premise.**  A bipartite state of Schmidt number at most `n` (with `1 ≤ n < D`)
satisfies `n • (ρ₁ ⊗ 1) ≥ ρ`, where `ρ₁ = traceRight ρ` is the reduced density on the
first factor.

The factor swap of a state of Schmidt number at most `n` again has Schmidt number at
most `n`, since the swap reindexes each pure summand to a vector with the transposed
coefficient matrix, of the same rank.  Applying step 1 to the swapped state supplies
the symmetric hypothesis of the operator-implication lemma.

**Scope restriction (1 ≤ n < D; square system d = d' = D):** inherited from step 1;
see `docs/paper-gaps/wolf_t_eta_top_index_scope.tex` and
`docs/paper-gaps/wolf_reduction_criterion_schmidt_premise.tex`. -/
theorem reductionCriterion_right_of_hasSchmidtNumberLE [NeZero D] {n : ℕ}
    (hn1 : 1 ≤ n) (hnD : n < D)
    {ρ : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ} (hρ : HasSchmidtNumberLE n ρ) :
    ρ ≤ (n : ℂ) • (traceRight ρ ⊗ₖ (1 : Matrix (Fin D) (Fin D) ℂ)) := by
  -- The factor swap of ρ again has Schmidt number at most n.
  have hswap : HasSchmidtNumberLE n (ρ.submatrix Prod.swap Prod.swap) := by
    obtain ⟨ι, _, ψ, hψ, rfl⟩ := hρ
    refine ⟨ι, inferInstance, fun i => (ψ i) ∘ Prod.swap, fun i => ?_, ?_⟩
    · -- The swapped vector has the transposed coefficient matrix, of equal rank.
      have hcoeff :
          schmidtCoeffMatrix ((ψ i) ∘ Prod.swap) = (schmidtCoeffMatrix (ψ i))ᵀ := by
        ext a b; simp [schmidtCoeffMatrix, Function.comp]
      rw [HasSchmidtRankLE, schmidtRank, hcoeff, Matrix.rank_transpose]
      exact hψ i
    · ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
      simp only [Matrix.submatrix_apply, Matrix.sum_apply, vecMulVec_apply, Pi.star_apply,
        Prod.swap_prod_mk, Function.comp_apply]
  exact reductionCriterion_right (by omega) ρ (hswap.tensorMapId_tEta_posSemidef hn1 hnD)

end Matrix
