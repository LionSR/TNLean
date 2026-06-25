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

**Scope restriction (square system d = d' = D):** the forward reduction step fixes
both tensor factors to a common dimension `D`, because the pure state is parametrized
through the square maximally entangled vector; Wolf states eq. (3.18) for a general
bipartite system `ℂ^d ⊗ ℂ^{d'}`, and the non-square case is documented in
`docs/paper-gaps/wolf_reduction_criterion_schmidt_premise.tex`.  The Schmidt-number
predicate itself and its equivalence with separability carry no such restriction.

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
