/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.ConjugationOddRankEquivalence
import TNLean.MPS.MPU.FundamentalTheoremGatesBlocked

/-!
# Equivalence of conjugation-invariant MPUs in the same case

Two conjugation-invariant MPUs in canonical form II whose standard forms have the
same even ranks `ℓ, r` and lie in the same case of Proposition `corconj` are
equivalent under conjugation symmetry. This is the "if" direction of
arXiv:1703.09188, Corollary `cor:equiv-under-conjugation`, lines 1548--1567.

The proof follows the source. After a gauge bringing both standard forms to the
normal form `ortuv` (Case I) or `sympuv` (Case II), the doubled gates
`u⁽²⁾, v⁽²⁾` of `MPOTensor.TwoSiteStandardFormData.doubled` satisfy the same
normal form, with `Σ_ℓ ⊗ 1_d` and `1_d ⊗ Σ_r` in Case II, and their determinants
agree for both tensors. Theorem `prop:conjsym-strict-equiv` makes the blocks of
four sites strictly equivalent under conjugation.

## Main definitions and results

* `MPOTensor.IsConjugationCaseI`, `MPOTensor.IsConjugationCaseII`: the two cases
  of Proposition `corconj`.
* `MPOTensor.equivalentUnderSymmetry_conjugation_of_same_case`: the corollary,
  "if" direction.
-/

open scoped Matrix Kronecker

namespace MPOTensor

variable {d D₁ D₂ ℓ r : ℕ}

/-- **Case I of Proposition `corconj`.** Standard-form gates `u, v` satisfy the
conjugation relations of Proposition `prop1conj`,
`conj u = (x ⊗ y) u` and `conj v = v (y† ⊗ x†)`, with symmetric unitaries `x, y`.
Source: arXiv:1703.09188, Propositions `prop1conj` (lines 1014--1027) and
`corconj` (lines 1098--1110). -/
def IsConjugationCaseI (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) : Prop :=
  ∃ (x : Matrix (Fin ℓ) (Fin ℓ) ℂ) (y : Matrix (Fin r) (Fin r) ℂ),
    x ∈ Matrix.unitaryGroup (Fin ℓ) ℂ ∧ y ∈ Matrix.unitaryGroup (Fin r) ℂ ∧ xᵀ = x ∧ yᵀ = y ∧
      u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u ∧ v.map (starRingEnd ℂ) = v * (yᴴ ⊗ₖ xᴴ)

/-- **Case II of Proposition `corconj`.** Standard-form gates `u, v` satisfy the
conjugation relations of Proposition `prop1conj` with skew-symmetric unitaries
`x, y`. Source: arXiv:1703.09188, Propositions `prop1conj` (lines 1014--1027) and
`corconj` (lines 1111--1120). -/
def IsConjugationCaseII (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) : Prop :=
  ∃ (x : Matrix (Fin ℓ) (Fin ℓ) ℂ) (y : Matrix (Fin r) (Fin r) ℂ),
    x ∈ Matrix.unitaryGroup (Fin ℓ) ℂ ∧ y ∈ Matrix.unitaryGroup (Fin r) ℂ ∧ xᵀ = -x ∧
      yᵀ = -y ∧ u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u ∧ v.map (starRingEnd ℂ) = v * (yᴴ ⊗ₖ xᴴ)

theorem map_star_kronecker {m n m' n' : Type*} (A : Matrix m n ℂ) (B : Matrix m' n' ℂ) :
    (A ⊗ₖ B).map (starRingEnd ℂ) = A.map (starRingEnd ℂ) ⊗ₖ B.map (starRingEnd ℂ) := by
  ext i j
  simp [Matrix.kroneckerMap_apply]

private theorem map_star_reindex {m n m' n' : Type*} (e : m ≃ m') (f : n ≃ n')
    (A : Matrix m n ℂ) :
    (Matrix.reindex e f A).map (starRingEnd ℂ) = Matrix.reindex e f (A.map (starRingEnd ℂ)) :=
  rfl

private theorem reindex_mul_reindex {m n o m' n' o' : Type*} [Fintype n] [Fintype n']
    (e : m ≃ m') (f : n ≃ n') (g : o ≃ o') (A : Matrix m n ℂ) (B : Matrix n o ℂ) :
    Matrix.reindex e f A * Matrix.reindex f g B = Matrix.reindex e g (A * B) := by
  simp only [Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv A B e.symm f.symm g.symm

/-- **The doubled gates keep the symplectic normal form.** If
`conj u = (X ⊗ Y) u` and `conj v = v (Y ⊗ X)` with `X² = -1` and `Y² = -1`,
then `conj u⁽²⁾ = ((X ⊗ 1_d) ⊗ (1_d ⊗ Y)) u⁽²⁾`.
Source: arXiv:1703.09188, proof of Corollary `cor:equiv-under-conjugation`,
lines 1559--1564. -/
theorem doubledU_map_star_of_skew {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    {X : Matrix (Fin ℓ) (Fin ℓ) ℂ} {Y : Matrix (Fin r) (Fin r) ℂ}
    (hX : X * X = -1) (hY : Y * Y = -1)
    (hu : u.map (starRingEnd ℂ) = (X ⊗ₖ Y) * u) (hv : v.map (starRingEnd ℂ) = v * (Y ⊗ₖ X)) :
    (doubledU u v).map (starRingEnd ℂ) =
      (Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) ⊗ₖ
        Matrix.reindex finProdFinEquiv finProdFinEquiv
          ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Y)) * doubledU u v := by
  set Z : Matrix (Fin ℓ × ((Fin d × Fin d) × Fin r)) (Fin ℓ × ((Fin d × Fin d) × Fin r)) ℂ :=
    X ⊗ₖ ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ Y)
  have hZ : Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) ⊗ₖ
      Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Y) =
      Matrix.reindex (doubledOutEquiv ℓ d r) (doubledOutEquiv ℓ d r) Z := by
    ext ⟨i, j⟩ ⟨i', j'⟩
    obtain ⟨⟨t, a⟩, rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨⟨b, s⟩, rfl⟩ := finProdFinEquiv.surjective j
    obtain ⟨⟨t', a'⟩, rfl⟩ := finProdFinEquiv.surjective i'
    obtain ⟨⟨b', s'⟩, rfl⟩ := finProdFinEquiv.surjective j'
    simp [Z, doubledOutEquiv, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]
    split_ifs <;> simp_all
  have hW : ((1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ ((Y ⊗ₖ X) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ))) *
      Matrix.reindex (doubledMidEquiv ℓ r) (doubledMidEquiv ℓ r) ((X ⊗ₖ Y) ⊗ₖ (X ⊗ₖ Y)) =
      X ⊗ₖ ((1 : Matrix (Fin r × Fin ℓ) (Fin r × Fin ℓ) ℂ) ⊗ₖ Y) := by
    have hM : Matrix.reindex (doubledMidEquiv ℓ r) (doubledMidEquiv ℓ r)
        ((X ⊗ₖ Y) ⊗ₖ (X ⊗ₖ Y)) = X ⊗ₖ ((Y ⊗ₖ X) ⊗ₖ Y) := by
      ext ⟨a, ⟨b, c⟩, e⟩ ⟨a', ⟨b', c'⟩, e'⟩
      simp [doubledMidEquiv, Matrix.kroneckerMap_apply]
      ring
    have hYX : (Y ⊗ₖ X) * (Y ⊗ₖ X) = 1 := by
      rw [← Matrix.mul_kronecker_mul, hX, hY]
      ext i j
      simp only [Matrix.kroneckerMap_apply, Matrix.neg_apply, Matrix.one_apply]
      split_ifs <;> simp_all [Prod.ext_iff]
    rw [hM, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, hYX, Matrix.one_mul,
      Matrix.one_mul]
  have hK : ((1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ ((v * (Y ⊗ₖ X)) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ))) =
      ((1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (v ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ))) *
        ((1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ ((Y ⊗ₖ X) ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ))) := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
  have hKZ : ((1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (v ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ))) *
      (X ⊗ₖ ((1 : Matrix (Fin r × Fin ℓ) (Fin r × Fin ℓ) ℂ) ⊗ₖ Y)) =
      Z * ((1 : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (v ⊗ₖ (1 : Matrix (Fin r) (Fin r) ℂ))) := by
    simp only [Z, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [hZ, doubledU, map_star_reindex, Matrix.map_mul, map_star_reindex, map_star_kronecker,
    map_star_kronecker, map_star_kronecker, hu, hv, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_one _ (map_zero _) (map_one _), hK, Matrix.mul_kronecker_mul,
    ← reindex_mul_reindex (doubledMidEquiv ℓ r) (doubledMidEquiv ℓ r) (Equiv.refl _),
    ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (Matrix.reindex _ _ ((X ⊗ₖ Y) ⊗ₖ (X ⊗ₖ Y))), hW,
    hKZ, Matrix.mul_assoc, reindex_mul_reindex]

/-- **The doubled shifted gate keeps the symplectic normal form.** If
`conj v = v (Y ⊗ X)`, then `conj v⁽²⁾ = v⁽²⁾ ((1_d ⊗ Y) ⊗ (X ⊗ 1_d))`.
Source: arXiv:1703.09188, proof of Corollary `cor:equiv-under-conjugation`,
lines 1559--1564. -/
theorem doubledV_map_star_of_skew {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    {X : Matrix (Fin ℓ) (Fin ℓ) ℂ} {Y : Matrix (Fin r) (Fin r) ℂ}
    (hv : v.map (starRingEnd ℂ) = v * (Y ⊗ₖ X)) :
    (doubledV v).map (starRingEnd ℂ) = doubledV v *
      (Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Y) ⊗ₖ
        Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))) := by
  have hZ : Matrix.reindex finProdFinEquiv finProdFinEquiv ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ Y) ⊗ₖ
      Matrix.reindex finProdFinEquiv finProdFinEquiv (X ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) =
      Matrix.reindex (doubledShiftInEquiv ℓ d r) (doubledShiftInEquiv ℓ d r)
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ ((Y ⊗ₖ X) ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))) := by
    ext ⟨i, j⟩ ⟨i', j'⟩
    obtain ⟨⟨b, s⟩, rfl⟩ := finProdFinEquiv.surjective i
    obtain ⟨⟨t, a⟩, rfl⟩ := finProdFinEquiv.surjective j
    obtain ⟨⟨b', s'⟩, rfl⟩ := finProdFinEquiv.surjective i'
    obtain ⟨⟨t', a'⟩, rfl⟩ := finProdFinEquiv.surjective j'
    simp [doubledShiftInEquiv, Matrix.kroneckerMap_apply, Matrix.one_apply]
  rw [hZ, doubledV, map_star_reindex, map_star_kronecker, map_star_kronecker, hv,
    Matrix.map_one _ (map_zero _) (map_one _), reindex_mul_reindex]
  congr 1
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- A matrix agreeing with `1 ⊗ Y` along an identification `τ` is the source skew
form after relabelling. -/
private theorem reindex_eq_sourceSkewForm {n : ℕ} (h : Even n) (A : Matrix (Fin n) (Fin n) ℂ)
    (τ : Fin (n / 2) × Fin 2 ≃ Fin n)
    (hA : ∀ x y, A (τ x) (τ y) =
      ((1 : Matrix (Fin (n / 2)) (Fin (n / 2)) ℂ) ⊗ₖ Matrix.symplecticY) x y) :
    Matrix.reindex ((Matrix.evenPairEquiv h).symm.trans τ).symm
      ((Matrix.evenPairEquiv h).symm.trans τ).symm A = Matrix.sourceSkewForm h := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.sourceSkewForm, hA]

private theorem half_mul_left {m : ℕ} (n : ℕ) (hm : Even m) : m * n / 2 = m / 2 * n := by
  obtain ⟨k, rfl⟩ := hm
  rw [show (k + k) * n = 2 * (k * n) by ring, show k + k = 2 * k by ring,
    Nat.mul_div_cancel_left _ two_pos, Nat.mul_div_cancel_left _ two_pos]

private theorem half_mul_right (m : ℕ) {n : ℕ} (hn : Even n) : m * n / 2 = m * (n / 2) := by
  rw [Nat.mul_comm, half_mul_left m hn, Nat.mul_comm]

/-- The pairing of `Fin (m n / 2) × Fin 2` with `Fin (m n)` that carries the skew
pairs of the first factor. -/
private def skewLeftPairing {m : ℕ} (n : ℕ) (hm : Even m) :
    Fin (m * n / 2) × Fin 2 ≃ Fin (m * n) :=
  (Equiv.prodCongr ((finCongr (half_mul_left n hm)).trans finProdFinEquiv.symm)
      (Equiv.refl (Fin 2))).trans
    (((Equiv.prodAssoc _ _ _).trans ((Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)).trans
      (Equiv.prodAssoc _ _ _).symm)).trans
    ((Equiv.prodCongr (Matrix.evenPairEquiv hm) (Equiv.refl (Fin n))).trans finProdFinEquiv))

/-- The pairing of `Fin (m n / 2) × Fin 2` with `Fin (m n)` that carries the skew
pairs of the second factor. -/
private def skewRightPairing (m : ℕ) {n : ℕ} (hn : Even n) :
    Fin (m * n / 2) × Fin 2 ≃ Fin (m * n) :=
  (Equiv.prodCongr ((finCongr (half_mul_right m hn)).trans finProdFinEquiv.symm)
      (Equiv.refl (Fin 2))).trans
    ((Equiv.prodAssoc _ _ _).trans
    ((Equiv.prodCongr (Equiv.refl (Fin m)) (Matrix.evenPairEquiv hn)).trans finProdFinEquiv))

private theorem skewLeftPairing_apply {m : ℕ} (n : ℕ) (hm : Even m) (p : Fin (m / 2))
    (c : Fin n) (b : Fin 2) :
    skewLeftPairing n hm ((finCongr (half_mul_left n hm)).symm (finProdFinEquiv (p, c)), b) =
      finProdFinEquiv (Matrix.evenPairEquiv hm (p, b), c) := by
  simp [skewLeftPairing]

private theorem skewRightPairing_apply (m : ℕ) {n : ℕ} (hn : Even n) (c : Fin m)
    (p : Fin (n / 2)) (b : Fin 2) :
    skewRightPairing m hn ((finCongr (half_mul_right m hn)).symm (finProdFinEquiv (c, p)), b) =
      finProdFinEquiv (c, Matrix.evenPairEquiv hn (p, b)) := by
  simp [skewRightPairing]

theorem exists_reindex_sourceSkewForm_kronecker_one {m : ℕ} (n : ℕ) (hm : Even m)
    (h : Even (m * n)) :
    ∃ σ : Fin (m * n) ≃ Fin (m * n),
      Matrix.reindex σ σ (Matrix.reindex finProdFinEquiv finProdFinEquiv
        (Matrix.sourceSkewForm hm ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ))) =
        Matrix.sourceSkewForm h := by
  refine ⟨_, reindex_eq_sourceSkewForm h _ (skewLeftPairing n hm) ?_⟩
  rintro ⟨q, b⟩ ⟨q', b'⟩
  obtain ⟨⟨p, c⟩, rfl⟩ : ∃ x, (finCongr (half_mul_left n hm)).symm (finProdFinEquiv x) = q :=
    ⟨finProdFinEquiv.symm (finCongr (half_mul_left n hm) q),
      by simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]⟩
  obtain ⟨⟨p', c'⟩, rfl⟩ : ∃ x, (finCongr (half_mul_left n hm)).symm (finProdFinEquiv x) = q' :=
    ⟨finProdFinEquiv.symm (finCongr (half_mul_left n hm) q'),
      by simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]⟩
  rw [skewLeftPairing_apply, skewLeftPairing_apply]
  simp [Matrix.sourceSkewForm, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

theorem exists_reindex_one_kronecker_sourceSkewForm (m : ℕ) {n : ℕ} (hn : Even n)
    (h : Even (m * n)) :
    ∃ σ : Fin (m * n) ≃ Fin (m * n),
      Matrix.reindex σ σ (Matrix.reindex finProdFinEquiv finProdFinEquiv
        ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ Matrix.sourceSkewForm hn)) =
        Matrix.sourceSkewForm h := by
  refine ⟨_, reindex_eq_sourceSkewForm h _ (skewRightPairing m hn) ?_⟩
  rintro ⟨q, b⟩ ⟨q', b'⟩
  obtain ⟨⟨c, p⟩, rfl⟩ : ∃ x, (finCongr (half_mul_right m hn)).symm (finProdFinEquiv x) = q :=
    ⟨finProdFinEquiv.symm (finCongr (half_mul_right m hn) q),
      by simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]⟩
  obtain ⟨⟨c', p'⟩, rfl⟩ : ∃ x, (finCongr (half_mul_right m hn)).symm (finProdFinEquiv x) = q' :=
    ⟨finProdFinEquiv.symm (finCongr (half_mul_right m hn) q'),
      by simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]⟩
  rw [skewRightPairing_apply, skewRightPairing_apply]
  simp [Matrix.sourceSkewForm, Matrix.kroneckerMap_apply, Matrix.one_apply, Prod.ext_iff]
  split_ifs <;> simp_all

/-- A unitary gate with `conj u = M u` and `det M = 1` has determinant `±1`
through every identification of its coordinate spaces. -/
theorem det_submatrix_eq_one_or_neg_one_of_map_star_eq_mul {m n : Type*} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] {U : Matrix m n ℂ} (hU : U.IsUnitaryBetween)
    {M : Matrix m m ℂ} (hM : M.det = 1) (hr : U.map (starRingEnd ℂ) = M * U) (e : m ≃ n) :
    (U.submatrix id e).det = 1 ∨ (U.submatrix id e).det = -1 := by
  have hA : U.submatrix id e ∈ Matrix.unitaryGroup m ℂ :=
    (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mp
      (by simpa [Matrix.reindex_apply] using hU.reindex _ (Equiv.refl _) e.symm)
  have hs : star (U.submatrix id e).det = (U.submatrix id e).det := by
    change starRingEnd ℂ _ = _
    rw [RingHom.map_det]
    change ((U.map (starRingEnd ℂ)).submatrix id e).det = _
    rw [hr, Matrix.det_mul_submatrix, hM, one_mul]
  have h1 := Unitary.mul_star_self_of_mem (Matrix.det_of_mem_unitary hA)
  rw [hs] at h1
  exact mul_self_eq_one_iff.mp h1

/-- The right-hand version: `conj v = v M` with `det M = 1`. -/
theorem det_submatrix_eq_one_or_neg_one_of_map_star_eq_mul_right {m n : Type*} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] {V : Matrix m n ℂ} (hV : V.IsUnitaryBetween)
    {M : Matrix n n ℂ} (hM : M.det = 1) (hr : V.map (starRingEnd ℂ) = V * M) (e : m ≃ n) :
    (V.submatrix id e).det = 1 ∨ (V.submatrix id e).det = -1 := by
  have hA : V.submatrix id e ∈ Matrix.unitaryGroup m ℂ :=
    (Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mp
      (by simpa [Matrix.reindex_apply] using hV.reindex _ (Equiv.refl _) e.symm)
  have hs : star (V.submatrix id e).det = (V.submatrix id e).det := by
    change starRingEnd ℂ _ = _
    rw [RingHom.map_det]
    change ((V.map (starRingEnd ℂ)).submatrix id e).det = _
    rw [hr, Matrix.det_submatrix_mul, hM, mul_one]
  have h1 := Unitary.mul_star_self_of_mem (Matrix.det_of_mem_unitary hA)
  rw [hs] at h1
  exact mul_self_eq_one_iff.mp h1

theorem det_sourceSkewForm {n : ℕ} (h : Even n) : (Matrix.sourceSkewForm h).det = 1 := by
  rw [Matrix.sourceSkewForm, Matrix.det_reindex_self, Matrix.det_kronecker]
  simp [Matrix.symplecticY, Matrix.det_fin_two]

theorem sourceSkewForm_mul_self {n : ℕ} (h : Even n) :
    Matrix.sourceSkewForm h * Matrix.sourceSkewForm h = -1 := by
  have hU := Matrix.mem_unitaryGroup_iff.mp (Matrix.sourceSkewForm_mem_unitaryGroup h)
  have hs : star (Matrix.sourceSkewForm h) = -Matrix.sourceSkewForm h := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose, Matrix.transpose_map]
    exact (congrArg Matrix.transpose (Matrix.map_star_sourceSkewForm h)).trans
      (Matrix.transpose_sourceSkewForm h)
  rw [hs, Matrix.mul_neg] at hU
  rw [← neg_neg (Matrix.sourceSkewForm h * _), hU]

/-- **Determinants of the doubled gates.** For gates of determinant `±1` and an
even physical dimension, `det u⁽²⁾ = 1` and `det v⁽²⁾` is the sign of the change
of identification. Source: arXiv:1703.09188, lines 1556--1560. -/
theorem det_doubled_of_sign {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ} (hd : Even d) (hℓr : r * ℓ = d * d)
    (e : Fin ℓ × Fin r ≃ Fin d × Fin d)
    (ht : (u.submatrix id e).det = 1 ∨ (u.submatrix id e).det = -1)
    (hs : (v.submatrix id (e.symm.trans (Equiv.prodComm _ _))).det = 1 ∨
      (v.submatrix id (e.symm.trans (Equiv.prodComm _ _))).det = -1) :
    ((doubledU u v).submatrix id (doubledIdent e)).det = 1 ∧
      ((doubledV v).submatrix id
        ((doubledIdent e).symm.trans (Equiv.prodComm (Fin (ℓ * d)) (Fin (d * r))))).det =
        (Equiv.Perm.sign (((doubledIdent e).symm.trans (Equiv.prodComm _ _)).trans
          (doubledShiftIdent (e.symm.trans (Equiv.prodComm _ _))).symm) : ℂ) := by
  have hev : ∀ s : ℂ, s = 1 ∨ s = -1 → s ^ (d * d) = 1 := by
    rintro s (rfl | rfl)
    · simp
    · exact (hd.mul_right d).neg_one_pow
  refine ⟨?_, ?_⟩
  · rw [det_doubledU_submatrix, hℓr, hev _ hs, one_mul, pow_mul]
    rcases ht with h | h <;> simp [h]
  · rw [det_submatrix_eq_sign_mul _ _ (doubledShiftIdent (e.symm.trans (Equiv.prodComm _ _))),
      det_doubledV_submatrix, hev _ hs, mul_one]

private theorem kronecker_reindex {m n m' n' : Type*} (σ : m ≃ m') (τ : n ≃ n')
    (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    Matrix.reindex (Equiv.prodCongr σ τ) (Equiv.prodCongr σ τ) (A ⊗ₖ B) =
      Matrix.reindex σ σ A ⊗ₖ Matrix.reindex τ τ B := by
  ext ⟨i, j⟩ ⟨i', j'⟩
  simp [Matrix.reindex_apply, Matrix.kroneckerMap_apply]

private theorem det_reindexRanks_u {P : Type*} {ℓ' r' : ℕ}
    (σ : Fin ℓ' ≃ Fin ℓ') (τ : Fin r' ≃ Fin r') (u : Matrix (Fin ℓ' × Fin r') P ℂ)
    (e : Fin ℓ' × Fin r' ≃ P) :
    ((Matrix.reindex (Equiv.prodCongr σ τ) (Equiv.refl _) u).submatrix id
      ((Equiv.prodCongr σ τ).symm.trans e)).det = (u.submatrix id e).det := by
  have : (Matrix.reindex (Equiv.prodCongr σ τ) (Equiv.refl _) u).submatrix id
      ((Equiv.prodCongr σ τ).symm.trans e) =
      (u.submatrix id e).submatrix (Equiv.prodCongr σ τ).symm (Equiv.prodCongr σ τ).symm := by
    ext i j
    simp [Matrix.reindex_apply]
  rw [this, Matrix.det_submatrix_equiv_self]

private theorem reindexRanks_v_submatrix {P : Type*} {ℓ' r' : ℕ}
    (σ : Fin ℓ' ≃ Fin ℓ') (τ : Fin r' ≃ Fin r') (v : Matrix P (Fin r' × Fin ℓ') ℂ)
    (e : Fin ℓ' × Fin r' ≃ P) :
    (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr τ σ) v).submatrix id
      (((Equiv.prodCongr σ τ).symm.trans e).symm.trans (Equiv.prodComm _ _)) =
      v.submatrix id (e.symm.trans (Equiv.prodComm _ _)) := by
  ext i j
  simp [Matrix.reindex_apply, Prod.map]
  rfl

/-- **Case I normal form.** Standard-form data in Case I can be gauged to real
gates (eq. `ortuv`). Source: arXiv:1703.09188, Proposition `corconj`,
lines 1098--1110 and 1124--1128. -/
theorem TwoSiteStandardFormData.exists_real_of_caseI {D : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (h : IsConjugationCaseI u v) :
    ∃ (U : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) (V : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ),
      Nonempty (TwoSiteStandardFormData W U V) ∧ U.map (starRingEnd ℂ) = U ∧
        V.map (starRingEnd ℂ) = V := by
  obtain ⟨x, y, hx, hy, hxT, hyT, hu, hv⟩ := h
  obtain ⟨a, b, ha, hb, hU, hV⟩ := Matrix.exists_orthogonal_gauge_of_symmetric hx hy hxT hyT hu hv
  exact ⟨_, _, ⟨S.ofGateGauges ⟨a, ha⟩ ⟨b, hb⟩⟩, hU, hV⟩

/-- **Case II normal form.** Standard-form data in Case II can be gauged to gates
in the symplectic normal form (eq. `sympuv`). Source: arXiv:1703.09188,
Proposition `corconj`, lines 1111--1120 and 1129--1149. -/
theorem TwoSiteStandardFormData.exists_symplectic_of_caseII {D : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (hℓ : Even ℓ) (hr : Even r)
    (h : IsConjugationCaseII u v) :
    ∃ (U : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) (V : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ),
      Nonempty (TwoSiteStandardFormData W U V) ∧
        U.map (starRingEnd ℂ) = (Matrix.sourceSkewForm hℓ ⊗ₖ Matrix.sourceSkewForm hr) * U ∧
        V.map (starRingEnd ℂ) = V * (Matrix.sourceSkewForm hr ⊗ₖ Matrix.sourceSkewForm hℓ) := by
  obtain ⟨x, y, hx, hy, hxT, hyT, hu, hv⟩ := h
  obtain ⟨_, _, a, b, ha, hb, hU, hV⟩ := Matrix.exists_symplectic_gauge_of_skew hx hy hxT hyT hu hv
  exact ⟨_, _, ⟨S.ofGateGauges ⟨a, ha⟩ ⟨b, hb⟩⟩, hU, hV⟩

/-- **Conjugation-invariant MPUs in the same case are equivalent.** Let
`𝒰₁, 𝒰₂` be MPUs in canonical form II whose two-site blocks have standard forms
of the same even ranks `ℓ, r`. If both standard forms are in Case I, or both in
Case II, of Proposition `corconj`, then `𝒰₁` and `𝒰₂` are equivalent under
conjugation symmetry: the blocks of four sites, with trivial ancillas, are
strictly equivalent under conjugation.

The corollary lies in the subsection "$r$ and $\ell$ are both even" (line 1464),
and the source states the parity explicitly at the comparable Theorem
`prop:conjsym-strict-equiv` (line 1482) and in the preceding odd subsection
(line 1401). The evenness of `ℓ, r` is therefore the standing hypothesis of the
corollary rather than an added one. The common ranks and physical dimension are
the convention of lines 1388--1398, and `ℓ r = d²` forces the ancilla
dimensions `p_a = p_b = 1`. Conjugation invariance of the MPUs follows from the
case hypothesis (Proposition `prop1conj`, "if" direction) and is not assumed
separately.

Source: arXiv:1703.09188, Corollary `cor:equiv-under-conjugation`,
lines 1548--1567, "if" direction, with the doubled gates of lines 1556--1564. -/
theorem equivalentUnderSymmetry_conjugation_of_same_case
    {𝒰₁ : MPOTensor d D₁} {𝒰₂ : MPOTensor d D₂}
    (h₁ : IsMPUCanonicalFormII 𝒰₁) (h₂ : IsMPUCanonicalFormII 𝒰₂)
    {u₁ u₂ : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v₁ v₂ : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S₁ : TwoSiteStandardFormData (blockTwo 𝒰₁) u₁ v₁)
    (S₂ : TwoSiteStandardFormData (blockTwo 𝒰₂) u₂ v₂)
    (hℓ : Even ℓ) (hr : Even r)
    (hcase : (IsConjugationCaseI u₁ v₁ ∧ IsConjugationCaseI u₂ v₂) ∨
      (IsConjugationCaseII u₁ v₁ ∧ IsConjugationCaseII u₂ v₂)) :
    EquivalentUnderSymmetry conjugationSymmetryFamily 𝒰₁ 𝒰₂ := by
  apply equivalentUnderSymmetry_conjugation_of_blockTensor_blockTwo h₁ h₂
  -- One identification of `ℂ^ℓ ⊗ ℂ^r` with `ℂ^d ⊗ ℂ^d`.
  have hcard : Fintype.card (Fin ℓ × Fin r) = Fintype.card (Fin d × Fin d) := by
    have h1 := Matrix.IsIsometry.card_le u₁ S₁.u_unitary.1
    have h2 := Matrix.IsCoisometry.card_le u₁ S₁.u_unitary.2
    omega
  have hℓr : r * ℓ = d * d := by
    simpa [Fintype.card_prod, Nat.mul_comm] using hcard
  have hd : Even d := by
    have h : Even (d * d) := hℓr ▸ hr.mul_right ℓ
    rcases Nat.even_mul.mp h with h | h <;> exact h
  let e : Fin ℓ × Fin r ≃ Fin d × Fin d := Fintype.equivOfCardEq hcard
  set f := e.symm.trans (Equiv.prodComm (Fin ℓ) (Fin r))
  set e' := doubledIdent e
  have hℓd : Even (ℓ * d) := hd.mul_left ℓ
  have hdr : Even (d * r) := hd.mul_right r
  rcases hcase with ⟨hc₁, hc₂⟩ | ⟨hc₁, hc₂⟩
  · -- Case I: real gates, and real doubled gates.
    obtain ⟨U₁, V₁, ⟨T₁⟩, hU₁, hV₁⟩ := S₁.exists_real_of_caseI hc₁
    obtain ⟨U₂, V₂, ⟨T₂⟩, hU₂, hV₂⟩ := S₂.exists_real_of_caseI hc₂
    obtain ⟨hu₁, hv₁⟩ := det_doubled_of_sign hd hℓr e
      (det_submatrix_eq_one_or_neg_one_of_real T₁.u_unitary hU₁ e)
      (det_submatrix_eq_one_or_neg_one_of_real T₁.v_unitary hV₁ f)
    obtain ⟨hu₂, hv₂⟩ := det_doubled_of_sign hd hℓr e
      (det_submatrix_eq_one_or_neg_one_of_real T₂.u_unitary hU₂ e)
      (det_submatrix_eq_one_or_neg_one_of_real T₂.v_unitary hV₂ f)
    exact strictlyEquivalentUnderSymmetry_conjugation_of_det_eq_of_even h₁.blockTwo h₂.blockTwo
      T₁.doubled T₂.doubled hℓd hdr
      (Or.inl ⟨by rw [doubledU_map_star, hU₁, hV₁], by rw [doubledV_map_star, hV₁],
        by rw [doubledU_map_star, hU₂, hV₂], by rw [doubledV_map_star, hV₂]⟩)
      e' (hu₁.trans hu₂.symm) (hv₁.trans hv₂.symm)
  · -- Case II: symplectic gates; the doubled gates are symplectic after a relabelling.
    obtain ⟨U₁, V₁, ⟨T₁⟩, hU₁, hV₁⟩ := S₁.exists_symplectic_of_caseII hℓ hr hc₁
    obtain ⟨U₂, V₂, ⟨T₂⟩, hU₂, hV₂⟩ := S₂.exists_symplectic_of_caseII hℓ hr hc₂
    have hdetS : (Matrix.sourceSkewForm hℓ ⊗ₖ Matrix.sourceSkewForm hr).det = 1 := by
      rw [Matrix.det_kronecker, det_sourceSkewForm, det_sourceSkewForm, one_pow, one_pow, one_mul]
    have hdetS' : (Matrix.sourceSkewForm hr ⊗ₖ Matrix.sourceSkewForm hℓ).det = 1 := by
      rw [Matrix.det_kronecker, det_sourceSkewForm, det_sourceSkewForm, one_pow, one_pow, one_mul]
    obtain ⟨hu₁, hv₁⟩ := det_doubled_of_sign hd hℓr e
      (det_submatrix_eq_one_or_neg_one_of_map_star_eq_mul T₁.u_unitary hdetS hU₁ e)
      (det_submatrix_eq_one_or_neg_one_of_map_star_eq_mul_right T₁.v_unitary hdetS' hV₁ f)
    obtain ⟨hu₂, hv₂⟩ := det_doubled_of_sign hd hℓr e
      (det_submatrix_eq_one_or_neg_one_of_map_star_eq_mul T₂.u_unitary hdetS hU₂ e)
      (det_submatrix_eq_one_or_neg_one_of_map_star_eq_mul_right T₂.v_unitary hdetS' hV₂ f)
    obtain ⟨σ, hσ⟩ := exists_reindex_sourceSkewForm_kronecker_one d hℓ hℓd
    obtain ⟨τ, hτ⟩ := exists_reindex_one_kronecker_sourceSkewForm d hr hdr
    have hsympU : ∀ {U : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
        {V : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ},
        U.map (starRingEnd ℂ) = (Matrix.sourceSkewForm hℓ ⊗ₖ Matrix.sourceSkewForm hr) * U →
        V.map (starRingEnd ℂ) = V * (Matrix.sourceSkewForm hr ⊗ₖ Matrix.sourceSkewForm hℓ) →
        (Matrix.reindex (Equiv.prodCongr σ τ) (Equiv.refl _) (doubledU U V)).map
            (starRingEnd ℂ) = (Matrix.sourceSkewForm hℓd ⊗ₖ Matrix.sourceSkewForm hdr) *
              Matrix.reindex (Equiv.prodCongr σ τ) (Equiv.refl _) (doubledU U V) ∧
        (Matrix.reindex (Equiv.refl _) (Equiv.prodCongr τ σ) (doubledV V)).map
            (starRingEnd ℂ) = Matrix.reindex (Equiv.refl _) (Equiv.prodCongr τ σ) (doubledV V) *
              (Matrix.sourceSkewForm hdr ⊗ₖ Matrix.sourceSkewForm hℓd) := by
      intro U V hU hV
      refine ⟨?_, ?_⟩
      · rw [map_star_reindex, doubledU_map_star_of_skew (sourceSkewForm_mul_self hℓ)
          (sourceSkewForm_mul_self hr) hU hV, ← reindex_mul_reindex _ (Equiv.prodCongr σ τ),
          kronecker_reindex, hσ, hτ]
      · rw [map_star_reindex, doubledV_map_star_of_skew hV,
          ← reindex_mul_reindex _ (Equiv.prodCongr τ σ), kronecker_reindex, hσ, hτ]
    obtain ⟨hsu₁, hsv₁⟩ := hsympU hU₁ hV₁
    obtain ⟨hsu₂, hsv₂⟩ := hsympU hU₂ hV₂
    exact strictlyEquivalentUnderSymmetry_conjugation_of_det_eq_of_even h₁.blockTwo h₂.blockTwo
      (T₁.doubled.reindexRanks σ τ) (T₂.doubled.reindexRanks σ τ) hℓd hdr
      (Or.inr ⟨hsu₁, hsv₁, hsu₂, hsv₂⟩) ((Equiv.prodCongr σ τ).symm.trans e')
      (by rw [det_reindexRanks_u, det_reindexRanks_u, hu₁, hu₂])
      (by rw [reindexRanks_v_submatrix, reindexRanks_v_submatrix, hv₁, hv₂])

end MPOTensor
