/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ConjugationGateGauge
import TNLean.Algebra.OrthogonalGroupJoined
import TNLean.MPS.MPU.ConjugationSymmetry
import TNLean.MPS.MPU.PhysicalMatrixBlocking
import TNLean.MPS.MPU.StandardFormConjugation
import TNLean.MPS.MPU.SymmetryPathCriterion

/-!
# Strict equivalence under conjugation

The "if" directions of Theorems `conjphs` and `prop:conjsym-strict-equiv` of
arXiv:1703.09188 (lines 1406--1446 and 1480--1546): two MPUs whose
standard-form gates have the same determinant invariants are strictly
equivalent under complex conjugation.

The determinant of `u v` reads the composite
`ℂ^r ⊗ ℂ^ℓ → ℂ^ℓ ⊗ ℂ^r` on `ℂ^ℓ ⊗ ℂ^r` through the swap of the two factors;
it is invariant under the gauge `u ↦ (x ⊗ y) u`, `v ↦ v (y† ⊗ x†)` of the
standard form, as computed at line 1416 of the source
(`det_gauge_mul_swap`).

## Main results

* `MPOTensor.strictlyEquivalentUnderSymmetry_conjugation_of_det_mul_eq`: the "if"
  direction of Theorem `conjphs`.
-/

open scoped Matrix Kronecker

namespace Matrix

variable {ℓ r : ℕ} {P : Type*} [Fintype P] [DecidableEq P]

omit [DecidableEq P] in
/-- The determinant of `u v` read on `ℂ^ℓ ⊗ ℂ^r` through the swap is invariant
under the gauge of the standard form. Source: arXiv:1703.09188, the remark after
Theorem `conjphs`, line 1416:
`det((x ⊗ y) u v (y† ⊗ x†)) = det(x ⊗ y) det(u v) det(y† ⊗ x†) = det(u v)`. -/
theorem det_gauge_mul_swap (u : Matrix (Fin ℓ × Fin r) P ℂ) (v : Matrix P (Fin r × Fin ℓ) ℂ)
    {x : Matrix (Fin ℓ) (Fin ℓ) ℂ} {y : Matrix (Fin r) (Fin r) ℂ}
    (hx : x ∈ unitaryGroup (Fin ℓ) ℂ) (hy : y ∈ unitaryGroup (Fin r) ℂ) :
    ((((x ⊗ₖ y) * u) * (v * (star y ⊗ₖ star x))).submatrix id
        (Equiv.prodComm (Fin ℓ) (Fin r))).det =
      ((u * v).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det := by
  set e := Equiv.prodComm (Fin ℓ) (Fin r)
  have hsplit : (((x ⊗ₖ y) * u) * (v * (star y ⊗ₖ star x))).submatrix id e =
      (x ⊗ₖ y) * (u * v).submatrix id e * (star y ⊗ₖ star x).submatrix e e := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc (x ⊗ₖ y) u v,
      ← Matrix.submatrix_mul_equiv _ _ id e e,
      ← Matrix.submatrix_mul_equiv (x ⊗ₖ y) (u * v) id (Equiv.refl _) e]
    simp
  have hx1 : star x * x = 1 := (Matrix.mem_unitaryGroup_iff'.mp hx)
  have hy1 : star y * y = 1 := (Matrix.mem_unitaryGroup_iff'.mp hy)
  rw [hsplit, det_mul, det_mul, det_submatrix_equiv_self, det_kronecker, det_kronecker]
  have hdx : (star x).det * x.det = 1 := by rw [← det_mul, hx1, det_one]
  have hdy : (star y).det * y.det = 1 := by rw [← det_mul, hy1, det_one]
  calc x.det ^ Fintype.card (Fin r) * y.det ^ Fintype.card (Fin ℓ) *
        ((u * v).submatrix id e).det *
        ((star y).det ^ Fintype.card (Fin ℓ) * (star x).det ^ Fintype.card (Fin r))
      = ((star x).det * x.det) ^ Fintype.card (Fin r) *
          ((star y).det * y.det) ^ Fintype.card (Fin ℓ) * ((u * v).submatrix id e).det := by
        ring
    _ = _ := by rw [hdx, hdy, one_pow, one_pow, one_mul, one_mul]

omit [Fintype P] [DecidableEq P] in
/-- Multiplying a gate on the left by a square matrix multiplies its
determinant, read through any identification of the coordinate spaces. -/
theorem det_mul_submatrix {m : Type*} [Fintype m] [DecidableEq m] (X : Matrix m m ℂ)
    (u : Matrix m P ℂ) (e : m ≃ P) :
    ((X * u).submatrix id e).det = X.det * (u.submatrix id e).det := by
  rw [← Matrix.submatrix_mul_equiv X u id (Equiv.refl _) e, det_mul]
  simp

/-- Multiplying a gate on the right by a square matrix multiplies its
determinant, read through any identification of the coordinate spaces. -/
theorem det_submatrix_mul {Q : Type*} [Fintype Q] [DecidableEq Q] (v : Matrix P Q ℂ)
    (Y : Matrix Q Q ℂ) (f : P ≃ Q) :
    ((v * Y).submatrix id f).det = (v.submatrix id f).det * Y.det := by
  rw [← Matrix.submatrix_mul_equiv v Y id f f, det_mul, det_submatrix_equiv_self]

/-- The determinant of `u v` read through the swap is the product of the
determinants of `u` and `v`, read through one identification `e`. -/
theorem det_mul_swap_eq (u : Matrix (Fin ℓ × Fin r) P ℂ) (v : Matrix P (Fin r × Fin ℓ) ℂ)
    (e : Fin ℓ × Fin r ≃ P) :
    ((u * v).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det =
      (u.submatrix id e).det *
        (v.submatrix id (e.symm.trans (Equiv.prodComm (Fin ℓ) (Fin r)))).det := by
  classical
  rw [← Matrix.submatrix_mul_equiv u v id e, det_mul]
  congr 1
  rw [← det_submatrix_equiv_self e]
  congr 1
  ext i j
  simp

/-- A unitary matrix with real entries has determinant `1` or `-1`. -/
theorem det_eq_one_or_neg_one_of_map_star_eq {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℂ} (hA : A ∈ unitaryGroup m ℂ) (hr : A.map (starRingEnd ℂ) = A) :
    A.det = 1 ∨ A.det = -1 := by
  have h := congrArg det (mem_unitaryGroup_iff'.mp hA)
  have hs : star A = Aᵀ := by
    ext i j
    simpa [star_apply] using congrFun (congrFun hr j) i
  rw [hs, det_mul, det_transpose, det_one, ← sq] at h
  exact sq_eq_one_iff.mp h

/-- The diagonal sign flip of the coordinate `i₀`, a real orthogonal matrix of
determinant `-1`. -/
def coordinateFlip {n : ℕ} (i₀ : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun i ↦ if i = i₀ then -1 else 1

theorem coordinateFlip_mem_unitaryGroup {n : ℕ} (i₀ : Fin n) :
    coordinateFlip i₀ ∈ unitaryGroup (Fin n) ℂ := by
  rw [mem_unitaryGroup_iff, coordinateFlip, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext i
  by_cases h : i = i₀ <;> simp [h]

theorem map_star_coordinateFlip {n : ℕ} (i₀ : Fin n) :
    (coordinateFlip i₀).map (starRingEnd ℂ) = coordinateFlip i₀ := by
  ext i j
  simp only [coordinateFlip, map_apply, diagonal_apply]
  split_ifs <;> simp

theorem star_coordinateFlip {n : ℕ} (i₀ : Fin n) :
    star (coordinateFlip i₀) = coordinateFlip i₀ := by
  rw [coordinateFlip, star_eq_conjTranspose, diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i = i₀ <;> simp [h]

theorem det_coordinateFlip {n : ℕ} (i₀ : Fin n) : (coordinateFlip i₀).det = -1 := by
  rw [coordinateFlip, det_diagonal, Finset.prod_ite_eq' Finset.univ i₀]
  simp

end Matrix

namespace Matrix

variable {ℓ r : ℕ} {P : Type*} [Fintype P] [DecidableEq P]

theorem map_star_mul_of_real {m n o : Type*} [Fintype n] {A : Matrix m n ℂ} {B : Matrix n o ℂ}
    (hA : A.map (starRingEnd ℂ) = A) (hB : B.map (starRingEnd ℂ) = B) :
    (A * B).map (starRingEnd ℂ) = A * B := by
  rw [Matrix.map_mul, hA, hB]

theorem map_star_kronecker_of_real {m n m' n' : Type*} {A : Matrix m n ℂ}
    {B : Matrix m' n' ℂ} (hA : A.map (starRingEnd ℂ) = A) (hB : B.map (starRingEnd ℂ) = B) :
    (A ⊗ₖ B).map (starRingEnd ℂ) = A ⊗ₖ B := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  have h₁ := congrFun (congrFun hA i) j
  have h₂ := congrFun (congrFun hB i') j'
  simp only [map_apply, kroneckerMap_apply] at h₁ h₂ ⊢
  rw [map_mul, h₁, h₂]

/-- **Sign change of the determinants by a real gauge.** If one of `ℓ, r` is
odd, a real orthogonal gauge `(x ⊗ y)` with `x` or `y` a coordinate flip
changes the signs of both determinants of real gates. Source: arXiv:1703.09188,
proof of Theorem `conjphs`, lines 1431--1437. -/
theorem exists_sign_flip_gauge (hℓ : 0 < ℓ) (hr : 0 < r) (hodd : Odd ℓ ∨ Odd r)
    (e : Fin ℓ × Fin r ≃ P) {u : Matrix (Fin ℓ × Fin r) P ℂ}
    {v : Matrix P (Fin r × Fin ℓ) ℂ}
    (hur : u.map (starRingEnd ℂ) = u) (hvr : v.map (starRingEnd ℂ) = v) :
    ∃ (x : unitaryGroup (Fin ℓ) ℂ) (y : unitaryGroup (Fin r) ℂ),
      (((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u).map
          (starRingEnd ℂ) = ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u ∧
      (v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ))).map
          (starRingEnd ℂ) =
        v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)) ∧
      ((((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u).submatrix
          id e).det = -(u.submatrix id e).det ∧
      ((v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ))).submatrix
          id (e.symm.trans (Equiv.prodComm (Fin ℓ) (Fin r)))).det =
        -(v.submatrix id (e.symm.trans (Equiv.prodComm (Fin ℓ) (Fin r)))).det := by
  have h1r : (1 : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have h1ℓ : (1 : Matrix (Fin ℓ) (Fin ℓ) ℂ).map (starRingEnd ℂ) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rcases hodd with hodd | hodd
  · let y : unitaryGroup (Fin r) ℂ := ⟨coordinateFlip ⟨0, hr⟩, coordinateFlip_mem_unitaryGroup _⟩
    refine ⟨1, y, ?_, ?_, ?_, ?_⟩
    · exact map_star_mul_of_real (map_star_kronecker_of_real h1ℓ (map_star_coordinateFlip _)) hur
    · simp only [y, OneMemClass.coe_one, star_one, star_coordinateFlip]
      exact map_star_mul_of_real hvr (map_star_kronecker_of_real (map_star_coordinateFlip _) h1ℓ)
    · rw [det_mul_submatrix, det_kronecker]
      simp [y, det_coordinateFlip, hodd.neg_one_pow]
    · rw [det_submatrix_mul, det_kronecker]
      simp [y, star_coordinateFlip, det_coordinateFlip, hodd.neg_one_pow]
  · let x : unitaryGroup (Fin ℓ) ℂ := ⟨coordinateFlip ⟨0, hℓ⟩, coordinateFlip_mem_unitaryGroup _⟩
    refine ⟨x, 1, ?_, ?_, ?_, ?_⟩
    · exact map_star_mul_of_real (map_star_kronecker_of_real (map_star_coordinateFlip _) h1r) hur
    · simp only [x, OneMemClass.coe_one, star_one, star_coordinateFlip]
      exact map_star_mul_of_real hvr (map_star_kronecker_of_real h1r (map_star_coordinateFlip _))
    · rw [det_mul_submatrix, det_kronecker]
      simp [x, det_coordinateFlip, hodd.neg_one_pow]
    · rw [det_submatrix_mul, det_kronecker]
      simp [x, star_coordinateFlip, det_coordinateFlip, hodd.neg_one_pow]

/-- **Symplectic gates with the same determinant are joined.** Let `A, B`
be unitary between `P` and `ℂ^ℓ ⊗ ℂ^r`, with `conj(A) = (Σ_ℓ ⊗ Σ_r) A` and
`conj(B) = (Σ_ℓ ⊗ Σ_r) B`. If their determinants agree through `e`, they are
joined by a path of such matrices. Write them as `(1 ⊗ R) Ã` and `(1 ⊗ R) B̃`
with `Ã, B̃` real (`exists_real_of_map_star_eq_sourceSkewForm_mul`) and join
`Ã` to `B̃` by real unitary gates. Source: arXiv:1703.09188, proof of Theorem
`prop:conjsym-strict-equiv`, "if" direction, Case II, lines 1540--1546. -/
theorem IsUnitaryBetween.joinedIn_symplectic_of_det_eq (hℓ : Even ℓ) (hr : Even r)
    (e : Fin ℓ × Fin r ≃ P) {A B : Matrix (Fin ℓ × Fin r) P ℂ}
    (hA : A.IsUnitaryBetween) (hB : B.IsUnitaryBetween)
    (hAc : A.map (starRingEnd ℂ) = (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * A)
    (hBc : B.map (starRingEnd ℂ) = (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * B)
    (hdet : (A.submatrix id e).det = (B.submatrix id e).det) :
    JoinedIn {X : Matrix (Fin ℓ × Fin r) P ℂ | X.IsUnitaryBetween ∧
      X.map (starRingEnd ℂ) = (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * X} A B := by
  set g := evenPairRegroupEquiv hℓ hr
  set K₂ := sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr
  obtain ⟨a, har, hAeq, hAu⟩ := exists_real_of_map_star_eq_sourceSkewForm_mul hℓ hr hAc
  obtain ⟨b, hbr, hBeq, hBu⟩ := exists_real_of_map_star_eq_sourceSkewForm_mul hℓ hr hBc
  set M := (1 : Matrix (Fin (ℓ / 2) × Fin (r / 2)) (Fin (ℓ / 2) × Fin (r / 2)) ℂ) ⊗ₖ
    symplecticOrthogonalR
  have hRu : symplecticOrthogonalR ∈ unitaryGroup (Fin 2 × Fin 2) ℂ := by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose]
    exact symplecticOrthogonalR_aux.1
  have hMu : M ∈ unitaryGroup _ ℂ := kronecker_mem_unitary (one_mem _) hRu
  have hMdet : M.det ≠ 0 := by
    intro h0
    have := congrArg det (mem_unitaryGroup_iff.mp hMu)
    rw [det_mul, h0, zero_mul, det_one] at this
    exact zero_ne_one this
  have ha := hAu hA
  have hb := hBu hB
  -- The determinants of the real parts agree.
  set e' := g.symm.trans e
  have hdetR : ∀ {X : Matrix (Fin ℓ × Fin r) P ℂ} {x : Matrix _ P ℂ},
      Matrix.reindex g (Equiv.refl P) X = M * x → (X.submatrix id e).det = M.det * (x.submatrix id e').det := by
    intro X x hX
    rw [← det_mul_submatrix, ← hX, ← det_submatrix_equiv_self g.symm]
    congr 1
  have hdet' : (a.submatrix id e').det = (b.submatrix id e').det :=
    mul_left_cancel₀ hMdet ((hdetR hAeq).symm.trans (hdet.trans (hdetR hBeq)))
  obtain ⟨γ, hγ⟩ := IsUnitaryBetween.joinedIn_real_of_det_eq e' ha hb har hbr hdet'
  -- Conjugating `M` multiplies it by the regrouped skew form.
  have hK : Matrix.reindex g g K₂ * Matrix.reindex g (Equiv.refl P) A =
      Matrix.reindex g (Equiv.refl P) (K₂ * A) := by
    simp only [Matrix.reindex_apply, submatrix_mul_equiv]
  have hM : M.map (starRingEnd ℂ) = Matrix.reindex g g K₂ * M := by
    have h1 : M.map (starRingEnd ℂ) * a = Matrix.reindex g g K₂ * M * a := by
      rw [Matrix.mul_assoc, ← hAeq, hK, ← hAc]
      conv_lhs => rw [← har]
      rw [← Matrix.map_mul, ← hAeq]
      ext i j
      simp [Matrix.reindex_apply, g]
    have h2 := congrArg (· * aᴴ) h1
    have ha2 : a * aᴴ = 1 := ha.2
    simp only [Matrix.mul_assoc, ha2, Matrix.mul_one] at h2
    exact h2
  let F : Matrix _ P ℂ → Matrix (Fin ℓ × Fin r) P ℂ := fun x ↦
    Matrix.reindex g.symm (Equiv.refl P) (M * x)
  have hF : Continuous F := (continuous_const.matrix_mul continuous_id).matrix_submatrix _ _
  have hFA : F a = A := by
    show Matrix.reindex g.symm (Equiv.refl P) (M * a) = A
    rw [← hAeq]
    ext i j
    simp [Matrix.reindex_apply, g]
  have hFB : F b = B := by
    show Matrix.reindex g.symm (Equiv.refl P) (M * b) = B
    rw [← hBeq]
    ext i j
    simp [Matrix.reindex_apply, g]
  refine ⟨(γ.map hF).cast hFA.symm hFB.symm, fun t ↦ ⟨?_, ?_⟩⟩
  · change (F (γ t)).IsUnitaryBetween
    exact (((isUnitaryBetween_iff_mem_unitaryGroup M).mpr hMu).mul _ _ (hγ t).1).reindex _ _ _
  · change (F (γ t)).map (starRingEnd ℂ) = K₂ * F (γ t)
    have hY : (M * γ t).map (starRingEnd ℂ) = Matrix.reindex g g K₂ * (M * γ t) := by
      rw [Matrix.map_mul, hM, (hγ t).2, Matrix.mul_assoc]
    have hmap : (F (γ t)).map (starRingEnd ℂ) =
        Matrix.reindex g.symm (Equiv.refl P) ((M * γ t).map (starRingEnd ℂ)) := by
      ext i j
      rfl
    rw [hmap, hY]
    simp only [F, Matrix.reindex_apply, Equiv.symm_symm, Equiv.refl_symm]
    rw [← submatrix_mul_equiv _ _ _ g]
    simp only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
    rfl

end Matrix

/-- Two factorizations `a b = a' b'` of one number into signs `a, a'` and
cofactors: if the signs differ, both factors change sign. -/
private theorem sign_change_of_mul_eq {a a' b b' : ℂ} (ha : a = 1 ∨ a = -1)
    (ha' : a' = 1 ∨ a' = -1) (h : a * b = a' * b') (hne : a ≠ a') : a' = -a ∧ b' = -b := by
  rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl
  · exact absurd rfl hne
  · exact ⟨rfl, by linear_combination h⟩
  · exact ⟨by norm_num, by linear_combination -h⟩
  · exact absurd rfl hne

namespace MPOTensor

variable {d D D₁ D₂ ℓ r : ℕ}

/-- **Real gates when one source rank is odd.** If the MPU generated by a
standard form is fixed by complex conjugation and one of the ranks `ℓ, r` is
odd, then a gauge `(x ⊗ y)` makes both gates real. Source: arXiv:1703.09188,
Proposition `corconj` (lines 1098--1149), Case I being the only case when `r`
or `ℓ` is odd (lines 1402--1403). -/
theorem TwoSiteStandardFormData.exists_real_gauge_of_conjugation {V : MPOTensor d D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData (blockTwo V) u v)
    (hc : ∀ N : ℕ, 0 < N → mpo (blockTwo V) N = (mpo (blockTwo V) N).map (starRingEnd ℂ))
    (hodd : Odd ℓ ∨ Odd r) :
    ∃ (x : Matrix.unitaryGroup (Fin ℓ) ℂ) (y : Matrix.unitaryGroup (Fin r) ℂ),
      (((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u).map
          (starRingEnd ℂ) = ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u ∧
      (v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ))).map
          (starRingEnd ℂ) =
        v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)) := by
  have : Nonempty (Fin ℓ) := ⟨⟨0, S.left_pos⟩⟩
  have : Nonempty (Fin r) := ⟨⟨0, S.right_pos⟩⟩
  obtain ⟨x, y, hu, hv⟩ := S.exists_gate_gauges_of_mpo_eq S.mapStar fun N hN ↦ by
    rw [mpo_map_star]
    exact hc N (by omega)
  have hv' : v.map (starRingEnd ℂ) =
      v * ((y : Matrix (Fin r) (Fin r) ℂ)ᴴ ⊗ₖ (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)ᴴ) := by
    simpa only [Matrix.star_eq_conjTranspose] using hv
  rcases Matrix.transpose_eq_self_or_transpose_eq_neg_of_gate_conjugation x.2 y.2
      S.u_unitary.2 hu with ⟨hxT, hyT⟩ | ⟨hxT, hyT⟩
  · obtain ⟨a, b, ha, hb, hu', hv''⟩ :=
      Matrix.exists_orthogonal_gauge_of_symmetric x.2 y.2 hxT hyT hu hv'
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hu', by simpa only [Matrix.star_eq_conjTranspose] using hv''⟩
  · obtain ⟨hℓ, hr, -⟩ := Matrix.exists_symplectic_gauge_of_skew x.2 y.2 hxT hyT hu hv'
    rcases hodd with h | h
    · exact absurd hℓ (Nat.not_even_iff_odd.mpr h)
    · exact absurd hr (Nat.not_even_iff_odd.mpr h)

/-- **Local sufficiency of `prop1conj` for gates.** If unitary gates satisfy
`conj(u) = (x ⊗ y) u` and `conj(v) = v (y† ⊗ x†)`, the MPU they generate is
fixed by complex conjugation at every positive length, after any physical
relabelling. Source: arXiv:1703.09188, Proposition `prop1conj`, "if" direction
(lines 1014--1027, proof at line 1030). -/
theorem isInvariantUnderSymmetry_conjugation_standardFormTensorOfGates {d' : ℕ}
    [NeZero d] [NeZero ℓ] [NeZero r] (e : Fin d' ≃ Fin (d * d))
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (hu : u.IsUnitaryBetween) (hv : v.IsUnitaryBetween)
    (x : Matrix.unitaryGroup (Fin ℓ) ℂ) (y : Matrix.unitaryGroup (Fin r) ℂ)
    (hcu : u.map (starRingEnd ℂ) =
      ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u)
    (hcv : v.map (starRingEnd ℂ) =
      v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ))) :
    IsInvariantUnderSymmetry (conjugationSymmetry d')
      (reindexPhysical e (standardFormTensorOfGates u v)) := by
  intro N hN
  change (mpo _ N).map (starRingEnd ℂ) = _
  let G := standardFormTensorOfGates u v
  let SG := standardFormTensorOfGatesData u v hu hv
  have SG' : TwoSiteStandardFormData (mapStar G) _ _ := hcu ▸ hcv ▸ SG.mapStar
  have hG : mpo (mapStar G) N = mpo G N := SG'.mpo_eq_of_same_gates (SG.ofGateGauges x y) N hN
  rw [← mpo_map_star]
  change mpo (reindexPhysical e (mapStar G)) N = _
  rw [mpo_reindexPhysical, mpo_reindexPhysical, hG]

/-- **Strict equivalence under conjugation from a conjugation-invariant gate
path.** If continuous families of unitary gates join standard-form gates of
the two-site blocks of `𝒰₁` and `𝒰₂`, and at every point satisfy the local
conjugation equations of `prop1conj`, then the two-site blocks are strictly
equivalent under conjugation. Source: arXiv:1703.09188, Lemma
`lem:equivalent-symmetry` (lines 1369--1376, "if" direction) with Proposition
`prop1conj` (lines 1014--1027), as combined in the proofs of Theorems
`conjphs` (line 1445) and `prop:conjsym-strict-equiv` (lines 1540--1546). -/
theorem strictlyEquivalentUnderSymmetry_conjugation_of_gate_path
    {𝒰₁ : MPOTensor d D₁} {𝒰₂ : MPOTensor d D₂}
    (h₁ : IsMPUCanonicalFormII 𝒰₁) (h₂ : IsMPUCanonicalFormII 𝒰₂)
    (u : unitInterval → Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : unitInterval → Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ)
    (hu : Continuous u) (hv : Continuous v)
    (hu' : ∀ p, (u p).IsUnitaryBetween) (hv' : ∀ p, (v p).IsUnitaryBetween)
    (S₁ : TwoSiteStandardFormData (blockTwo 𝒰₁) (u 0) (v 0))
    (S₂ : TwoSiteStandardFormData (blockTwo 𝒰₂) (u 1) (v 1))
    (hloc : ∀ p, ∃ (x : Matrix.unitaryGroup (Fin ℓ) ℂ) (y : Matrix.unitaryGroup (Fin r) ℂ),
      (u p).map (starRingEnd ℂ) =
          ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u p ∧
        (v p).map (starRingEnd ℂ) =
          v p * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ))) :
    StrictlyEquivalentUnderSymmetry (conjugationSymmetry (MPSTensor.blockPhysDim d 2))
      (blockTensor 𝒰₁ 2) (blockTensor 𝒰₂ 2) rfl := by
  have : NeZero d := h₁.neZero_phys
  have : NeZero ℓ := ⟨S₁.left_pos.ne'⟩
  have : NeZero r := ⟨S₁.right_pos.ne'⟩
  have h := strictlyEquivalentUnderSymmetry_blockTwo_of_gate_path
    (S := conjugationSymmetry d) (fun N hN ↦ hN) h₁ h₂ u v hu hv hu' hv' S₁ S₂
    (fun p ↦ by
      obtain ⟨x, y, hcu, hcv⟩ := hloc p
      rw [conjugationSymmetry_block (by norm_num)]
      exact isInvariantUnderSymmetry_conjugation_standardFormTensorOfGates _
        (hu' p) (hv' p) x y hcu hcv)
  rwa [conjugationSymmetry_block (by norm_num)] at h

/-- Real gates satisfy the local conjugation equations with `x = y = 1`. -/
private theorem exists_local_conjugation_of_real
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ} {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (hur : u.map (starRingEnd ℂ) = u) (hvr : v.map (starRingEnd ℂ) = v) :
    ∃ (x : Matrix.unitaryGroup (Fin ℓ) ℂ) (y : Matrix.unitaryGroup (Fin r) ℂ),
      u.map (starRingEnd ℂ) =
          ((x : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y : Matrix (Fin r) (Fin r) ℂ)) * u ∧
        v.map (starRingEnd ℂ) =
          v * (star (y : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x : Matrix (Fin ℓ) (Fin ℓ) ℂ)) :=
  ⟨1, 1, by simpa using hur, by simpa using hvr⟩

/-- **Conjugation symmetry when one source rank is odd, "if" direction.** Let
`𝒰₁, 𝒰₂` be simple tensors in canonical form II whose standard-form MPUs are
fixed by complex conjugation, with standard-form gates `u_i, v_i` of the same
ranks `ℓ, r`. If `r` or `ℓ` is odd and `det(u₁ v₁) = det(u₂ v₂)`, then the two
MPUs are strictly equivalent under conjugation. The standard-form chain is the
chain of two-site blocks, as in
`docs/paper-gaps/mpu_standard_form_canonical_convention.tex`; the determinant
of `u v` is read on `ℂ^ℓ ⊗ ℂ^r` through the swap, see
`Matrix.det_gauge_mul_swap`.

Source: arXiv:1703.09188, Theorem `conjphs`, lines 1406--1414, "if"
direction, proof at lines 1426--1446. -/
theorem strictlyEquivalentUnderSymmetry_conjugation_of_det_mul_eq
    {𝒰₁ : MPOTensor d D₁} {𝒰₂ : MPOTensor d D₂}
    (h₁ : IsMPUCanonicalFormII 𝒰₁) (h₂ : IsMPUCanonicalFormII 𝒰₂)
    (hc₁ : ∀ N : ℕ, 0 < N → mpo (blockTwo 𝒰₁) N = (mpo (blockTwo 𝒰₁) N).map (starRingEnd ℂ))
    (hc₂ : ∀ N : ℕ, 0 < N → mpo (blockTwo 𝒰₂) N = (mpo (blockTwo 𝒰₂) N).map (starRingEnd ℂ))
    {u₁ u₂ : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v₁ v₂ : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S₁ : TwoSiteStandardFormData (blockTwo 𝒰₁) u₁ v₁)
    (S₂ : TwoSiteStandardFormData (blockTwo 𝒰₂) u₂ v₂)
    (hodd : Odd ℓ ∨ Odd r)
    (hdet : ((u₁ * v₁).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det =
      ((u₂ * v₂).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det) :
    StrictlyEquivalentUnderSymmetry (conjugationSymmetry (MPSTensor.blockPhysDim d 2))
      (blockTensor 𝒰₁ 2) (blockTensor 𝒰₂ 2) rfl := by
  have : NeZero d := h₁.neZero_phys
  have : NeZero ℓ := ⟨S₁.left_pos.ne'⟩
  have : NeZero r := ⟨S₁.right_pos.ne'⟩
  -- Real gates for both standard forms (Case I of `corconj`).
  obtain ⟨x₁, y₁, hU₁, hV₁⟩ := S₁.exists_real_gauge_of_conjugation hc₁ hodd
  obtain ⟨x₂, y₂, hU₂, hV₂⟩ := S₂.exists_real_gauge_of_conjugation hc₂ hodd
  set U₁ := ((x₁ : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y₁ : Matrix (Fin r) (Fin r) ℂ)) * u₁
  set V₁ := v₁ * (star (y₁ : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x₁ : Matrix (Fin ℓ) (Fin ℓ) ℂ))
  set U₂ := ((x₂ : Matrix (Fin ℓ) (Fin ℓ) ℂ) ⊗ₖ (y₂ : Matrix (Fin r) (Fin r) ℂ)) * u₂
  set V₂ := v₂ * (star (y₂ : Matrix (Fin r) (Fin r) ℂ) ⊗ₖ star (x₂ : Matrix (Fin ℓ) (Fin ℓ) ℂ))
  let T₁ := S₁.ofGateGauges x₁ y₁
  let T₂ := S₂.ofGateGauges x₂ y₂
  have hdetUV : ((U₁ * V₁).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det =
      ((U₂ * V₂).submatrix id (Equiv.prodComm (Fin ℓ) (Fin r))).det := by
    rw [Matrix.det_gauge_mul_swap _ _ x₁.2 y₁.2, Matrix.det_gauge_mul_swap _ _ x₂.2 y₂.2, hdet]
  -- One identification of `ℂ^ℓ ⊗ ℂ^r` with `ℂ^d ⊗ ℂ^d`.
  have hcard : Fintype.card (Fin ℓ × Fin r) = Fintype.card (Fin d × Fin d) := by
    have h1 := Matrix.IsIsometry.card_le u₁ S₁.u_unitary.1
    have h2 := Matrix.IsCoisometry.card_le u₁ S₁.u_unitary.2
    omega
  let e : Fin ℓ × Fin r ≃ Fin d × Fin d := Fintype.equivOfCardEq hcard
  set f := e.symm.trans (Equiv.prodComm (Fin ℓ) (Fin r)) with hf
  -- The determinants of real unitary gates are signs.
  have hsignU : ∀ {U : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}, U.IsUnitaryBetween →
      U.map (starRingEnd ℂ) = U → (U.submatrix id e).det = 1 ∨ (U.submatrix id e).det = -1 :=
    fun hU hUr ↦ Matrix.det_eq_one_or_neg_one_of_map_star_eq
      ((Matrix.isUnitaryBetween_iff_mem_unitaryGroup _).mp
        (by simpa [Matrix.reindex_apply] using hU.reindex _ (Equiv.refl _) e.symm))
      (by ext i j; exact congrFun (congrFun hUr i) (e j))
  rw [Matrix.det_mul_swap_eq _ _ e, Matrix.det_mul_swap_eq _ _ e, ← hf] at hdetUV
  -- Choose the gauge of the second standard form with the same two determinants.
  obtain ⟨U₂', V₂', T₂', hU₂', hV₂', hdU, hdV⟩ :
      ∃ (U₂' : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
        (V₂' : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ),
        Nonempty (TwoSiteStandardFormData (blockTwo 𝒰₂) U₂' V₂') ∧
        U₂'.map (starRingEnd ℂ) = U₂' ∧ V₂'.map (starRingEnd ℂ) = V₂' ∧
        (U₁.submatrix id e).det = (U₂'.submatrix id e).det ∧
        (V₁.submatrix id f).det = (V₂'.submatrix id f).det := by
    have hs₁ := hsignU T₁.u_unitary hU₁
    have hs₂ := hsignU T₂.u_unitary hU₂
    by_cases hsame : (U₁.submatrix id e).det = (U₂.submatrix id e).det
    · refine ⟨U₂, V₂, ⟨T₂⟩, hU₂, hV₂, hsame, ?_⟩
      have hne : (U₁.submatrix id e).det ≠ 0 := by
        rcases hs₁ with h | h <;> rw [h] <;> norm_num
      rw [← hsame] at hdetUV
      exact mul_left_cancel₀ hne hdetUV
    · obtain ⟨hsU, hsV⟩ := sign_change_of_mul_eq hs₁ hs₂ hdetUV hsame
      obtain ⟨x, y, hU, hV, hdu, hdv⟩ := Matrix.exists_sign_flip_gauge
        S₁.left_pos S₁.right_pos hodd e hU₂ hV₂
      refine ⟨_, _, ⟨T₂.ofGateGauges x y⟩, hU, hV, ?_, ?_⟩
      · rw [hdu, hsU, neg_neg]
      · rw [hf, hdv, ← hf, hsV, neg_neg]
  obtain ⟨T₂'⟩ := T₂'
  -- Real paths of unitary gates with these determinants.
  obtain ⟨γu, hγu⟩ := Matrix.IsUnitaryBetween.joinedIn_real_of_det_eq e T₁.u_unitary
    T₂'.u_unitary hU₁ hU₂' hdU
  obtain ⟨γv, hγv⟩ := Matrix.IsUnitaryBetween.joinedIn_real_of_det_eq f T₁.v_unitary
    T₂'.v_unitary hV₁ hV₂' hdV
  exact strictlyEquivalentUnderSymmetry_conjugation_of_gate_path h₁ h₂ γu γv γu.continuous
    γv.continuous (fun p ↦ (hγu p).1) (fun p ↦ (hγv p).1)
    (by rw [γu.source, γv.source]; exact T₁) (by rw [γu.target, γv.target]; exact T₂')
    (fun p ↦ exists_local_conjugation_of_real (hγu p).2 (hγv p).2)

end MPOTensor
