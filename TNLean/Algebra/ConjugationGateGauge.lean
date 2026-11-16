/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SkewUnitaryNormalForm
import TNLean.Algebra.SymplecticOrthogonalFour
import TNLean.Algebra.UnitaryConjugationTransposeSign
import QICLean.Algebra.MatrixReindexUnitary
import QICLean.Algebra.SkewSymmetricMatrix

/-!
# Orthogonal and symplectic gauges of conjugation-covariant gates

Let `u : ℂ^P → ℂ^L ⊗ ℂ^R` and `v : ℂ^R ⊗ ℂ^L → ℂ^P` satisfy
`conj(u) = (x ⊗ y) u` and `conj(v) = v (y† ⊗ x†)` for unitaries `x, y`.
If `x = Uᵀ Λ U` and `y = Vᵀ Λ' V` with `U, V` unitary, then the gauged gates
`u' = (U ⊗ V) u` and `v' = v (V† ⊗ U†)` satisfy
`conj(u') = (Λ ⊗ Λ') u'` and `conj(v') = v' (Λ'† ⊗ Λ†)`. For symmetric `x, y`
one takes `Λ = 1`; for skew-symmetric `x, y` one takes the source's form
`Σ_n = 1_{n/2} ⊗ Y`, defined here as `Matrix.sourceSkewForm`.

Conversely, if `u'` is a coisometry and `u'' = (a ⊗ b) u'` satisfies the same
covariance as `u'`, then after a phase `a, b` themselves intertwine
conjugation with `Λ, Λ'`: they are orthogonal for `Λ = 1` and symplectic
for `Λ = Σ`.

Finally, in the symplectic case the explicit matrix `R` of the source
transforms `u'` and `v'` into real gates.

## Main statements

* `Matrix.map_star_gaugeLeft_eq_of_congruence`,
  `Matrix.map_star_gaugeRight_eq_of_congruence`: the gauge computation.
* `Matrix.exists_orthogonal_gauge_of_symmetric`,
  `Matrix.exists_symplectic_gauge_of_skew`: Case I and Case II existence.
* `Matrix.exists_orthogonal_factors_of_kronecker_mul`,
  `Matrix.exists_symplectic_factors_of_kronecker_mul`: Case I and Case II
  uniqueness.
* `Matrix.exists_real_of_map_star_eq_sourceSkewForm_mul`,
  `Matrix.exists_real_of_map_star_eq_mul_sourceSkewForm`: the reduction
  `u' = (1 ⊗ R) uR`, `v' = vR (1 ⊗ R)` with `uR, vR` real.

## References

* Cirac, Pérez-García, Schuch and Verstraete, arXiv:1703.09188,
  Proposition `corconj` (lines 1098--1163) and Corollary
  `cor:sympl-to-orthogonal` (lines 1168--1185).

**Local fix (Case II uniqueness of `v`):** the source prints
`v'' = v' (S_rᵀ ⊗ S_ℓᵀ)` in Case II (line 1124). The Fundamental Theorem gives
`v'' = v' (b† ⊗ a†)` (line 1152), and for a unitary symplectic `S` one has
`S† ≠ Sᵀ` in general, so `Matrix.exists_symplectic_factors_of_kronecker_mul`
states the relation with `S_r† ⊗ S_ℓ†`. Documented in
`docs/paper-gaps/mpu_conjugation_symplectic_uniqueness_transpose.tex`.
-/

open scoped Matrix Kronecker

namespace Matrix

section Gauge

variable {L R P : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

theorem map_star_kronecker {m n m' n' : Type*} (A : Matrix m n ℂ) (B : Matrix m' n' ℂ) :
    (A ⊗ₖ B).map (starRingEnd ℂ) = A.map (starRingEnd ℂ) ⊗ₖ B.map (starRingEnd ℂ) := by
  ext i j
  simp [kroneckerMap_apply]

theorem conjTranspose_transpose_eq_map_star {m n : Type*} (U : Matrix m n ℂ) :
    (Uᵀ)ᴴ = U.map (starRingEnd ℂ) := by
  ext i j
  simp [conjTranspose_apply]

theorem map_star_conjTranspose_eq_transpose {m n : Type*} (U : Matrix m n ℂ) :
    Uᴴ.map (starRingEnd ℂ) = Uᵀ := by
  ext i j
  simp [conjTranspose_apply]

/-- For a unitary `U`, `conj(U) Uᵀ = 1`. -/
theorem map_star_mul_transpose_of_mem_unitaryGroup {n : Type*} [Fintype n] [DecidableEq n]
    {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) :
    U.map (starRingEnd ℂ) * Uᵀ = 1 := by
  have h := congrArg (fun M ↦ M.map (starRingEnd ℂ)) (mem_unitaryGroup_iff.mp hU)
  simpa [Matrix.map_mul, Matrix.star_eq_conjTranspose, map_star_conjTranspose_eq_transpose]
    using h

/-- **Gauge of the gate `u`.** If `conj(u) = (x ⊗ y) u`, `x = Uᵀ Λ U` and
`y = Vᵀ Λ' V` with `U, V` unitary, then `u' = (U ⊗ V) u` satisfies
`conj(u') = (Λ ⊗ Λ') u'`. This is the computation
`\bar{u'} = (Λ_ℓ ⊗ Λ_r) u'` in the proof of arXiv:1703.09188, `corconj`,
lines 1142--1149. -/
theorem map_star_gaugeLeft_eq_of_congruence {u : Matrix (L × R) P ℂ}
    {x U Λ : Matrix L L ℂ} {y V Λ' : Matrix R R ℂ}
    (hU : U ∈ unitaryGroup L ℂ) (hV : V ∈ unitaryGroup R ℂ)
    (hx : x = Uᵀ * Λ * U) (hy : y = Vᵀ * Λ' * V)
    (hu : u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u) :
    ((U ⊗ₖ V) * u).map (starRingEnd ℂ) = (Λ ⊗ₖ Λ') * ((U ⊗ₖ V) * u) := by
  rw [Matrix.map_mul, map_star_kronecker, hu, ← Matrix.mul_assoc, ← mul_kronecker_mul,
    hx, hy]
  have hU' : U.map (starRingEnd ℂ) * (Uᵀ * Λ * U) = Λ * U := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, map_star_mul_transpose_of_mem_unitaryGroup hU,
      Matrix.one_mul]
  have hV' : V.map (starRingEnd ℂ) * (Vᵀ * Λ' * V) = Λ' * V := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, map_star_mul_transpose_of_mem_unitaryGroup hV,
      Matrix.one_mul]
  rw [hU', hV', mul_kronecker_mul, Matrix.mul_assoc]

/-- **Gauge of the gate `v`.** If `conj(v) = v (y† ⊗ x†)`, `x = Uᵀ Λ U` and
`y = Vᵀ Λ' V` with `U, V` unitary, then `v' = v (V† ⊗ U†)` satisfies
`conj(v') = v' (Λ'† ⊗ Λ†)`. This is the computation
`\bar{v'} = v' (Λ_r^T ⊗ Λ_ℓ^T)` in the proof of arXiv:1703.09188, `corconj`,
lines 1142--1149, before the real forms `Λ` are inserted. -/
theorem map_star_gaugeRight_eq_of_congruence {v : Matrix P (R × L) ℂ}
    {x U Λ : Matrix L L ℂ} {y V Λ' : Matrix R R ℂ}
    (hU : U ∈ unitaryGroup L ℂ) (hV : V ∈ unitaryGroup R ℂ)
    (hx : x = Uᵀ * Λ * U) (hy : y = Vᵀ * Λ' * V)
    (hv : v.map (starRingEnd ℂ) = v * (yᴴ ⊗ₖ xᴴ)) :
    (v * (Vᴴ ⊗ₖ Uᴴ)).map (starRingEnd ℂ) = (v * (Vᴴ ⊗ₖ Uᴴ)) * (Λ'ᴴ ⊗ₖ Λᴴ) := by
  rw [Matrix.map_mul, map_star_kronecker, hv, map_star_conjTranspose_eq_transpose,
    map_star_conjTranspose_eq_transpose, Matrix.mul_assoc, ← mul_kronecker_mul, hx, hy]
  have hU' : (Uᵀ * Λ * U)ᴴ * Uᵀ = Uᴴ * Λᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_transpose_eq_map_star]
    simp only [Matrix.mul_assoc, map_star_mul_transpose_of_mem_unitaryGroup hU, Matrix.mul_one]
  have hV' : (Vᵀ * Λ' * V)ᴴ * Vᵀ = Vᴴ * Λ'ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_transpose_eq_map_star]
    simp only [Matrix.mul_assoc, map_star_mul_transpose_of_mem_unitaryGroup hV, Matrix.mul_one]
  rw [hU', hV', mul_kronecker_mul, Matrix.mul_assoc]

end Gauge

section SkewForm

/-- The coordinate identification `Fin (n/2) × Fin 2 ≃ Fin n` of an even
dimension, ordered as the Kronecker product `1_{n/2} ⊗ Y`. -/
def evenPairEquiv {n : ℕ} (h : Even n) : Fin (n / 2) × Fin 2 ≃ Fin n :=
  (interleavedSkewFinEquiv (n / 2)).trans (finCongr (Nat.two_mul_div_two_of_even h))

/-- The source's skew form `Σ_n = 1_{n/2} ⊗ Y` on an even dimension `n`, with
`Y = !![0, 1; -1, 0]`. Source: arXiv:1703.09188, `corconj`, eq. `sympuv`,
lines 1113--1120. -/
noncomputable def sourceSkewForm {n : ℕ} (h : Even n) : Matrix (Fin n) (Fin n) ℂ :=
  reindex (evenPairEquiv h) (evenPairEquiv h) ((1 : Matrix (Fin (n / 2)) (Fin (n / 2)) ℂ) ⊗ₖ
    symplecticY)

theorem sourceSkewForm_eq_reindex_complexInterleavedSkewFormFin {n : ℕ} (h : Even n) :
    sourceSkewForm h = reindex (finCongr (Nat.two_mul_div_two_of_even h))
      (finCongr (Nat.two_mul_div_two_of_even h)) (complexInterleavedSkewFormFin (n / 2)) := by
  ext i j
  simp only [sourceSkewForm, complexInterleavedSkewFormFin, interleavedSkewFormFin,
    interleavedSkewForm, evenPairEquiv, reindex_apply, submatrix_apply, map_apply,
    Equiv.symm_trans_apply]
  rcases (interleavedSkewFinEquiv (n / 2)).symm ((finCongr _).symm i) with ⟨a, b⟩
  rcases (interleavedSkewFinEquiv (n / 2)).symm ((finCongr _).symm j) with ⟨c, e⟩
  fin_cases b <;> fin_cases e <;>
    simp [kroneckerMap_apply, one_apply, symplecticY, apply_ite Complex.ofReal]

/-- The source skew form is real. -/
theorem map_star_sourceSkewForm {n : ℕ} (h : Even n) :
    (sourceSkewForm h).map (starRingEnd ℂ) = sourceSkewForm h := by
  ext i j
  simp only [sourceSkewForm, reindex_apply, submatrix_apply, map_apply, kroneckerMap_apply,
    one_apply]
  rcases (evenPairEquiv h).symm i with ⟨a, b⟩
  rcases (evenPairEquiv h).symm j with ⟨c, e⟩
  fin_cases b <;> fin_cases e <;> split_ifs <;> simp [symplecticY]

/-- The source skew form is skew-symmetric. -/
theorem transpose_sourceSkewForm {n : ℕ} (h : Even n) :
    (sourceSkewForm h)ᵀ = -sourceSkewForm h := by
  ext i j
  simp only [sourceSkewForm, transpose_apply, reindex_apply, submatrix_apply, neg_apply,
    kroneckerMap_apply, one_apply]
  rcases (evenPairEquiv h).symm i with ⟨a, b⟩
  rcases (evenPairEquiv h).symm j with ⟨c, e⟩
  by_cases hac : a = c
  · subst hac
    fin_cases b <;> fin_cases e <;> simp [symplecticY]
  · simp [hac, Ne.symm hac]

/-- The source skew form is unitary. -/
theorem sourceSkewForm_mem_unitaryGroup {n : ℕ} (h : Even n) :
    sourceSkewForm h ∈ unitaryGroup (Fin n) ℂ := by
  have hY : symplecticY ∈ unitaryGroup (Fin 2) ℂ := by
    rw [mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [symplecticY, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
  have hK : (1 : Matrix (Fin (n / 2)) (Fin (n / 2)) ℂ) ⊗ₖ symplecticY ∈
      unitaryGroup (Fin (n / 2) × Fin 2) ℂ :=
    kronecker_mem_unitary (one_mem _) hY
  exact reindex_mem_unitaryGroup _ _ hK

/-- Transport of the source skew form along an equality of even dimensions. -/
theorem reindex_finCongr_sourceSkewForm {n n' : ℕ} (hn : Even n) (h : n = n') :
    reindex (finCongr h) (finCongr h) (sourceSkewForm hn) = sourceSkewForm (h ▸ hn) := by
  subst h
  ext i j
  simp [reindex_apply]

/-- **Skew-symmetric unitaries in the source normal form.** Every
skew-symmetric unitary `x` on an even dimension `n` is `Uᵀ Σ_n U` with `U`
unitary. This is the first step of the proof of arXiv:1703.09188, `corconj`,
lines 1129--1140, stated with the source's `Σ_n = 1_{n/2} ⊗ Y`. -/
theorem exists_unitary_congruence_sourceSkewForm {n : ℕ} (h : Even n)
    (x : Matrix (Fin n) (Fin n) ℂ) (hx : x ∈ unitaryGroup (Fin n) ℂ) (hskew : xᵀ = -x) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ,
      U ∈ unitaryGroup (Fin n) ℂ ∧ x = Uᵀ * sourceSkewForm h * U := by
  let e := finCongr (Nat.two_mul_div_two_of_even h)
  let x' := reindex e.symm e.symm x
  have hx' : x' ∈ unitaryGroup (Fin (2 * (n / 2))) ℂ := reindex_mem_unitaryGroup _ _ hx
  have hskew' : x'ᵀ = -x' := by
    simp only [x', transpose_reindex, hskew]
    ext i j
    simp [reindex_apply]
  obtain ⟨U', hU', hfac⟩ := exists_unitary_congruence_interleavedSkewForm (n / 2) x' hx' hskew'
  refine ⟨reindex e e U', reindex_mem_unitaryGroup _ _ hU', ?_⟩
  have hx_eq : x = reindex e e x' := by
    ext i j
    simp [x', reindex_apply]
  rw [hx_eq, hfac, sourceSkewForm_eq_reindex_complexInterleavedSkewFormFin h,
    transpose_reindex]
  simp only [e, reindex_apply, submatrix_mul_equiv]

end SkewForm

section Existence

variable {ℓ r : ℕ} {P : Type*}

/-- **Case I existence.** For symmetric unitaries `x, y`, there are unitary
gauges `U, V` such that `(U ⊗ V) u` and `v (V† ⊗ U†)` are real.
Source: arXiv:1703.09188, `corconj`, eq. `ortuv` (lines 1104--1112) and the
proof at lines 1129--1149, with `x = Sᵀ S` from
`lemma:conjclass-normalform-continuous`. -/
theorem exists_orthogonal_gauge_of_symmetric
    {u : Matrix (Fin ℓ × Fin r) P ℂ} {v : Matrix P (Fin r × Fin ℓ) ℂ}
    {x : Matrix (Fin ℓ) (Fin ℓ) ℂ} {y : Matrix (Fin r) (Fin r) ℂ}
    (hx : x ∈ unitaryGroup (Fin ℓ) ℂ) (hy : y ∈ unitaryGroup (Fin r) ℂ)
    (hxT : xᵀ = x) (hyT : yᵀ = y)
    (hu : u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u)
    (hv : v.map (starRingEnd ℂ) = v * (yᴴ ⊗ₖ xᴴ)) :
    ∃ (U : Matrix (Fin ℓ) (Fin ℓ) ℂ) (V : Matrix (Fin r) (Fin r) ℂ),
      U ∈ unitaryGroup (Fin ℓ) ℂ ∧ V ∈ unitaryGroup (Fin r) ℂ ∧
      ((U ⊗ₖ V) * u).map (starRingEnd ℂ) = (U ⊗ₖ V) * u ∧
      (v * (Vᴴ ⊗ₖ Uᴴ)).map (starRingEnd ℂ) = v * (Vᴴ ⊗ₖ Uᴴ) := by
  obtain ⟨U, -, hU, hxU⟩ := exists_symmetric_unitary_squareRoot x hx hxT
  obtain ⟨V, -, hV, hyV⟩ := exists_symmetric_unitary_squareRoot y hy hyT
  have hx' : x = Uᵀ * 1 * U := by rw [Matrix.mul_one]; exact hxU
  have hy' : y = Vᵀ * 1 * V := by rw [Matrix.mul_one]; exact hyV
  refine ⟨U, V, hU, hV, ?_, ?_⟩
  · simpa [one_kronecker_one] using map_star_gaugeLeft_eq_of_congruence hU hV hx' hy' hu
  · simpa [one_kronecker_one] using map_star_gaugeRight_eq_of_congruence hU hV hx' hy' hv

/-- **Case II existence.** For skew-symmetric unitaries `x, y`, both
dimensions are even and there are unitary gauges `U, V` such that
`conj((U ⊗ V) u) = (Σ_ℓ ⊗ Σ_r) (U ⊗ V) u` and
`conj(v (V† ⊗ U†)) = v (V† ⊗ U†) (Σ_r ⊗ Σ_ℓ)`.
Source: arXiv:1703.09188, `corconj`, eq. `sympuv` (lines 1113--1125) and the
proof at lines 1129--1149. -/
theorem exists_symplectic_gauge_of_skew
    {u : Matrix (Fin ℓ × Fin r) P ℂ} {v : Matrix P (Fin r × Fin ℓ) ℂ}
    {x : Matrix (Fin ℓ) (Fin ℓ) ℂ} {y : Matrix (Fin r) (Fin r) ℂ}
    (hx : x ∈ unitaryGroup (Fin ℓ) ℂ) (hy : y ∈ unitaryGroup (Fin r) ℂ)
    (hxT : xᵀ = -x) (hyT : yᵀ = -y)
    (hu : u.map (starRingEnd ℂ) = (x ⊗ₖ y) * u)
    (hv : v.map (starRingEnd ℂ) = v * (yᴴ ⊗ₖ xᴴ)) :
    ∃ (hℓ : Even ℓ) (hr : Even r) (U : Matrix (Fin ℓ) (Fin ℓ) ℂ)
      (V : Matrix (Fin r) (Fin r) ℂ),
      U ∈ unitaryGroup (Fin ℓ) ℂ ∧ V ∈ unitaryGroup (Fin r) ℂ ∧
      ((U ⊗ₖ V) * u).map (starRingEnd ℂ) =
        (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * ((U ⊗ₖ V) * u) ∧
      (v * (Vᴴ ⊗ₖ Uᴴ)).map (starRingEnd ℂ) =
        (v * (Vᴴ ⊗ₖ Uᴴ)) * (sourceSkewForm hr ⊗ₖ sourceSkewForm hℓ) := by
  have hℓ : Even ℓ := UnitaryGroup.even_dimension_of_transpose_eq_neg (R := ℂ) ⟨x, hx⟩ hxT
  have hr : Even r := UnitaryGroup.even_dimension_of_transpose_eq_neg (R := ℂ) ⟨y, hy⟩ hyT
  obtain ⟨U, hU, hxU⟩ := exists_unitary_congruence_sourceSkewForm hℓ x hx hxT
  obtain ⟨V, hV, hyV⟩ := exists_unitary_congruence_sourceSkewForm hr y hy hyT
  refine ⟨hℓ, hr, U, V, hU, hV, map_star_gaugeLeft_eq_of_congruence hU hV hxU hyV hu, ?_⟩
  have hSig {n : ℕ} (hn : Even n) : (sourceSkewForm hn)ᴴ = -sourceSkewForm hn := by
    rw [conjTranspose, transpose_sourceSkewForm]
    ext i j
    have := congrFun (congrFun (map_star_sourceSkewForm hn) i) j
    simpa using this
  rw [map_star_gaugeRight_eq_of_congruence hU hV hxU hyV hv, hSig, hSig]
  congr 1
  ext i j
  simp [kroneckerMap_apply]

end Existence

section Uniqueness

variable {L R P : Type*} [Fintype L] [Fintype R] [Fintype P] [DecidableEq L] [DecidableEq R]

/-- A unitary scalar matrix on a nonempty index type has a scalar of norm one. -/
private theorem norm_eq_one_of_smul_one_mem_unitaryGroup [Nonempty L] {c : ℂ}
    (hc : c • (1 : Matrix L L ℂ) ∈ unitaryGroup L ℂ) : ‖c‖ = 1 := by
  obtain ⟨i⟩ := ‹Nonempty L›
  have h := congrFun (congrFun (mem_unitaryGroup_iff'.mp hc) i) i
  simp only [Matrix.star_eq_conjTranspose, conjTranspose_smul, conjTranspose_one,
    smul_mul_smul_comm, smul_apply, one_apply_eq, smul_eq_mul,
    mul_one] at h
  have h' : (Complex.normSq c : ℂ) = 1 := by
    rw [← Complex.mul_conj, mul_comm]
    exact h
  have h'' : ‖c‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact_mod_cast h'
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).mp h''

/-- **Common phase of a gauge preserving conjugation covariance.** Let `u` be
a coisometry with `conj(u) = (Λ ⊗ Λ') u`, and let `a, b` be unitaries with
`conj((a ⊗ b) u) = (Λ ⊗ Λ') (a ⊗ b) u`, where `Λ, Λ'` are unitary. Then there
is a phase `w` with `conj(w a) Λ = Λ (w a)` and
`conj(w⁻¹ b) Λ' = Λ' (w⁻¹ b)`. This is the phase choice in the uniqueness part
of the proof of arXiv:1703.09188, `corconj`, lines 1151--1163. -/
theorem exists_phase_of_kronecker_mul_map_star_eq [Nonempty L] [Nonempty R]
    {u : Matrix (L × R) P ℂ} (hu : u.IsCoisometry)
    {Λ a : Matrix L L ℂ} {Λ' b : Matrix R R ℂ}
    (hΛ : Λ ∈ unitaryGroup L ℂ) (hΛ' : Λ' ∈ unitaryGroup R ℂ)
    (ha : a ∈ unitaryGroup L ℂ) (hb : b ∈ unitaryGroup R ℂ)
    (h₁ : u.map (starRingEnd ℂ) = (Λ ⊗ₖ Λ') * u)
    (h₂ : ((a ⊗ₖ b) * u).map (starRingEnd ℂ) = (Λ ⊗ₖ Λ') * ((a ⊗ₖ b) * u)) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      (w • a).map (starRingEnd ℂ) * Λ = Λ * (w • a) ∧
      (w⁻¹ • b).map (starRingEnd ℂ) * Λ' = Λ' * (w⁻¹ • b) := by
  -- Cancel the coisometry `u` on the right.
  have hK : (a.map (starRingEnd ℂ) * Λ) ⊗ₖ (b.map (starRingEnd ℂ) * Λ') =
      (Λ * a) ⊗ₖ (Λ' * b) := by
    have h := h₂
    rw [Matrix.map_mul, map_star_kronecker, h₁, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← mul_kronecker_mul, ← mul_kronecker_mul] at h
    have h' := congrArg (· * uᴴ) h
    simpa only [Matrix.mul_assoc, show u * uᴴ = 1 from hu, Matrix.mul_one] using h'
  have habar : a.map (starRingEnd ℂ) ∈ unitaryGroup L ℂ :=
    map_star_mem_unitaryGroup_iff.mpr ha
  have hbbar : b.map (starRingEnd ℂ) ∈ unitaryGroup R ℂ :=
    map_star_mem_unitaryGroup_iff.mpr hb
  -- Compare the two sides as `(Λ a)† (ā Λ) ⊗ (Λ' b)† (b̄ Λ') = 1`.
  have hA : Λ * a ∈ unitaryGroup L ℂ := (unitaryGroup L ℂ).mul_mem hΛ ha
  have hB : Λ' * b ∈ unitaryGroup R ℂ := (unitaryGroup R ℂ).mul_mem hΛ' hb
  have hone : ((Λ * a)ᴴ * (a.map (starRingEnd ℂ) * Λ)) ⊗ₖ
      ((Λ' * b)ᴴ * (b.map (starRingEnd ℂ) * Λ')) = 1 := by
    rw [mul_kronecker_mul, hK, ← mul_kronecker_mul,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
      mem_unitaryGroup_iff'.mp hA, mem_unitaryGroup_iff'.mp hB, one_kronecker_one]
  obtain ⟨c, hc0, hcA, hcB⟩ := exists_eq_smul_one_of_kronecker_eq_one hone
  have hcunit : c • (1 : Matrix L L ℂ) ∈ unitaryGroup L ℂ := by
    rw [← hcA]
    exact (unitaryGroup L ℂ).mul_mem (Unitary.star_mem hA)
      ((unitaryGroup L ℂ).mul_mem habar hΛ)
  have hcnorm : ‖c‖ = 1 := norm_eq_one_of_smul_one_mem_unitaryGroup hcunit
  -- `ā Λ = c Λ a` and `b̄ Λ' = c⁻¹ Λ' b`.
  have hlA : a.map (starRingEnd ℂ) * Λ = c • (Λ * a) := by
    have h := congrArg ((Λ * a) * ·) hcA
    rwa [← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, mem_unitaryGroup_iff.mp hA,
      Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at h
  have hlB : b.map (starRingEnd ℂ) * Λ' = c⁻¹ • (Λ' * b) := by
    have h := congrArg ((Λ' * b) * ·) hcB
    rwa [← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, mem_unitaryGroup_iff.mp hB,
      Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at h
  -- A square root `w` of `c` has `conj(w) c = w`.
  set w : ℂ := c ^ (2⁻¹ : ℂ) with hw
  have hw2 : w ^ 2 = c := by
    rw [hw]
    exact_mod_cast Complex.cpow_nat_inv_pow c two_ne_zero
  have hwnorm : ‖w‖ = 1 := by
    have h : ‖w‖ ^ 2 = 1 := by rw [← norm_pow, hw2, hcnorm]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) two_ne_zero).mp h
  have hw0 : w ≠ 0 := by
    intro h0; simp [h0] at hwnorm
  have hwconj : starRingEnd ℂ w = w⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hwnorm]
    simp
  have hkey : starRingEnd ℂ w * c = w := by
    rw [hwconj, ← hw2, pow_two, ← mul_assoc, inv_mul_cancel₀ hw0, one_mul]
  refine ⟨w, hwnorm, ?_, ?_⟩
  · rw [Matrix.map_smul' _ _ _ (map_mul (starRingEnd ℂ)), Matrix.smul_mul, hlA, smul_smul, hkey,
      Matrix.mul_smul]
  · rw [Matrix.map_smul' _ _ _ (map_mul (starRingEnd ℂ)), Matrix.smul_mul, hlB, smul_smul,
      map_inv₀, ← mul_inv, hkey, Matrix.mul_smul]

omit [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] in
theorem smul_kronecker_inv_smul {w : ℂ} (hw : w ≠ 0) (a : Matrix L L ℂ) (b : Matrix R R ℂ) :
    (w • a) ⊗ₖ (w⁻¹ • b) = a ⊗ₖ b := by
  rw [smul_kronecker, kronecker_smul, smul_smul, mul_inv_cancel₀ hw, one_smul]

omit [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R] in
theorem conjTranspose_inv_smul_kronecker_conjTranspose_smul {w : ℂ} (hw : ‖w‖ = 1)
    (a : Matrix L L ℂ) (b : Matrix R R ℂ) :
    (w⁻¹ • b)ᴴ ⊗ₖ (w • a)ᴴ = bᴴ ⊗ₖ aᴴ := by
  have hw0 : w ≠ 0 := by intro h0; simp [h0] at hw
  have hwconj : star w = w⁻¹ := by
    rw [Complex.star_def, Complex.inv_def, Complex.normSq_eq_norm_sq, hw]
    simp
  rw [conjTranspose_smul, conjTranspose_smul, star_inv₀, hwconj, inv_inv,
    smul_kronecker, kronecker_smul, smul_smul, mul_inv_cancel₀ hw0, one_smul]

/-- A real matrix has equal transpose and adjoint. -/
theorem conjTranspose_eq_transpose_of_map_star_eq {m n : Type*} {M : Matrix m n ℂ}
    (hM : M.map (starRingEnd ℂ) = M) : Mᴴ = Mᵀ := by
  rw [conjTranspose, Matrix.transpose_map]
  exact congrArg Matrix.transpose hM

/-- A unit-modulus multiple of a unitary matrix is unitary. -/
theorem smul_mem_unitaryGroup_of_norm_eq_one {n : Type*} [Fintype n] [DecidableEq n] {c : ℂ}
    (hc : ‖c‖ = 1) {M : Matrix n n ℂ} (hM : M ∈ unitaryGroup n ℂ) :
    c • M ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, ← Matrix.star_eq_conjTranspose, mem_unitaryGroup_iff.mp hM,
    smul_smul, Complex.star_def]
  have h : c * (starRingEnd ℂ) c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    norm_num
  rw [h, one_smul]

/-- **Case I uniqueness.** Let `u'` be a real coisometry and let `a, b` be
unitaries with `(a ⊗ b) u'` real. Then `a ⊗ b = O_ℓ ⊗ O_r` and
`b† ⊗ a† = O_rᵀ ⊗ O_ℓᵀ` with `O_ℓ, O_r` real orthogonal.
Source: arXiv:1703.09188, `corconj`, Case I (lines 1104--1112) and the proof at
lines 1151--1157. -/
theorem exists_orthogonal_factors_of_kronecker_mul [Nonempty L] [Nonempty R]
    {u : Matrix (L × R) P ℂ} (hu : u.IsCoisometry)
    {a : Matrix L L ℂ} {b : Matrix R R ℂ}
    (ha : a ∈ unitaryGroup L ℂ) (hb : b ∈ unitaryGroup R ℂ)
    (h₁ : u.map (starRingEnd ℂ) = u)
    (h₂ : ((a ⊗ₖ b) * u).map (starRingEnd ℂ) = (a ⊗ₖ b) * u) :
    ∃ (Oℓ : Matrix L L ℂ) (Or : Matrix R R ℂ),
      Oℓ ∈ unitaryGroup L ℂ ∧ Oℓ.map (starRingEnd ℂ) = Oℓ ∧
      Or ∈ unitaryGroup R ℂ ∧ Or.map (starRingEnd ℂ) = Or ∧
      a ⊗ₖ b = Oℓ ⊗ₖ Or ∧ bᴴ ⊗ₖ aᴴ = Orᵀ ⊗ₖ Oℓᵀ := by
  obtain ⟨w, hw, hwa, hwb⟩ := exists_phase_of_kronecker_mul_map_star_eq hu
    (one_mem _) (one_mem _) ha hb (by simpa [one_kronecker_one] using h₁)
    (by simpa [one_kronecker_one] using h₂)
  have hw0 : w ≠ 0 := by intro h0; simp [h0] at hw
  have hwinv : ‖w⁻¹‖ = 1 := by rw [norm_inv, hw, inv_one]
  have hOℓ : (w • a).map (starRingEnd ℂ) = w • a := by simpa using hwa
  have hOr : (w⁻¹ • b).map (starRingEnd ℂ) = w⁻¹ • b := by simpa using hwb
  refine ⟨w • a, w⁻¹ • b, smul_mem_unitaryGroup_of_norm_eq_one hw ha, hOℓ,
    smul_mem_unitaryGroup_of_norm_eq_one hwinv hb, hOr,
    (smul_kronecker_inv_smul hw0 a b).symm, ?_⟩
  rw [← conjTranspose_eq_transpose_of_map_star_eq hOℓ,
    ← conjTranspose_eq_transpose_of_map_star_eq hOr,
    conjTranspose_inv_smul_kronecker_conjTranspose_smul hw]

/-- A unitary `S` with `conj(S) Σ = Σ S` satisfies the symplectic identity
`Sᵀ Σ S = Σ`. -/
theorem transpose_mul_mul_eq_of_map_star_mul_eq {n : Type*} [Fintype n] [DecidableEq n]
    {S Λ : Matrix n n ℂ} (hS : S ∈ unitaryGroup n ℂ)
    (h : S.map (starRingEnd ℂ) * Λ = Λ * S) : Sᵀ * Λ * S = Λ := by
  rw [Matrix.mul_assoc, ← h, ← Matrix.mul_assoc, transpose_mul_map_star_of_mem_unitaryGroup hS,
    Matrix.one_mul]

/-- **Case II uniqueness.** Let `u'` be a coisometry with
`conj(u') = (Σ_ℓ ⊗ Σ_r) u'`, and let `a, b` be unitaries such that `(a ⊗ b) u'`
satisfies the same equation. Then `a ⊗ b = S_ℓ ⊗ S_r` and
`b† ⊗ a† = S_r† ⊗ S_ℓ†` with `S_ℓ, S_r` unitary and
`S_xᵀ Σ_x S_x = Σ_x`.
Source: arXiv:1703.09188, `corconj`, Case II (lines 1113--1125) and the proof
at lines 1151--1163. The local fix of this module applies. -/
theorem exists_symplectic_factors_of_kronecker_mul {ℓ r : ℕ} (hℓ : Even ℓ) (hr : Even r)
    [Nonempty (Fin ℓ)] [Nonempty (Fin r)]
    {u : Matrix (Fin ℓ × Fin r) P ℂ} (hu : u.IsCoisometry)
    {a : Matrix (Fin ℓ) (Fin ℓ) ℂ} {b : Matrix (Fin r) (Fin r) ℂ}
    (ha : a ∈ unitaryGroup (Fin ℓ) ℂ) (hb : b ∈ unitaryGroup (Fin r) ℂ)
    (h₁ : u.map (starRingEnd ℂ) = (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * u)
    (h₂ : ((a ⊗ₖ b) * u).map (starRingEnd ℂ) =
      (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * ((a ⊗ₖ b) * u)) :
    ∃ (Sℓ : Matrix (Fin ℓ) (Fin ℓ) ℂ) (Sr : Matrix (Fin r) (Fin r) ℂ),
      Sℓ ∈ unitaryGroup (Fin ℓ) ℂ ∧ Sℓᵀ * sourceSkewForm hℓ * Sℓ = sourceSkewForm hℓ ∧
      Sr ∈ unitaryGroup (Fin r) ℂ ∧ Srᵀ * sourceSkewForm hr * Sr = sourceSkewForm hr ∧
      a ⊗ₖ b = Sℓ ⊗ₖ Sr ∧ bᴴ ⊗ₖ aᴴ = Srᴴ ⊗ₖ Sℓᴴ := by
  obtain ⟨w, hw, hwa, hwb⟩ := exists_phase_of_kronecker_mul_map_star_eq hu
    (sourceSkewForm_mem_unitaryGroup hℓ) (sourceSkewForm_mem_unitaryGroup hr) ha hb h₁ h₂
  have hw0 : w ≠ 0 := by intro h0; simp [h0] at hw
  have hwinv : ‖w⁻¹‖ = 1 := by rw [norm_inv, hw, inv_one]
  have hSℓ := smul_mem_unitaryGroup_of_norm_eq_one hw ha
  have hSr := smul_mem_unitaryGroup_of_norm_eq_one hwinv hb
  exact ⟨w • a, w⁻¹ • b, hSℓ, transpose_mul_mul_eq_of_map_star_mul_eq hSℓ hwa,
    hSr, transpose_mul_mul_eq_of_map_star_mul_eq hSr hwb,
    (smul_kronecker_inv_smul hw0 a b).symm,
    (conjTranspose_inv_smul_kronecker_conjTranspose_smul hw a b).symm⟩

end Uniqueness

section SymplecticToOrthogonal

variable {ℓ r : ℕ} {P : Type*} [Fintype P] [DecidableEq P]

/-- The regrouping `Fin ℓ × Fin r ≃ (Fin (ℓ/2) × Fin (r/2)) × (Fin 2 × Fin 2)`
that collects the two `Y` positions of `Σ_ℓ ⊗ Σ_r` into the last factor, as in
arXiv:1703.09188, `cor:sympl-to-orthogonal`, lines 1178--1180. -/
def evenPairRegroupEquiv (hℓ : Even ℓ) (hr : Even r) :
    Fin ℓ × Fin r ≃ (Fin (ℓ / 2) × Fin (r / 2)) × (Fin 2 × Fin 2) :=
  (Equiv.prodCongr (evenPairEquiv hℓ).symm (evenPairEquiv hr).symm).trans
    (Equiv.prodProdProdComm _ _ _ _)

/-- In the regrouped coordinates, `Σ_ℓ ⊗ Σ_r = 1_{ℓr/4} ⊗ (Y ⊗ Y)`. -/
theorem reindex_sourceSkewForm_kronecker (hℓ : Even ℓ) (hr : Even r) :
    reindex (evenPairRegroupEquiv hℓ hr) (evenPairRegroupEquiv hℓ hr)
        (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) =
      (1 : Matrix (Fin (ℓ / 2) × Fin (r / 2)) (Fin (ℓ / 2) × Fin (r / 2)) ℂ) ⊗ₖ
        (symplecticY ⊗ₖ symplecticY) := by
  ext ⟨⟨a, b⟩, ⟨c, e⟩⟩ ⟨⟨a', b'⟩, ⟨c', e'⟩⟩
  simp only [evenPairRegroupEquiv, sourceSkewForm, reindex_apply, submatrix_apply,
    kroneckerMap_apply, Equiv.symm_trans_apply, Equiv.prodProdProdComm_symm,
    Equiv.prodProdProdComm_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.symm_symm, Prod.map_apply, one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- The explicit matrix `R` is symmetric and satisfies the two forms of the
transpose congruence used in arXiv:1703.09188, `cor:sympl-to-orthogonal`,
lines 1172--1185. -/
lemma symplecticOrthogonalR_aux :
    symplecticOrthogonalR * symplecticOrthogonalRᴴ = 1 ∧
      symplecticOrthogonalRᵀ * (symplecticY ⊗ₖ symplecticY) = symplecticOrthogonalRᴴ ∧
      (symplecticY ⊗ₖ symplecticY) * symplecticOrthogonalRᵀ = symplecticOrthogonalRᴴ := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
      norm_num [symplecticOrthogonalR, symplecticY, Matrix.mul_apply,
        Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.conjTranspose_apply] <;>
      ring_nf <;> norm_num [Complex.I_sq, Complex.ext_iff]

/-- **Reduction of the symplectic gate `u'` to a real gate.** If
`conj(u') = (Σ_ℓ ⊗ Σ_r) u'`, then in the regrouped coordinates
`u' = (1_{ℓr/4} ⊗ R) uR` with `uR` real; `uR` is unitary between its coordinate
spaces whenever `u'` is. Source: arXiv:1703.09188,
`cor:sympl-to-orthogonal`, eq. `upvpconj` (lines 1168--1185). -/
theorem exists_real_of_map_star_eq_sourceSkewForm_mul (hℓ : Even ℓ) (hr : Even r)
    {u : Matrix (Fin ℓ × Fin r) P ℂ}
    (hu : u.map (starRingEnd ℂ) = (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * u) :
    ∃ uR : Matrix ((Fin (ℓ / 2) × Fin (r / 2)) × (Fin 2 × Fin 2)) P ℂ,
      uR.map (starRingEnd ℂ) = uR ∧
      reindex (evenPairRegroupEquiv hℓ hr) (Equiv.refl P) u =
        ((1 : Matrix (Fin (ℓ / 2) × Fin (r / 2)) (Fin (ℓ / 2) × Fin (r / 2)) ℂ) ⊗ₖ
          symplecticOrthogonalR) * uR ∧
      (u.IsUnitaryBetween → uR.IsUnitaryBetween) := by
  obtain ⟨hRR, hRY, -⟩ := symplecticOrthogonalR_aux
  let e := evenPairRegroupEquiv hℓ hr
  let u₀ := reindex e (Equiv.refl P) u
  let K : Matrix (Fin (ℓ / 2) × Fin (r / 2)) (Fin (ℓ / 2) × Fin (r / 2)) ℂ := 1
  have hu₀ : u₀.map (starRingEnd ℂ) = (K ⊗ₖ (symplecticY ⊗ₖ symplecticY)) * u₀ := by
    have hmul : reindex e e (sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * u₀ =
        reindex e (Equiv.refl P) ((sourceSkewForm hℓ ⊗ₖ sourceSkewForm hr) * u) := by
      simp only [u₀, reindex_apply, submatrix_mul_equiv]
    rw [← reindex_sourceSkewForm_kronecker hℓ hr]
    change _ = reindex e e _ * u₀
    rw [hmul, ← hu]
    ext i j
    simp [u₀, reindex_apply]
  refine ⟨(K ⊗ₖ symplecticOrthogonalRᴴ) * u₀, ?_, ?_, ?_⟩
  · rw [Matrix.map_mul, map_star_kronecker, hu₀, map_star_conjTranspose_eq_transpose,
      ← Matrix.mul_assoc, ← mul_kronecker_mul, hRY]
    simp [K]
  · rw [← Matrix.mul_assoc, ← mul_kronecker_mul, hRR]
    simp [K, u₀, e]
  · intro hU
    have hR : (K ⊗ₖ symplecticOrthogonalRᴴ).IsUnitaryBetween := by
      refine ⟨?_, ?_⟩
      · rw [IsIsometry, conjTranspose_kronecker, conjTranspose_conjTranspose,
          ← mul_kronecker_mul, hRR]
        simp [K]
      · rw [IsCoisometry, conjTranspose_kronecker, conjTranspose_conjTranspose,
          ← mul_kronecker_mul, symplecticOrthogonalR_identities.1]
        simp [K]
    exact hR.mul _ _ (hU.reindex _ _ _)

/-- **Reduction of the symplectic gate `v'` to a real gate.** If
`conj(v') = v' (Σ_r ⊗ Σ_ℓ)`, then in the regrouped coordinates
`v' = vR (1_{rℓ/4} ⊗ R)` with `vR` real; `vR` is unitary between its coordinate
spaces whenever `v'` is. Source: arXiv:1703.09188,
`cor:sympl-to-orthogonal`, eq. `upvpconj` (lines 1168--1185). -/
theorem exists_real_of_map_star_eq_mul_sourceSkewForm (hℓ : Even ℓ) (hr : Even r)
    {v : Matrix P (Fin r × Fin ℓ) ℂ}
    (hv : v.map (starRingEnd ℂ) = v * (sourceSkewForm hr ⊗ₖ sourceSkewForm hℓ)) :
    ∃ vR : Matrix P ((Fin (r / 2) × Fin (ℓ / 2)) × (Fin 2 × Fin 2)) ℂ,
      vR.map (starRingEnd ℂ) = vR ∧
      reindex (Equiv.refl P) (evenPairRegroupEquiv hr hℓ) v =
        vR * ((1 : Matrix (Fin (r / 2) × Fin (ℓ / 2)) (Fin (r / 2) × Fin (ℓ / 2)) ℂ) ⊗ₖ
          symplecticOrthogonalR) ∧
      (v.IsUnitaryBetween → vR.IsUnitaryBetween) := by
  obtain ⟨-, -, hYR⟩ := symplecticOrthogonalR_aux
  let e := evenPairRegroupEquiv hr hℓ
  let v₀ := reindex (Equiv.refl P) e v
  let K : Matrix (Fin (r / 2) × Fin (ℓ / 2)) (Fin (r / 2) × Fin (ℓ / 2)) ℂ := 1
  have hv₀ : v₀.map (starRingEnd ℂ) = v₀ * (K ⊗ₖ (symplecticY ⊗ₖ symplecticY)) := by
    have hmul : v₀ * reindex e e (sourceSkewForm hr ⊗ₖ sourceSkewForm hℓ) =
        reindex (Equiv.refl P) e (v * (sourceSkewForm hr ⊗ₖ sourceSkewForm hℓ)) := by
      simp only [v₀, reindex_apply, submatrix_mul_equiv]
    rw [← reindex_sourceSkewForm_kronecker hr hℓ]
    change _ = v₀ * reindex e e _
    rw [hmul, ← hv]
    ext i j
    simp [v₀, reindex_apply]
  refine ⟨v₀ * (K ⊗ₖ symplecticOrthogonalRᴴ), ?_, ?_, ?_⟩
  · rw [Matrix.map_mul, map_star_kronecker, hv₀, map_star_conjTranspose_eq_transpose,
      Matrix.mul_assoc, ← mul_kronecker_mul, hYR]
    simp [K]
  · rw [Matrix.mul_assoc, ← mul_kronecker_mul, symplecticOrthogonalR_identities.1]
    simp [K, v₀, e]
  · intro hV
    have hR : (K ⊗ₖ symplecticOrthogonalRᴴ).IsUnitaryBetween := by
      refine ⟨?_, ?_⟩
      · rw [IsIsometry, conjTranspose_kronecker, conjTranspose_conjTranspose,
          ← mul_kronecker_mul, symplecticOrthogonalR_aux.1]
        simp [K]
      · rw [IsCoisometry, conjTranspose_kronecker, conjTranspose_conjTranspose,
          ← mul_kronecker_mul, symplecticOrthogonalR_identities.1]
        simp [K]
    exact (hV.reindex _ _ _).mul _ _ hR

end SymplecticToOrthogonal

end Matrix
