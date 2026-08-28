/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.NonCartesianActiveSectorRigidity

/-!
# The universal neighboring-trace obstruction

Every physical-sector decomposition of the candidate is reduced to scalar
sectors, and its neighboring trace matrix has a nonzero minor.

This construction concerns arXiv:1606.00608, Appendix C.2,
Proposition `prop2to3`, lines 1740--1782.
-/

open scoped Matrix BigOperators ComplexOrder Matrix.Norms.Operator

noncomputable section

namespace MPOTensor.NonCartesianActiveSectorCandidate

/-- The unique physical coordinate in a scalar sector. -/
def scalarSectorIndex (F : PhysicalSectorFactorization tensor)
    (k : Fin F.sectorCount) : Σ h, F.SectorIndex h :=
  ⟨k, (⟨0, F.leftDim_pos k⟩, ⟨0, F.rightDim_pos k⟩)⟩

/-- The corresponding physical index before passage to sector coordinates. -/
def scalarSectorPhysicalIndex (F : PhysicalSectorFactorization tensor)
    (k : Fin F.sectorCount) : Fin 4 :=
  F.sectorEquiv.symm (scalarSectorIndex F k)

/-- Every coordinate in a scalar sector is its canonical coordinate. -/
lemma sigma_eq_scalarSectorIndex (F : PhysicalSectorFactorization tensor)
    (q : Σ h, F.SectorIndex h) : q = scalarSectorIndex F q.1 := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · apply Fin.ext
      change q.2.1.val = 0
      have hx := q.2.1.isLt
      have hdim := leftDim_eq_one F q.1
      omega
    · apply Fin.ext
      change q.2.2.val = 0
      have hy := q.2.2.isLt
      have hdim := rightDim_eq_one F q.1
      omega

/-- Every column of the physical isometry is nonzero on at least one scalar
sector. -/
lemma exists_scalarSector_isometry_ne_zero
    (F : PhysicalSectorFactorization tensor) (p : Fin 4) :
    ∃ k, F.physicalIsometry (scalarSectorPhysicalIndex F k) p ≠ 0 := by
  have hcolumn := congrFun (congrFun F.physicalIsometry_isometry p) p
  have hsum :
      ∑ i, star (F.physicalIsometry i p) * F.physicalIsometry i p = 1 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using hcolumn
  have hsum_ne :
      (∑ i, star (F.physicalIsometry i p) * F.physicalIsometry i p) ≠ 0 := by
    rw [hsum]
    norm_num
  obtain ⟨i, hi_mem, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  let q := F.sectorEquiv i
  refine ⟨q.1, ?_⟩
  have hq := sigma_eq_scalarSectorIndex F q
  have hiq : scalarSectorPhysicalIndex F q.1 = i := by
    rw [scalarSectorPhysicalIndex, ← hq]
    exact F.sectorEquiv.symm_apply_apply i
  rw [hiq]
  intro hzero
  apply hi
  simp [hzero]

/-- A column of the physical isometry cannot be nonzero on two different
scalar sectors. -/
lemma scalarSector_isometry_support_unique
    (F : PhysicalSectorFactorization tensor) (p : Fin 4)
    {k h : Fin F.sectorCount}
    (hk : F.physicalIsometry (scalarSectorPhysicalIndex F k) p ≠ 0)
    (hh : F.physicalIsometry (scalarSectorPhysicalIndex F h) p ≠ 0) :
    k = h := by
  by_contra hkh
  have hP := transformedCoordinateProjection_eq_blockDiagonal_left F p
  have hoff := congrFun (congrFun hP (scalarSectorIndex F k))
    (scalarSectorIndex F h)
  simp only [scalarSectorIndex] at hoff
  rw [Matrix.blockDiagonal'_apply_ne _ _ _ hkh] at hoff
  have hoff' : transformedCoordinateProjection F p
      (scalarSectorIndex F k) (scalarSectorIndex F h) = 0 := by
    simpa [scalarSectorIndex] using hoff
  have houter := transformedCoordinateProjection_apply F p
    (scalarSectorIndex F k) (scalarSectorIndex F h)
  rw [hoff'] at houter
  apply (mul_ne_zero hk (star_ne_zero.mpr hh))
  simpa [scalarSectorPhysicalIndex] using houter.symm

/-- The unique scalar sector supporting a column of the physical isometry. -/
noncomputable def supportSector (F : PhysicalSectorFactorization tensor)
    (p : Fin 4) : Fin F.sectorCount :=
  Classical.choose (exists_scalarSector_isometry_ne_zero F p)

/-- The chosen support sector carries a nonzero isometry coefficient. -/
lemma supportSector_isometry_ne_zero
    (F : PhysicalSectorFactorization tensor) (p : Fin 4) :
    F.physicalIsometry (scalarSectorPhysicalIndex F (supportSector F p)) p ≠ 0 :=
  Classical.choose_spec (exists_scalarSector_isometry_ne_zero F p)

/-- Distinct coordinate projections are orthogonal after the physical
transformation and reindexing. -/
lemma transformedCoordinateProjection_mul_eq_zero
    (F : PhysicalSectorFactorization tensor) {p q : Fin 4} (hpq : p ≠ q) :
    transformedCoordinateProjection F p * transformedCoordinateProjection F q = 0 := by
  let E := Matrix.reindexRingEquiv ℂ F.sectorEquiv
  let P (r : Fin 4) := Matrix.diagonal (fun i ↦ if i = r then (1 : ℂ) else 0)
  change E (F.physicalIsometry * P p * F.physicalIsometryᴴ) *
      E (F.physicalIsometry * P q * F.physicalIsometryᴴ) = 0
  rw [← map_mul]
  have hdiag : P p * P q = 0 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [mul_ite, mul_one, mul_zero, Matrix.diagonal_apply_eq,
        Matrix.zero_apply, ite_eq_right_iff, one_ne_zero, imp_false]
      intro hiq hip
      exact hpq (hip.symm.trans hiq)
    · simp [hij]
  have hinside :
      (F.physicalIsometry * P p * F.physicalIsometryᴴ) *
          (F.physicalIsometry * P q * F.physicalIsometryᴴ) = 0 := by
    calc
      _ = F.physicalIsometry * P p *
          (F.physicalIsometryᴴ * F.physicalIsometry) * P q *
            F.physicalIsometryᴴ := by noncomm_ring
      _ = F.physicalIsometry * (P p * P q) * F.physicalIsometryᴴ := by
        rw [F.physicalIsometry_isometry]
        noncomm_ring
      _ = 0 := by rw [hdiag]; simp
  rw [hinside, map_zero]

/-- Distinct physical coordinate projections occupy distinct scalar sectors. -/
lemma supportSector_injective (F : PhysicalSectorFactorization tensor) :
    Function.Injective (supportSector F) := by
  intro p q hpqSector
  by_contra hpq
  let k := supportSector F p
  have hkq : supportSector F q = k := by
    simpa [k] using hpqSector.symm
  let s := scalarSectorIndex F k
  let P := transformedCoordinateProjection F p
  let Q := transformedCoordinateProjection F q
  have hpU := supportSector_isometry_ne_zero F p
  have hqU := supportSector_isometry_ne_zero F q
  have hP := transformedCoordinateProjection_eq_blockDiagonal_left F p
  have hQ := transformedCoordinateProjection_eq_blockDiagonal_left F q
  have hPdiag : P s s ≠ 0 := by
    change transformedCoordinateProjection F p s s ≠ 0
    rw [transformedCoordinateProjection_apply]
    simpa [s, k, scalarSectorPhysicalIndex] using
      mul_ne_zero hpU (star_ne_zero.mpr hpU)
  have hQdiag : Q s s ≠ 0 := by
    change transformedCoordinateProjection F q s s ≠ 0
    rw [transformedCoordinateProjection_apply]
    rw [hkq] at hqU
    simpa [s, k, scalarSectorPhysicalIndex] using
      mul_ne_zero hqU (star_ne_zero.mpr hqU)
  have hoff (z : Σ h, F.SectorIndex h) (hz : z ≠ s) : P s z = 0 := by
    have hzsector : k ≠ z.1 := by
      intro hkz
      apply hz
      calc
        z = scalarSectorIndex F z.1 := sigma_eq_scalarSectorIndex F z
        _ = scalarSectorIndex F k := by rw [hkz]
        _ = s := rfl
    have h := congrFun (congrFun hP s) z
    have hs : s.1 = k := rfl
    simp only [s, scalarSectorIndex] at h
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ hzsector] at h
    simpa [P, s, scalarSectorIndex] using h
  have hzero := transformedCoordinateProjection_mul_eq_zero F hpq
  have hentry := congrFun (congrFun hzero s) s
  have hsum : (P * Q) s s = P s s * Q s s := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_single s
    · intro z hzmem hzs
      rw [hoff z hzs]
      simp
    · simp
  change (P * Q) s s = (0 : Matrix _ _ ℂ) s s at hentry
  simp only [Matrix.zero_apply] at hentry
  rw [hsum] at hentry
  exact (mul_ne_zero hPdiag hQdiag) hentry

/-- An isometry column vanishes on every scalar sector except its chosen
support. -/
lemma isometry_eq_zero_of_supportSector_ne
    (F : PhysicalSectorFactorization tensor) (p : Fin 4)
    (k : Fin F.sectorCount) (hpk : supportSector F p ≠ k) :
    F.physicalIsometry (scalarSectorPhysicalIndex F k) p = 0 := by
  by_contra hne
  exact hpk (scalarSector_isometry_support_unique F p
    (supportSector_isometry_ne_zero F p) hne)

/-- On the support of a column, its squared modulus is one. -/
lemma isometry_mul_star_at_support
    (F : PhysicalSectorFactorization tensor) (p : Fin 4) :
    F.physicalIsometry (scalarSectorPhysicalIndex F (supportSector F p)) p *
        star (F.physicalIsometry
          (scalarSectorPhysicalIndex F (supportSector F p)) p) = 1 := by
  let i := scalarSectorPhysicalIndex F (supportSector F p)
  have hrow := congrFun (congrFun F.physicalIsometry_mul_conjTranspose i) i
  have hsum :
      ∑ q, F.physicalIsometry i q * star (F.physicalIsometry i q) = 1 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using hrow
  rw [← hsum]
  symm
  apply Finset.sum_eq_single p
  · intro q hqmem hqp
    have hsupport : supportSector F q ≠ supportSector F p := by
      intro h
      exact hqp ((supportSector_injective F) h)
    rw [isometry_eq_zero_of_supportSector_ne F q (supportSector F p) hsupport]
    simp
  · simp

/-- Conjugating a diagonal matrix by the physical isometry evaluates its
diagonal entry at the unique supported coordinate. -/
lemma conjugate_diagonal_apply_at_support
    (F : PhysicalSectorFactorization tensor) (p : Fin 4) (d : Fin 4 → ℂ) :
    (F.physicalIsometry * Matrix.diagonal d * F.physicalIsometryᴴ)
        (scalarSectorPhysicalIndex F (supportSector F p))
        (scalarSectorPhysicalIndex F (supportSector F p)) = d p := by
  let i := scalarSectorPhysicalIndex F (supportSector F p)
  have hmul :
      F.physicalIsometry * Matrix.diagonal d =
        Matrix.of fun x q ↦ F.physicalIsometry x q * d q := by
    ext x q
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
  rw [hmul]
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  rw [show (∑ q, F.physicalIsometry i q * d q *
      star (F.physicalIsometry i q)) =
      F.physicalIsometry i p * d p * star (F.physicalIsometry i p) by
    apply Finset.sum_eq_single p
    · intro q hqmem hqp
      have hsupport : supportSector F q ≠ supportSector F p := by
        intro h
        exact hqp ((supportSector_injective F) h)
      rw [isometry_eq_zero_of_supportSector_ne F q (supportSector F p) hsupport]
      simp
    · simp]
  have hnorm := isometry_mul_star_at_support F p
  change F.physicalIsometry i p * d p * star (F.physicalIsometry i p) = d p
  calc
    _ = d p * (F.physicalIsometry i p * star (F.physicalIsometry i p)) := by ring
    _ = d p := by rw [hnorm]; simp

/-- Ordered eigenvalues of the left observable. -/
def leftEigenvalue : Fin 4 → ℂ := ![1, 2, -7, 4]

/-- Ordered eigenvalues of the right observable. -/
def rightEigenvalue : Fin 4 → ℂ := ![-3, -1, 1, 3]

/-- The transformed left observable has its `p`-th eigenvalue on the support
sector of column `p`. -/
lemma left_observable_apply_support
    (F : PhysicalSectorFactorization tensor) (p : Fin 4) :
    ((4 : ℂ) • F.transformedPhysicalSlice 1 0)
        (scalarSectorIndex F (supportSector F p))
        (scalarSectorIndex F (supportSector F p)) = leftEigenvalue p := by
  have hdiag :
      (4 : ℂ) • physicalSlice tensor 1 0 = Matrix.diagonal leftEigenvalue := by
    rw [physicalSlice_one_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [leftEigenvalue]
  have hobs :
      (4 : ℂ) • F.transformedPhysicalSlice 1 0 =
        Matrix.reindex F.sectorEquiv F.sectorEquiv
          (F.physicalIsometry * Matrix.diagonal leftEigenvalue *
            F.physicalIsometryᴴ) := by
    rw [← hdiag]
    have hin :
        F.physicalIsometry * ((4 : ℂ) • physicalSlice tensor 1 0) *
            F.physicalIsometryᴴ =
          (4 : ℂ) • (F.physicalIsometry * physicalSlice tensor 1 0 *
            F.physicalIsometryᴴ) := by simp
    rw [hin]
    ext i j
    rfl
  rw [hobs]
  simpa [Matrix.reindex_apply, scalarSectorPhysicalIndex] using
    conjugate_diagonal_apply_at_support F p leftEigenvalue

/-- The transformed right observable has its `p`-th eigenvalue on the support
sector of column `p`. -/
lemma right_observable_apply_support
    (F : PhysicalSectorFactorization tensor) (p : Fin 4) :
    ((100 : ℂ) • F.transformedPhysicalSlice 0 1)
        (scalarSectorIndex F (supportSector F p))
        (scalarSectorIndex F (supportSector F p)) = rightEigenvalue p := by
  have hdiag :
      (100 : ℂ) • physicalSlice tensor 0 1 = Matrix.diagonal rightEigenvalue := by
    rw [physicalSlice_zero_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rightEigenvalue]
  have hobs :
      (100 : ℂ) • F.transformedPhysicalSlice 0 1 =
        Matrix.reindex F.sectorEquiv F.sectorEquiv
          (F.physicalIsometry * Matrix.diagonal rightEigenvalue *
            F.physicalIsometryᴴ) := by
    rw [← hdiag]
    have hin :
        F.physicalIsometry * ((100 : ℂ) • physicalSlice tensor 0 1) *
            F.physicalIsometryᴴ =
          (100 : ℂ) • (F.physicalIsometry * physicalSlice tensor 0 1 *
            F.physicalIsometryᴴ) := by simp
    rw [hin]
    ext i j
    rfl
  rw [hobs]
  simpa [Matrix.reindex_apply, scalarSectorPhysicalIndex] using
    conjugate_diagonal_apply_at_support F p rightEigenvalue

/-- Scalar left coefficient of a sector. -/
def scalarLeft (F : PhysicalSectorFactorization tensor)
    (k : Fin F.sectorCount) (beta : Fin 2) : ℂ :=
  F.leftTensor k beta ⟨0, F.leftDim_pos k⟩ ⟨0, F.leftDim_pos k⟩

/-- Scalar right coefficient of a sector. -/
def scalarRight (F : PhysicalSectorFactorization tensor)
    (k : Fin F.sectorCount) (alpha : Fin 2) : ℂ :=
  F.rightTensor k alpha ⟨0, F.rightDim_pos k⟩ ⟨0, F.rightDim_pos k⟩

/-- The zero-index scalar coefficients multiply to `(1/4)`. -/
lemma scalarLeft_mul_scalarRight_zero
    (F : PhysicalSectorFactorization tensor) (k : Fin F.sectorCount) :
    scalarLeft F k 0 * scalarRight F k 0 = 1 / 4 := by
  have h := zero_zero_block_of_factorization F k
  have hentry := congrFun (congrFun h
    (⟨0, F.leftDim_pos k⟩, ⟨0, F.rightDim_pos k⟩))
    (⟨0, F.leftDim_pos k⟩, ⟨0, F.rightDim_pos k⟩)
  simpa [scalarLeft, scalarRight, Matrix.kroneckerMap_apply] using hentry

/-- On a supported sector, the ratio of the two left coefficients is the
corresponding left eigenvalue. -/
lemma scalarLeft_one_eq_at_support
    (F : PhysicalSectorFactorization tensor) (p : Fin 4) :
    scalarLeft F (supportSector F p) 1 =
      leftEigenvalue p * scalarLeft F (supportSector F p) 0 := by
  let k := supportSector F p
  have hobs := left_observable_apply_support F p
  rw [F.transformedPhysicalSlice_eq] at hobs
  simp only [Matrix.smul_apply] at hobs
  have hzero := scalarLeft_mul_scalarRight_zero F k
  have hzero_ne : scalarLeft F k 0 * scalarRight F k 0 ≠ 0 := by
    rw [hzero]
    norm_num
  apply mul_right_cancel₀ (right_ne_zero_of_mul hzero_ne)
  change scalarLeft F k 1 * scalarRight F k 0 =
    (leftEigenvalue p * scalarLeft F k 0) * scalarRight F k 0
  have hscaled : (4 : ℂ) *
      (scalarLeft F k 1 * scalarRight F k 0) = leftEigenvalue p := by
    simpa [k, scalarLeft, scalarRight, scalarSectorIndex] using hobs
  calc
    scalarLeft F k 1 * scalarRight F k 0 =
        (1 / 4 : ℂ) * leftEigenvalue p := by
      apply mul_left_cancel₀ (show (4 : ℂ) ≠ 0 by norm_num)
      rw [hscaled]
      ring
    _ = (leftEigenvalue p * scalarLeft F k 0) * scalarRight F k 0 := by
      calc
        _ = leftEigenvalue p * (scalarLeft F k 0 * scalarRight F k 0) := by
          rw [hzero]
          ring
        _ = _ := by ring

/-- On a supported sector, the ratio of the two right coefficients is the
corresponding right eigenvalue. -/
lemma scalarRight_one_eq_at_support
    (F : PhysicalSectorFactorization tensor) (p : Fin 4) :
    scalarRight F (supportSector F p) 1 =
      (rightEigenvalue p / 25) * scalarRight F (supportSector F p) 0 := by
  let k := supportSector F p
  have hobs := right_observable_apply_support F p
  rw [F.transformedPhysicalSlice_eq] at hobs
  simp only [Matrix.smul_apply] at hobs
  have hzero := scalarLeft_mul_scalarRight_zero F k
  have hzero_ne : scalarLeft F k 0 * scalarRight F k 0 ≠ 0 := by
    rw [hzero]
    norm_num
  apply mul_left_cancel₀ (left_ne_zero_of_mul hzero_ne)
  change scalarLeft F k 0 * scalarRight F k 1 =
    scalarLeft F k 0 * ((rightEigenvalue p / 25) * scalarRight F k 0)
  have hscaled : (100 : ℂ) *
      (scalarLeft F k 0 * scalarRight F k 1) = rightEigenvalue p := by
    simpa [k, scalarLeft, scalarRight, scalarSectorIndex] using hobs
  calc
    scalarLeft F k 0 * scalarRight F k 1 =
        (1 / 100 : ℂ) * rightEigenvalue p := by
      apply mul_left_cancel₀ (show (100 : ℂ) ≠ 0 by norm_num)
      rw [hscaled]
      ring
    _ = scalarLeft F k 0 *
        ((rightEigenvalue p / 25) * scalarRight F k 0) := by
      calc
        _ = (rightEigenvalue p / 25) *
            (scalarLeft F k 0 * scalarRight F k 0) := by
          rw [hzero]
          ring
        _ = _ := by ring

/-- In scalar sectors, the neighboring trace is the two-term contraction of
the scalar right and left coefficient vectors. -/
lemma trace_neighboringOperator_scalar
    (F : PhysicalSectorFactorization tensor) (k h : Fin F.sectorCount) :
    (F.neighboringOperator k h).trace =
      scalarRight F k 0 * scalarLeft F h 0 +
        scalarRight F k 1 * scalarLeft F h 1 := by
  let x₀ : F.NeighborIndex k h :=
    (⟨0, F.rightDim_pos k⟩, ⟨0, F.leftDim_pos h⟩)
  rw [Matrix.trace]
  rw [show (∑ x, (F.neighboringOperator k h).diag x) =
      F.neighboringOperator k h x₀ x₀ by
    apply Finset.sum_eq_single x₀
    · intro x hxmem hxx
      exfalso
      apply hxx
      apply Prod.ext
      · apply Fin.ext
        have hx := x.1.isLt
        have hdim := rightDim_eq_one F k
        omega
      · apply Fin.ext
        have hx := x.2.isLt
        have hdim := leftDim_eq_one F h
        omega
    · simp]
  simp only [PhysicalSectorFactorization.neighboringOperator_apply]
  rw [Fin.sum_univ_two]
  rfl

/-- The neighboring trace matrix of any scalar-sector factorization has a
nonzero two-by-two minor on the sectors supporting coordinates zero and one. -/
lemma neighboringTrace_minor_ne_zero
    (F : PhysicalSectorFactorization tensor) :
    let k₀ := supportSector F 0
    let k₁ := supportSector F 1
    (F.neighboringOperator k₀ k₀).trace *
          (F.neighboringOperator k₁ k₁).trace -
        (F.neighboringOperator k₀ k₁).trace *
          (F.neighboringOperator k₁ k₀).trace ≠ 0 := by
  dsimp only
  rw [trace_neighboringOperator_scalar, trace_neighboringOperator_scalar,
    trace_neighboringOperator_scalar, trace_neighboringOperator_scalar]
  rw [scalarLeft_one_eq_at_support, scalarLeft_one_eq_at_support,
    scalarRight_one_eq_at_support, scalarRight_one_eq_at_support]
  norm_num [leftEigenvalue, rightEigenvalue]
  have h₀ := scalarLeft_mul_scalarRight_zero F (supportSector F 0)
  have h₁ := scalarLeft_mul_scalarRight_zero F (supportSector F 1)
  intro hminor
  have hpair₀ : scalarRight F (supportSector F 0) 0 *
      scalarLeft F (supportSector F 0) 0 ≠ 0 := by
    rw [show scalarRight F (supportSector F 0) 0 *
        scalarLeft F (supportSector F 0) 0 = 1 / 4 by
      rw [mul_comm]
      exact h₀]
    norm_num
  have hpair₁ : scalarRight F (supportSector F 1) 0 *
      scalarLeft F (supportSector F 1) 0 ≠ 0 := by
    rw [show scalarRight F (supportSector F 1) 0 *
        scalarLeft F (supportSector F 1) 0 = 1 / 4 by
      rw [mul_comm]
      exact h₁]
    norm_num
  apply mul_ne_zero hpair₀ hpair₁
  linear_combination (25 / 2) * hminor

/-- No physical-sector factorization of the candidate has a rank-one
neighboring trace matrix. -/
theorem no_neighboringTraceFactorization
    (F : PhysicalSectorFactorization tensor) :
    IsEmpty F.NeighboringTraceFactorization := by
  constructor
  intro H
  apply neighboringTrace_minor_ne_zero F
  rw [H.trace_neighboringOperator, H.trace_neighboringOperator,
    H.trace_neighboringOperator, H.trace_neighboringOperator]
  push_cast
  ring

/-- The candidate admits no physical-sector factorization satisfying the
neighboring trace factorization required in CPSV16 Proposition C.7. -/
theorem not_exists_neighboringTraceFactorization :
    ¬∃ F : PhysicalSectorFactorization tensor,
      Nonempty F.NeighboringTraceFactorization := by
  rintro ⟨F, ⟨hF⟩⟩
  exact (no_neighboringTraceFactorization F).false hF

end MPOTensor.NonCartesianActiveSectorCandidate
