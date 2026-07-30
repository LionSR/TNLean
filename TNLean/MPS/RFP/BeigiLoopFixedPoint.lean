/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.RFP.BeigiLoopInjectivity
import TNLean.MPS.RFP.Defs
import TNLean.MPS.SharedInfra.Scaling
import TNLean.MPS.Tactic.Basic
import TNLean.Spectral.FrobeniusNorm

/-!
# Transfer fixed point of a normalized Beigi loop tensor

The minimal tensor associated with a nonzero Beigi loop need not itself have
an idempotent transfer map.  If the loop bond vector is `φ`, its transfer map
satisfies `E² = ‖φ‖₂² E`.  Dividing every tensor letter by the Euclidean norm
of `φ` gives an injective normal tensor whose transfer map is idempotent.

The normalization does not alter the associated ray of periodic vectors: at
length `N`, it multiplies Beigi's product-of-pairs vector by `‖φ‖₂⁻ᴺ`.

## References

* S. Beigi, *Classification of the phases of 1D spin chains with commuting
  Hamiltonians*, J. Phys. A 45 (2012) 025306, Section IV.
* J. I. Cirac, D. Pérez-García, N. Schuch, and F. Verstraete, *Matrix product
  density operators: Renormalization fixed points and boundary theories*,
  arXiv:1606.00608, equations `III_CFI_RFP` and `eq:III_isometry`, source
  lines 543--555; equations `eq:basic-vectors-RFP-pure` and `eq:III_varphi`,
  source lines 570--578; and the fixed-point normal-form derivation, source
  lines 1293--1300.
-/

open scoped BigOperators ComplexOrder Kronecker Matrix Matrix.Norms.Frobenius

namespace Matrix

/-- Summing the completely positive terms associated with all pairwise outer
products gives a rank-one map on the matrix algebra. -/
private theorem sum_vecMulVec_mul_mul_conjTranspose
    {l r n : Type*} [Fintype l] [Fintype r] [Fintype n]
    (Y : Matrix n l ℂ) (X : Matrix r n ℂ) (Z : Matrix n n ℂ) :
    ∑ q : r, ∑ a : l,
      Matrix.vecMulVec (Y.col a) (X.row q) * Z *
          (Matrix.vecMulVec (Y.col a) (X.row q))ᴴ =
      Matrix.trace (Xᴴ * X * Z) • (Y * Yᴴ) := by
  classical
  have hletter (q : r) (a : l) :
      Matrix.vecMulVec (Y.col a) (X.row q) * Z *
          (Matrix.vecMulVec (Y.col a) (X.row q))ᴴ =
        (((X.row q ᵥ* Z) ⬝ᵥ star (X.row q)) : ℂ) •
          Matrix.vecMulVec (Y.col a) (star (Y.col a)) := by
    rw [Matrix.vecMulVec_mul, Matrix.conjTranspose_vecMulVec,
      Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  have hleft :
      ∑ a : l, Matrix.vecMulVec (Y.col a) (star (Y.col a)) = Y * Yᴴ := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.col_apply, Pi.star_apply, RCLike.star_def]
  have hright :
      ∑ q : r, (((X.row q ᵥ* Z) ⬝ᵥ star (X.row q)) : ℂ) =
        Matrix.trace (Xᴴ * X * Z) := by
    rw [← Matrix.trace_mul_cycle X Z Xᴴ]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, Matrix.vecMul]
  simp_rw [hletter, ← Finset.smul_sum]
  rw [← Finset.sum_smul, hright, hleft]

/-- The Hilbert--Schmidt trace is the squared Frobenius norm, regarded as a
complex number. -/
private theorem trace_conjTranspose_mul_self_eq_frobenius_norm_sq
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) :
    trace (Aᴴ * A) = ((‖A‖ ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using
      trace_conjTranspose_mul_self_re_eq_frobenius_norm_sq A
  · have him : (trace (Aᴴ * A)).im = 0 :=
      (RCLike.nonneg_iff.mp
        (posSemidef_conjTranspose_mul_self A).trace_nonneg).2
    simpa only [Complex.ofReal_im] using him

end Matrix

namespace MPSTensor.BeigiSectorGraphData

open FiniteWeightedDigraph

variable {d D : ℕ} {A : MPSTensor d D}

/-- The Euclidean norm of the loop bond vector.

The coordinate-function space has the supremum norm, so the passage to
Euclidean space is essential here.

**Local fix (normalization):** Beigi chooses an arbitrary nonzero loop bond
vector.  The normalized RFP representative divides by its Euclidean norm; see
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16,
`eq:basic-vectors-RFP-pure` and `eq:III_varphi`, source lines 570--578, and
the fixed-point normal-form derivation, source lines 1293--1300. -/
noncomputable def loopBondNorm (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) : ℝ :=
  ‖(WithLp.toLp 2 (F.loopBondVector l) :
    EuclideanSpace ℂ (Matrix.EtaEdgeIndex F.leftDim F.rightDim l.1 l.1))‖

/-- The Euclidean norm of a positive-loop bond vector is positive.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16, fixed-point
normal-form derivation, source lines 1293--1300.  The normalization correction
is recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem loopBondNorm_pos (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) : 0 < F.loopBondNorm l := by
  rw [loopBondNorm, norm_pos_iff]
  simpa [WithLp.toLp_eq_zero] using F.loopBondVector_ne_zero l

/-- The Euclidean norm of a positive-loop bond vector is nonzero.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16, fixed-point
normal-form derivation, source lines 1293--1300.  The normalization correction
is recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem loopBondNorm_ne_zero (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) : F.loopBondNorm l ≠ 0 :=
  ne_of_gt (F.loopBondNorm_pos l)

/-- The Euclidean norm of the loop bond vector is the Frobenius norm of its
coefficient matrix.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16, fixed-point
normal-form derivation, source lines 1293--1300.  The normalization correction
is recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem loopBondNorm_eq_frobeniusNorm (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) :
    F.loopBondNorm l =
      ‖Matrix.schmidtCoeffMatrix (F.loopBondVector l)‖ := by
  rw [loopBondNorm, ← MPSTensor.norm_matToES_eq_frobenius_norm]
  rfl

/-- The minimal sector-coordinate loop tensor divided by the Euclidean norm
of its bond vector.

**Local fix (Schmidt support and normalization):** Restriction to the Schmidt
support removes unused virtual directions, while division by the Euclidean
norm gives the normalized fixed-point representative; see
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16,
`III_CFI_RFP` and `eq:III_isometry`, source lines 543--555,
`eq:basic-vectors-RFP-pure` and `eq:III_varphi`, source lines 570--578, and
the fixed-point normal-form derivation, source lines 1293--1300. -/
noncomputable def normalizedMinimalLoopCoordinateTensor
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    MPSTensor d (F.loopSchmidtRank l) :=
  fun i ↦ ((F.loopBondNorm l : ℂ)⁻¹) • F.minimalLoopCoordinateTensor l i

/-- The physical minimal loop tensor divided by the Euclidean norm of its
bond vector.

**Local fix (Schmidt support and normalization):** This is the normalized
representative of Beigi's product-of-pairs tensor on its Schmidt support; see
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16,
`III_CFI_RFP` and `eq:III_isometry`, source lines 543--555,
`eq:basic-vectors-RFP-pure` and `eq:III_varphi`, source lines 570--578, and
the fixed-point normal-form derivation, source lines 1293--1300. -/
noncomputable def normalizedMinimalLoopTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) : MPSTensor d (F.loopSchmidtRank l) :=
  fun i ↦ ((F.loopBondNorm l : ℂ)⁻¹) • F.minimalLoopTensor l i

private theorem normalizedMinimalLoopTensor_eq_rotatePhysical
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    F.normalizedMinimalLoopTensor l =
      rotatePhysical F.unitary (F.normalizedMinimalLoopCoordinateTensor l) := by
  classical
  ext i
  simp only [normalizedMinimalLoopTensor, normalizedMinimalLoopCoordinateTensor,
    minimalLoopTensor, rotatePhysical_apply, Finset.smul_sum, smul_smul]
  simp [mul_comm]

/-- Distinct normalized minimal loop tensors have zero mixed transfer map in
sector coordinates. -/
private theorem normalizedMinimalLoopCoordinateTensor_mixedTransferMap₂_eq_zero_of_ne
    (F : BeigiSectorGraphData A) {l m : Loop F.edgeWeight} (hlm : l ≠ m) :
    mixedTransferMap₂ (F.normalizedMinimalLoopCoordinateTensor l)
      (F.normalizedMinimalLoopCoordinateTensor m) = 0 := by
  classical
  apply LinearMap.ext
  intro Z
  simp only [mixedTransferMap₂_apply, LinearMap.zero_apply]
  calc
    (∑ i : Fin d, F.normalizedMinimalLoopCoordinateTensor l i * Z *
        (F.normalizedMinimalLoopCoordinateTensor m i)ᴴ) =
        ∑ z : Σ k, Fin (F.rightDim k) × Fin (F.leftDim k),
          F.normalizedMinimalLoopCoordinateTensor l (F.sectorEquiv z) * Z *
            (F.normalizedMinimalLoopCoordinateTensor m (F.sectorEquiv z))ᴴ := by
      exact Fintype.sum_equiv F.sectorEquiv.symm
        (fun i : Fin d ↦ F.normalizedMinimalLoopCoordinateTensor l i * Z *
          (F.normalizedMinimalLoopCoordinateTensor m i)ᴴ)
        (fun z ↦ F.normalizedMinimalLoopCoordinateTensor l (F.sectorEquiv z) * Z *
          (F.normalizedMinimalLoopCoordinateTensor m (F.sectorEquiv z))ᴴ)
        (fun i ↦ by rw [Equiv.apply_symm_apply])
    _ = ∑ k : Fin F.sectorCount,
        ∑ qa : Fin (F.rightDim k) × Fin (F.leftDim k),
          F.normalizedMinimalLoopCoordinateTensor l (F.sectorEquiv ⟨k, qa⟩) * Z *
            (F.normalizedMinimalLoopCoordinateTensor m (F.sectorEquiv ⟨k, qa⟩))ᴴ := by
      rw [Fintype.sum_sigma]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      apply Finset.sum_eq_zero
      rintro ⟨q, a⟩ _
      by_cases hkl : k = l.1
      · subst k
        have hlmSector : l.1 ≠ m.1 := by
          intro h
          exact hlm (Subtype.ext h)
        simp only [normalizedMinimalLoopCoordinateTensor]
        rw [F.minimalLoopCoordinateTensor_sector_ne m l.1 hlmSector q a]
        simp
      · simp only [normalizedMinimalLoopCoordinateTensor]
        rw [F.minimalLoopCoordinateTensor_sector_ne l k hkl q a]
        simp

/-- Distinct normalized minimal Beigi loop tensors are locally orthogonal:
their rectangular mixed transfer map vanishes.

Source: CPSV16, proof of Theorem 3.10 at line 1307; Beigi,
J. Phys. A 45 (2012) 025306, Sections III--IV.

**Local fix (Schmidt support and normalization):** The formal loop tensors use
their Schmidt supports and the fixed-point normalization documented in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. The common physical
unitary preserves the mixed transfer map, so disjoint loop-sector support gives
the stated local orthogonality. -/
theorem normalizedMinimalLoopTensor_mixedTransferMap₂_eq_zero_of_ne
    (F : BeigiSectorGraphData A) {l m : Loop F.edgeWeight} (hlm : l ≠ m) :
    mixedTransferMap₂ (F.normalizedMinimalLoopTensor l)
      (F.normalizedMinimalLoopTensor m) = 0 := by
  have hunitary : F.unitary * F.unitaryᴴ = 1 :=
    Unitary.mul_star_self_of_mem F.unitary_mem
  rw [F.normalizedMinimalLoopTensor_eq_rotatePhysical l,
    F.normalizedMinimalLoopTensor_eq_rotatePhysical m,
    mixedTransferMap₂_rotatePhysical _ _ F.unitary hunitary]
  exact F.normalizedMinimalLoopCoordinateTensor_mixedTransferMap₂_eq_zero_of_ne hlm

/-- The transfer map of the minimal loop tensor in sector coordinates is a
rank-one map on the virtual matrix algebra.

**Local fix (Schmidt support):** The two Gram matrices are formed from the
rank factorization through the Schmidt support; see
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source context: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16,
`III_CFI_RFP` and `eq:III_isometry`, source lines 543--555, and the
fixed-point normal-form derivation, source lines 1293--1300.  The rank-one
formula itself is the local rank-factorization calculation recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem transferMap_minimalLoopCoordinateTensor
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    (Z : Matrix (Fin (F.loopSchmidtRank l))
      (Fin (F.loopSchmidtRank l)) ℂ) :
    transferMap (F.minimalLoopCoordinateTensor l) Z =
      Matrix.trace
          ((F.loopSchmidtFactorization l).rightFactorᴴ *
            (F.loopSchmidtFactorization l).rightFactor * Z) •
        ((F.loopSchmidtFactorization l).leftFactor *
          (F.loopSchmidtFactorization l).leftFactorᴴ) := by
  classical
  transfer_simp
  calc
    (∑ i : Fin d, F.minimalLoopCoordinateTensor l i * Z *
        (F.minimalLoopCoordinateTensor l i)ᴴ) =
        ∑ z : Σ k, Fin (F.rightDim k) × Fin (F.leftDim k),
          F.minimalLoopCoordinateTensor l (F.sectorEquiv z) * Z *
            (F.minimalLoopCoordinateTensor l (F.sectorEquiv z))ᴴ := by
      exact Fintype.sum_equiv F.sectorEquiv.symm
        (fun i : Fin d ↦ F.minimalLoopCoordinateTensor l i * Z *
          (F.minimalLoopCoordinateTensor l i)ᴴ)
        (fun z ↦ F.minimalLoopCoordinateTensor l (F.sectorEquiv z) * Z *
          (F.minimalLoopCoordinateTensor l (F.sectorEquiv z))ᴴ)
        (fun i ↦ by rw [Equiv.apply_symm_apply])
    _ = ∑ k : Fin F.sectorCount,
        ∑ qa : Fin (F.rightDim k) × Fin (F.leftDim k),
          F.minimalLoopCoordinateTensor l (F.sectorEquiv ⟨k, qa⟩) * Z *
            (F.minimalLoopCoordinateTensor l (F.sectorEquiv ⟨k, qa⟩))ᴴ := by
      rw [Fintype.sum_sigma]
    _ = ∑ qa : Fin (F.rightDim l.1) × Fin (F.leftDim l.1),
        F.minimalLoopCoordinateTensor l (F.sectorEquiv ⟨l.1, qa⟩) * Z *
          (F.minimalLoopCoordinateTensor l (F.sectorEquiv ⟨l.1, qa⟩))ᴴ := by
      rw [Finset.sum_eq_single l.1]
      · intro k _ hk
        apply Finset.sum_eq_zero
        rintro ⟨q, a⟩ _
        rw [F.minimalLoopCoordinateTensor_sector_ne l k hk q a]
        simp
      · simp
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [F.minimalLoopCoordinateTensor_sector_apply l]
      exact Matrix.sum_vecMulVec_mul_mul_conjTranspose
        (F.loopSchmidtFactorization l).leftFactor
        (F.loopSchmidtFactorization l).rightFactor Z

private theorem loopSchmidtGram_trace
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    Matrix.trace
        ((F.loopSchmidtFactorization l).rightFactorᴴ *
          (F.loopSchmidtFactorization l).rightFactor *
            ((F.loopSchmidtFactorization l).leftFactor *
              (F.loopSchmidtFactorization l).leftFactorᴴ)) =
      (((F.loopBondNorm l) ^ 2 : ℝ) : ℂ) := by
  let X := (F.loopSchmidtFactorization l).rightFactor
  let Y := (F.loopSchmidtFactorization l).leftFactor
  calc
    Matrix.trace (Xᴴ * X * (Y * Yᴴ)) =
        Matrix.trace ((X * Y)ᴴ * (X * Y)) := by
      rw [Matrix.conjTranspose_mul]
      simpa only [Matrix.mul_assoc] using
        Matrix.trace_mul_cycle' Xᴴ (X * Y) Yᴴ
    _ = ((‖X * Y‖ ^ 2 : ℝ) : ℂ) :=
      Matrix.trace_conjTranspose_mul_self_eq_frobenius_norm_sq (X * Y)
    _ = (((F.loopBondNorm l) ^ 2 : ℝ) : ℂ) := by
      rw [(F.loopSchmidtFactorization l).mul_eq]
      rw [← F.loopBondNorm_eq_frobeniusNorm l]

/-- Squaring the transfer map of the unnormalized minimal loop tensor gives
the same map multiplied by the squared Euclidean bond norm.

**Local fix (Schmidt support and normalization):** Beigi's chosen bond vector
is nonzero but need not have unit norm.  Thus the raw transfer map is a scalar
multiple of an idempotent rather than necessarily idempotent itself; see
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source context: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16,
`III_CFI_RFP` and `eq:III_isometry`, source lines 543--555, and the
fixed-point normal-form derivation, source lines 1293--1300.  The scalar
identity itself is the local rank-factorization calculation recorded in
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem transferMap_minimalLoopCoordinateTensor_comp_self
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    transferMap (F.minimalLoopCoordinateTensor l) ∘ₗ
        transferMap (F.minimalLoopCoordinateTensor l) =
      (((F.loopBondNorm l) ^ 2 : ℝ) : ℂ) •
        transferMap (F.minimalLoopCoordinateTensor l) := by
  apply LinearMap.ext
  intro Z
  simp only [LinearMap.comp_apply, LinearMap.smul_apply]
  let Q := (F.loopSchmidtFactorization l).rightFactorᴴ *
    (F.loopSchmidtFactorization l).rightFactor
  let P := (F.loopSchmidtFactorization l).leftFactor *
    (F.loopSchmidtFactorization l).leftFactorᴴ
  have hformula (W : Matrix (Fin (F.loopSchmidtRank l))
      (Fin (F.loopSchmidtRank l)) ℂ) :
      transferMap (F.minimalLoopCoordinateTensor l) W =
        Matrix.trace (Q * W) • P := by
    simpa only [Q, P, Matrix.mul_assoc] using
      F.transferMap_minimalLoopCoordinateTensor l W
  have htrace : Matrix.trace (Q * P) =
      (((F.loopBondNorm l) ^ 2 : ℝ) : ℂ) := by
    simpa only [Q, P, Matrix.mul_assoc] using F.loopSchmidtGram_trace l
  rw [hformula, hformula]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, htrace,
    smul_smul, mul_comm]

/-- Euclidean normalization multiplies the rank-one transfer formula by the
inverse squared bond norm.

**Local fix (Schmidt support and normalization):** The norm is the Euclidean
norm of the bond vector, equivalently the Frobenius norm of its coefficient
matrix; see `docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16,
`III_CFI_RFP` and `eq:III_isometry`, source lines 543--555, and the
fixed-point normal-form derivation, source lines 1293--1300. -/
theorem transferMap_normalizedMinimalLoopCoordinateTensor
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight)
    (Z : Matrix (Fin (F.loopSchmidtRank l))
      (Fin (F.loopSchmidtRank l)) ℂ) :
    transferMap (F.normalizedMinimalLoopCoordinateTensor l) Z =
      (((F.loopBondNorm l : ℂ) ^ 2)⁻¹ *
        Matrix.trace
          ((F.loopSchmidtFactorization l).rightFactorᴴ *
            (F.loopSchmidtFactorization l).rightFactor * Z)) •
        ((F.loopSchmidtFactorization l).leftFactor *
          (F.loopSchmidtFactorization l).leftFactorᴴ) := by
  unfold normalizedMinimalLoopCoordinateTensor
  rw [transferMap_smul, F.transferMap_minimalLoopCoordinateTensor l]
  simp only [smul_smul]
  have hscalar :
      (F.loopBondNorm l : ℂ)⁻¹ * starRingEnd ℂ (F.loopBondNorm l : ℂ)⁻¹ =
        ((F.loopBondNorm l : ℂ) ^ 2)⁻¹ := by
    simp [pow_two]
  rw [hscalar]

/-- The Euclidean-normalized minimal loop tensor in sector coordinates has an
idempotent transfer map.

**Local fix (Schmidt support and normalization):** Euclidean normalization
removes the factor `‖φ‖₂²` from the square of the raw rank-one transfer map;
see `docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16,
`III_CFI_RFP` and `eq:III_isometry`, source lines 543--555, and the
fixed-point normal-form derivation, source lines 1293--1300. -/
theorem normalizedMinimalLoopCoordinateTensor_isTransferIdempotent
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    IsTransferIdempotent (F.normalizedMinimalLoopCoordinateTensor l) := by
  rw [IsTransferIdempotent]
  apply LinearMap.ext
  intro Z
  simp only [LinearMap.comp_apply]
  let Q := (F.loopSchmidtFactorization l).rightFactorᴴ *
    (F.loopSchmidtFactorization l).rightFactor
  let P := (F.loopSchmidtFactorization l).leftFactor *
    (F.loopSchmidtFactorization l).leftFactorᴴ
  let c : ℂ := ((F.loopBondNorm l : ℂ) ^ 2)⁻¹
  have hformula (W : Matrix (Fin (F.loopSchmidtRank l))
      (Fin (F.loopSchmidtRank l)) ℂ) :
      transferMap (F.normalizedMinimalLoopCoordinateTensor l) W =
        (c * Matrix.trace (Q * W)) • P := by
    simpa only [Q, P, c, Matrix.mul_assoc] using
      F.transferMap_normalizedMinimalLoopCoordinateTensor l W
  have htrace : Matrix.trace (Q * P) =
      (((F.loopBondNorm l) ^ 2 : ℝ) : ℂ) := by
    simpa only [Q, P, Matrix.mul_assoc] using F.loopSchmidtGram_trace l
  rw [hformula, hformula]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, htrace]
  congr 1
  dsimp only [c]
  field_simp [Complex.ofReal_ne_zero.mpr (F.loopBondNorm_ne_zero l)]
  push_cast
  exact mul_comm _ _

/-- The Euclidean-normalized physical minimal loop tensor has an idempotent
transfer map.

**Local fix (Schmidt support and normalization):** The physical unitary leaves
the transfer map invariant, so the coordinate result passes to Beigi's
physical coordinates; see
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16,
`III_CFI_RFP` and `eq:III_isometry`, source lines 543--555, and the
fixed-point normal-form derivation, source lines 1293--1300. -/
theorem normalizedMinimalLoopTensor_isTransferIdempotent
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    IsTransferIdempotent (F.normalizedMinimalLoopTensor l) := by
  have hunitary : F.unitary * F.unitaryᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      Unitary.mul_star_self_of_mem F.unitary_mem
  have htransfer :
      transferMap (F.normalizedMinimalLoopTensor l) =
        transferMap (F.normalizedMinimalLoopCoordinateTensor l) := by
    rw [F.normalizedMinimalLoopTensor_eq_rotatePhysical l,
      transferMap_rotatePhysical _ F.unitary hunitary]
  rw [IsTransferIdempotent, htransfer]
  exact F.normalizedMinimalLoopCoordinateTensor_isTransferIdempotent l

/-- The normalized physical loop tensor is injective on its Schmidt support.

**Local fix (Schmidt support and normalization):** Multiplication by the
nonzero inverse bond norm preserves one-site injectivity; see
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16,
`III_CFI_RFP` and `eq:III_isometry`, source lines 543--555, and the
fixed-point normal-form derivation, source lines 1293--1300. -/
theorem normalizedMinimalLoopTensor_isInjective
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    IsInjective (F.normalizedMinimalLoopTensor l) := by
  apply (F.minimalLoopTensor_isInjective l).smul
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (F.loopBondNorm_ne_zero l))

/-- The normalized physical loop tensor is normal on its Schmidt support.

**Local fix (Schmidt support and normalization):** This follows from the
one-site injectivity of the normalized representative; see
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16,
`III_CFI_RFP` and `eq:III_isometry`, source lines 543--555, and the
fixed-point normal-form derivation, source lines 1293--1300. -/
theorem normalizedMinimalLoopTensor_isNormal
    (F : BeigiSectorGraphData A) (l : Loop F.edgeWeight) :
    IsNormal (F.normalizedMinimalLoopTensor l) :=
  (F.normalizedMinimalLoopTensor_isInjective l).isNormal

/-- At length `N`, the periodic vector of the normalized minimal loop tensor
is Beigi's product-of-pairs vector multiplied by `‖φ‖₂⁻ᴺ`.

**Local fix (Schmidt support and normalization):** The scalar is the inverse
Euclidean bond norm at each site; see
`docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`.

Source: Beigi, J. Phys. A 45 (2012) 025306, Section IV, equation (13); CPSV16,
`III_CFI_RFP` and `eq:III_isometry`, source lines 543--555,
`eq:basic-vectors-RFP-pure` and `eq:III_varphi`, source lines 570--578, and
the fixed-point normal-form derivation, source lines 1293--1300. -/
theorem mpv_normalizedMinimalLoopTensor (F : BeigiSectorGraphData A)
    (l : Loop F.edgeWeight) {N : ℕ} [NeZero N] (s : Fin N → Fin d) :
    mpv (F.normalizedMinimalLoopTensor l) s =
      ((F.loopBondNorm l : ℂ)⁻¹) ^ N * F.loopProductState l s := by
  unfold normalizedMinimalLoopTensor
  rw [mpv_smul, F.mpv_minimalLoopTensor l]

end MPSTensor.BeigiSectorGraphData
