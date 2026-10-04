/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.SPTFixedPoint
import TNLean.MPS.Symmetry.TwoSiteBondContraction
import TNLean.MPS.ParentHamiltonian.Martingale.Transport
import TNLean.Algebra.ComplexSqrt

/-!
# The two-site ground space of the SPT fixed point

For the fixed-point tensor with letters `D^{-1/2} |a⟩⟨b|`, the internal
virtual indices of two adjacent sites coincide in every open-boundary
ground-state vector. This is the local
calculation behind the independent-bond parent Hamiltonian of
Schuch--Pérez-García--Cirac, arXiv:1010.3732, Section II.D.2.
-/

open scoped Matrix InnerProductSpace

namespace MPSTensor

/-- The unit maximally entangled vector on the two virtual legs of the
fixed-point tensor. Source: arXiv:1010.3732, Section II.D.2,
`eq:phase-nosym:iso-hamiltonian`. -/
noncomputable def matrixUnitBondVector (D : ℕ) : Fin (D * D) → ℂ :=
  fun p => if (finProdFinEquiv.symm p).1 = (finProdFinEquiv.symm p).2 then
    (↑(Real.sqrt (D : ℝ)) : ℂ)⁻¹ else 0

@[simp] theorem matrixUnitBondVector_apply (D : ℕ) (a b : Fin D) :
    matrixUnitBondVector D (finProdFinEquiv (a, b)) =
      if a = b then (↑(Real.sqrt (D : ℝ)) : ℂ)⁻¹ else 0 := by
  simp [matrixUnitBondVector]

/-- The diagonal bond vector has unit Hilbert norm. Source:
arXiv:1010.3732, Section II.D.2,
`eq:phase-nosym:iso-hamiltonian`. -/
theorem matrixUnitBondVector_sum_normSq (D : ℕ) (hD : 0 < D) :
    ∑ p, Complex.normSq (matrixUnitBondVector D p) = 1 := by
  classical
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Fintype.sum_prod_type, matrixUnitBondVector_apply,
    apply_ite Complex.normSq, Complex.normSq_zero]
  simp only [map_inv₀, Complex.normSq_ofReal, Nat.cast_nonneg, Real.mul_self_sqrt,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt hD)

/-- A two-site boundary vector of the fixed-point tensor has coefficient
`D⁻¹ X d a` when the internal indices of `(a,b)` and `(c,d)` coincide, and zero
otherwise.
Source: arXiv:1010.3732, Section II.D.2,
`eq:phase-nosym:iso-hamiltonian`. -/
theorem groundSpaceMap_sptFixedPointTensor_two_apply (D : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (s : Fin 2 → Fin (D * D)) :
    groundSpaceMap (sptFixedPointTensor D) 2 X s =
      if (finProdFinEquiv.symm (s 0)).2 = (finProdFinEquiv.symm (s 1)).1 then
        (D : ℂ)⁻¹ * X (finProdFinEquiv.symm (s 1)).2 (finProdFinEquiv.symm (s 0)).1
      else 0 := by
  have hc : sptScale D * sptScale D = (D : ℂ)⁻¹ := by
    rw [sptScale, Complex.ofReal_sqrt_inv_mul_self _ (Nat.cast_nonneg D),
      Complex.ofReal_natCast]
  simp [groundSpaceMap_apply, List.ofFn_succ, Kraus.evalWord, sptFixedPointTensor]
  by_cases h : (s 0).modNat = (s 1).divNat
  · simp [h, Matrix.single_mul_single_same, Matrix.trace_single_mul, ← hc]
  · simp [h, Matrix.single_mul_single_of_ne]

/-- The independent-bond interaction annihilates every two-site open-boundary
vector of the fixed-point tensor. Source: arXiv:1010.3732,
Section II.D.2, `eq:phase-nosym:iso-hamiltonian`. -/
theorem twoSiteBondInteraction_groundSpaceMap_sptFixedPointTensor
    (D : ℕ) (hD : 0 < D) (X : Matrix (Fin D) (Fin D) ℂ) :
    (twoSiteBondInteraction
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty (matrixUnitBondVector D)))).mulVec
      (groundSpaceMap (sptFixedPointTensor D) 2 X) = 0 := by
  have hform : groundSpaceMap (sptFixedPointTensor D) 2 X =
      fun s => matrixUnitBondVector D
        (finProdFinEquiv ((sptPair (s 0)).2, (sptPair (s 1)).1)) *
        (sptScale D * X (sptPair (s 1)).2 (sptPair (s 0)).1) := by
    funext s
    rw [groundSpaceMap_sptFixedPointTensor_two_apply]
    simp [matrixUnitBondVector_apply, sptPair, sptScale, ← mul_assoc,
      Complex.ofReal_sqrt_inv_mul_self (D : ℝ) (Nat.cast_nonneg D),
      Complex.ofReal_natCast]
  simpa only [hform] using twoSiteBondPenalty_mulVec_separable
    (matrixUnitBondVector D) (matrixUnitBondVector_sum_normSq D hD)
    (fun a d => sptScale D * X d a)

/-- Reindexing the two virtual legs preserves the independent-bond
projection. -/
theorem bondPenalty_reindex_isStarProjection
    {D : ℕ} (η : Fin (D * D) → ℂ)
    (hη : ∑ p, Complex.normSq (η p) = 1) :
    IsStarProjection
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty η)) := by
  let K := bondPenalty η
  have hK : IsStarProjection K :=
    bondPenalty_isStarProjection _ hη
  rw [isStarProjection_iff'] at hK ⊢
  constructor
  · change (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv.symm K) *
        (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv.symm K) = _
    rw [← map_mul, hK.1]
    rfl
  · have hKH : Kᴴ = K := by
      simpa only [Matrix.star_eq_conjTranspose] using hK.2
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
    change Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm Kᴴ =
      Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm K
    rw [hKH]

/-- The two-site independent-bond interaction is an orthogonal projection
whenever its bond vector has unit norm. -/
theorem twoSiteBondInteraction_bondPenalty_isSymmetricProjection
    {D : ℕ} (η : Fin (D * D) → ℂ)
    (hη : ∑ p, Complex.normSq (η p) = 1) :
    (Matrix.toEuclideanLin
      (twoSiteBondInteraction
        (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (bondPenalty η)))).IsSymmetricProjection := by
  let M := twoSiteBondInteraction
    (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (bondPenalty η))
  have hM : IsStarProjection M :=
    twoSiteBondInteraction_isStarProjection _
      (bondPenalty_reindex_isStarProjection η hη)
  apply LinearMap.isStarProjection_iff_isSymmetricProjection.mp
  rw [isStarProjection_iff'] at hM ⊢
  constructor
  · change Matrix.toLpLin 2 2 M ∘ₗ Matrix.toLpLin 2 2 M = Matrix.toLpLin 2 2 M
    rw [← Matrix.toLpLin_mul_same, hM.1]
  · change (Matrix.toEuclideanLin M).adjoint = Matrix.toEuclideanLin M
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    have hMH : Mᴴ = M := by
      simpa only [Matrix.star_eq_conjTranspose] using hM.2
    rw [hMH]

private theorem twoSiteBondInteraction_kills_groundSpaceES_of_groundSpaceMap
    {D E : ℕ} (A : MPSTensor (D * D) E)
    (η : Fin (D * D) → ℂ)
    (hkill : ∀ X : Matrix (Fin E) (Fin E) ℂ,
      (twoSiteBondInteraction
        (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (bondPenalty η))).mulVec (groundSpaceMap A 2 X) = 0)
    (g : EuclideanSpace ℂ (Cfg (D * D) 2))
    (hg : g ∈ groundSpaceES A 2) :
    Matrix.toEuclideanLin
      (twoSiteBondInteraction
        (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (bondPenalty η))) g = 0 := by
  rw [mem_groundSpaceES_iff, groundSpace, LinearMap.mem_range] at hg
  obtain ⟨X, hX⟩ := hg
  have hgX : g = WithLp.toLp 2 (groundSpaceMap A 2 X) := by
    apply (WithLp.linearEquiv 2 ℂ (NSiteSpace (D * D) 2)).injective
    simpa using hX.symm
  rw [hgX]
  exact congrArg (WithLp.toLp 2) (hkill X)

/-- A unit bond penalty is bounded above by a two-site parent interaction
whenever it annihilates every open-boundary ground vector. -/
theorem twoSiteBondInteraction_le_parentInteractionES_of_groundSpaceMap
    {D E : ℕ} (A : MPSTensor (D * D) E)
    (η : Fin (D * D) → ℂ)
    (hη : ∑ p, Complex.normSq (η p) = 1)
    (hkill : ∀ X : Matrix (Fin E) (Fin E) ℂ,
      (twoSiteBondInteraction
        (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (bondPenalty η))).mulVec (groundSpaceMap A 2 X) = 0) :
    Matrix.toEuclideanLin
      (twoSiteBondInteraction
        (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (bondPenalty η))) ≤ parentInteractionES A 2 := by
  let B := Matrix.toEuclideanLin
    (twoSiteBondInteraction
      (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
        (bondPenalty η)))
  let G := groundSpaceES A 2
  have hB : B.IsSymmetricProjection :=
    twoSiteBondInteraction_bondPenalty_isSymmetricProjection η hη
  have hP := parentInteractionES_isSymmetricProjection A 2
  apply (hB.le_iff_range_le_range hP).mpr
  change B.range ≤ (Gᗮ.starProjection.toLinearMap).range
  rw [Submodule.range_starProjection]
  intro v hv
  obtain ⟨w, rfl⟩ := hv
  apply (G.mem_orthogonal (B w)).mpr
  intro g hg
  calc
    ⟪g, B w⟫_ℂ = ⟪B.adjoint g, w⟫_ℂ :=
      (LinearMap.adjoint_inner_left B w g).symm
    _ = 0 := by
      have hBA : B.adjoint = B :=
        (LinearMap.isSymmetric_iff_isSelfAdjoint B).mp hB.isSymmetric
      rw [hBA,
        twoSiteBondInteraction_kills_groundSpaceES_of_groundSpaceMap A η hkill g hg]
      simp

/-- The independent-bond penalty is bounded above by the canonical two-site
parent interaction of the fixed-point tensor. Source: arXiv:1010.3732,
Section II.D.2, `eq:phase-nosym:iso-hamiltonian`. -/
theorem twoSiteBondInteraction_le_parentInteractionES_sptFixedPointTensor
    (D : ℕ) (hD : 0 < D) :
    Matrix.toEuclideanLin
      (twoSiteBondInteraction
        (Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
          (bondPenalty (matrixUnitBondVector D)))) ≤
      parentInteractionES (sptFixedPointTensor D) 2 :=
  twoSiteBondInteraction_le_parentInteractionES_of_groundSpaceMap
    (sptFixedPointTensor D) (matrixUnitBondVector D)
    (matrixUnitBondVector_sum_normSq D hD)
    (twoSiteBondInteraction_groundSpaceMap_sptFixedPointTensor D hD)

end MPSTensor
