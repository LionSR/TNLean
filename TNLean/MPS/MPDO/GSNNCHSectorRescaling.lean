/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.GSNNCHOrthogonalSectors

/-!
# Fixed-length rescaling of orthogonal commuting sectors

A nonnegative scalar multiplying one sector state may be absorbed into its
positive two-site bond at any fixed positive chain length. If the chain has
length `N` and the sector has positive natural multiplicity `n`, the bond is
multiplied by the positive `N`-th root of `c / n`. The multiplicity-weighted
periodic product then acquires exactly the prescribed scalar `c`.

This construction is chainwise: the rescaled bond may depend on `N`. This is
precisely the quantifier order in the GSNNCH form of Definition 4.8.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.8, lines 829--850
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d g : ℕ} {dim : Fin g → ℕ}
  {K : (s : Fin g) → MPOTensor d (dim s)}

namespace OrthogonalCommutingSectorFamily

/-- The positive `N`-th root used to absorb a nonnegative sector coefficient
into a sector with the prescribed positive natural multiplicity. -/
noncomputable def coefficientRoot (multiplicity N : ℕ) (c : ℝ) : ℝ :=
  (c / multiplicity) ^ (N : ℝ)⁻¹

private theorem embedLocalOperator_smul
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) (c : ℂ)
    (A : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    embedLocalOperator (d := d) L N hLN i (c • A) =
      c • embedLocalOperator L N hLN i A := by
  ext σ τ
  simp [embedLocalOperator_apply]

/-- At a fixed chain length, rescale every sector bond so that its
multiplicity-weighted periodic product acquires a prescribed nonnegative real
coefficient. -/
noncomputable def toCoefficientRescaledGSNNCHData
    (F : OrthogonalCommutingSectorFamily K)
    (multiplicity : Fin g → ℕ) (hMultiplicity : ∀ s, 0 < multiplicity s)
    (coefficient : Fin g → ℝ) (hCoefficient : ∀ s, 0 ≤ coefficient s)
    (N : ℕ) (hN : 2 ≤ N) : GSNNCHData d N where
  hN := hN
  sectorCount := g
  multiplicity := multiplicity
  sectorProjection := F.projection
  sectorProjection_isOrthogonal := F.projection_isOrthogonal
  sectorProjection_orthogonal := fun hst ↦ F.projection_orthogonal hst
  bond := fun s ↦
    ((coefficientRoot (multiplicity s) N (coefficient s) : ℝ) : ℂ) •
      (F.bondData s).bond
  bond_pos := by
    intro s
    exact (F.bondData s).bond_pos.smul
      (by
        exact_mod_cast Real.rpow_nonneg
          (div_nonneg (hCoefficient s) (by exact_mod_cast (hMultiplicity s).le))
          (N : ℝ)⁻¹)
  bond_supported := by
    intro s
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [F.bond_supported s]
  neighboring_comm := by
    intro s
    simp only [embedLocalOperator_smul, Matrix.mul_smul, Matrix.smul_mul]
    rw [(F.bondData s).bond_comm hN ⟨0, by omega⟩ ⟨1, by omega⟩]

/-- The rescaled periodic bond product is `coefficient / multiplicity` times
the original sector MPO. -/
theorem toCoefficientRescaledGSNNCHData_sectorProduct
    (F : OrthogonalCommutingSectorFamily K)
    (multiplicity : Fin g → ℕ) (hMultiplicity : ∀ s, 0 < multiplicity s)
    (coefficient : Fin g → ℝ) (hCoefficient : ∀ s, 0 ≤ coefficient s)
    (N : ℕ) (hN : 2 ≤ N) (s : Fin g) :
    (F.toCoefficientRescaledGSNNCHData multiplicity hMultiplicity
      coefficient hCoefficient N hN).sectorProduct s =
      ((coefficient s / multiplicity s : ℝ) : ℂ) • mpo (K s) N := by
  simp only [GSNNCHData.sectorProduct, GSNNCHData.bondAt,
    toCoefficientRescaledGSNNCHData, embedLocalOperator_smul]
  rw [List.prod_ofFn_smul]
  have hN0 : N ≠ 0 := by omega
  have hroot :
      (coefficientRoot (multiplicity s) N (coefficient s)) ^ N =
        coefficient s / multiplicity s := by
    exact Real.rpow_inv_natCast_pow
      (div_nonneg (hCoefficient s) (Nat.cast_nonneg _)) hN0
  rw [show (∏ _i : Fin N,
      ((coefficientRoot (multiplicity s) N (coefficient s) : ℝ) : ℂ)) =
        (((coefficientRoot (multiplicity s) N (coefficient s)) ^ N : ℝ) : ℂ) by
          simp]
  rw [hroot]
  rw [F.realizes_mpo s N hN]
  rfl

/-- The state represented by the rescaled GSNNCH data is the prescribed
nonnegative linear combination of the orthogonal sector MPOs. The natural
multiplicities remain explicit in the data. -/
theorem toCoefficientRescaledGSNNCHData_unnormalizedState
    (F : OrthogonalCommutingSectorFamily K)
    (multiplicity : Fin g → ℕ) (hMultiplicity : ∀ s, 0 < multiplicity s)
    (coefficient : Fin g → ℝ) (hCoefficient : ∀ s, 0 ≤ coefficient s)
    (N : ℕ) (hN : 2 ≤ N) :
    (F.toCoefficientRescaledGSNNCHData multiplicity hMultiplicity
      coefficient hCoefficient N hN).unnormalizedState =
      ∑ s : Fin g, (coefficient s : ℂ) • mpo (K s) N := by
  rw [GSNNCHData.unnormalizedState]
  apply Finset.sum_congr rfl
  intro s _
  rw [F.toCoefficientRescaledGSNNCHData_sectorProduct
    multiplicity hMultiplicity coefficient hCoefficient N hN s]
  rw [smul_smul]
  have hm : ((multiplicity s : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (hMultiplicity s)
  change ((multiplicity s : ℂ) * (coefficient s / multiplicity s : ℝ)) •
      mpo (K s) N = _
  rw [Complex.ofReal_div, Complex.ofReal_natCast]
  field_simp

end OrthogonalCommutingSectorFamily

/-- A chainwise nonnegative linear combination of orthogonally supported
commuting sector products has the GSNNCH form with any prescribed positive
natural sector multiplicities.

The coefficients and their bond rescalings may depend on the chain length,
as permitted by Definition 4.8. -/
theorem hasGSNNCHForm_of_nonnegative_orthogonalCommutingSectorFamily
    {D : ℕ} (M : MPOTensor d D)
    (K : (s : Fin g) → MPOTensor d (dim s))
    (multiplicity : Fin g → ℕ) (hMultiplicity : ∀ s, 0 < multiplicity s)
    (F : OrthogonalCommutingSectorFamily K)
    (coefficient : ℕ → Fin g → ℝ)
    (hCoefficient : ∀ N, 2 ≤ N → ∀ s, 0 ≤ coefficient N s)
    (hM : ∀ N, 2 ≤ N →
      mpo M N = ∑ s : Fin g, (coefficient N s : ℂ) • mpo (K s) N) :
    HasGSNNCHForm M := by
  intro N hN
  let data :=
    F.toCoefficientRescaledGSNNCHData multiplicity hMultiplicity
      (coefficient N) (hCoefficient N hN) N hN
  refine ⟨data, 1, by norm_num, ?_⟩
  rw [show ((1 : ℝ) : ℂ) = 1 by norm_num, one_smul]
  change mpo M N =
    (F.toCoefficientRescaledGSNNCHData multiplicity hMultiplicity
      (coefficient N) (hCoefficient N hN) N hN).unnormalizedState
  exact (hM N hN).trans
    (F.toCoefficientRescaledGSNNCHData_unnormalizedState
      multiplicity hMultiplicity (coefficient N) (hCoefficient N hN) N hN).symm

end MPOTensor
