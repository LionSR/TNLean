/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.UnitaryEntrywiseConjugation
import TNLean.MPS.Core.BondReindex
import TNLean.MPS.Core.ReductionExistence
import TNLean.MPS.FundamentalTheorem.UnitaryGauge
import TNLean.MPS.MPU.DaggerInverse
import TNLean.MPS.MPU.PhysicalAdjointCanonicalForm
import TNLean.MPS.Symmetry.GaugeUniqueness

/-!
# Virtual gauges relating physical adjoints and group inverses

For a group representation by simple injective MPU tensors whose normalized
flattenings are left-canonical, this file constructs the unitary matrices
\(T_g\) satisfying
\[
  \mathcal U_g^\dagger=T_g^\dagger\mathcal U_{g^{-1}}T_g.
\]
It then compares the equations for \(g\) and \(g^{-1}\) to obtain
\[
  T_gT_{g^{-1}}^*=\sigma_g\mathbf 1,
\]
where the star on \(T_{g^{-1}}\) is entrywise complex conjugation.

Source: arXiv:2502.20257, equations `eq:defT` and `eq:intro_sigma`, lines
1552--1562.
-/

open scoped Matrix

namespace MPOTensor.GroupFamily

universe u

variable {G : Type u} {d : ℕ}

/-- The tensors representing \(g\) and \(g^{-1}\) have equal bond dimensions.

This is the dimension equality implicit in the gauge equation `eq:defT` of
arXiv:2502.20257, lines 1552--1557. It follows from the two rectangular
reductions supplied by injectivity, one for \(g\) and one for \(g^{-1}\). -/
theorem IsRepresentation.bondDim_inv [Group G]
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation) (g : G) :
    F.bondDim g = F.bondDim g⁻¹ := by
  obtain ⟨V₁, W₁, h₁⟩ :=
    MPSTensor.exists_isReduction_of_isInjective_of_sameMPV₂Pos
      (F.tensor g⁻¹).toMPSTensor
      (MPOTensor.physicalAdjointTensor (F.tensor g)).toMPSTensor
      (hF.isInjective g⁻¹)
      (hF.sameMPV₂Pos_physicalAdjointTensor_inv F g)
  obtain ⟨V₂, W₂, h₂⟩ :=
    MPSTensor.exists_isReduction_of_isInjective_of_sameMPV₂Pos
      (F.tensor (g⁻¹)⁻¹).toMPSTensor
      (MPOTensor.physicalAdjointTensor (F.tensor g⁻¹)).toMPSTensor
      (hF.isInjective (g⁻¹)⁻¹)
      (hF.sameMPV₂Pos_physicalAdjointTensor_inv F g⁻¹)
  exact Nat.le_antisymm (by simpa using h₂.bondDim_le) h₁.bondDim_le

/-- Reindex the tensor for \(g^{-1}\) to the bond coordinates used in the
gauge equation for \(g\).

This is the bond-space identification implicit in equation `eq:defT` of
arXiv:2502.20257, lines 1552--1557. -/
noncomputable def inverseFlattening [Group G]
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation) (g : G) :
    MPSTensor (d * d) (F.bondDim g) :=
  MPSTensor.reindex (hF.bondDim_inv F g).symm (F.tensor g⁻¹).toMPSTensor

/-- The positive-length equality between the physical adjoint and the inverse
tensor extends to all lengths after their bond dimensions have been identified.

This is the Fundamental-Theorem step in equation `eq:defT` of
arXiv:2502.20257, lines 1552--1557. -/
private theorem IsRepresentation.sameMPV_physicalAdjointTensor_inverseFlattening
    [Group G] (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation) (g : G) :
    MPSTensor.SameMPV
      (MPOTensor.physicalAdjointTensor (F.tensor g)).toMPSTensor
      (inverseFlattening F hF g) := by
  intro N ρ
  cases N with
  | zero => simp
  | succ N =>
      rw [inverseFlattening, MPSTensor.reindex_mpv]
      exact hF.sameMPV₂Pos_physicalAdjointTensor_inv F g (N + 1) (by omega) ρ

private theorem leftCanonical_reindex {D₁ D₂ : ℕ} (h : D₁ = D₂)
    (A : MPSTensor (d * d) D₁) (hA : MPSTensor.IsLeftCanonical A) :
    MPSTensor.IsLeftCanonical (MPSTensor.reindex h A) := by
  subst h
  simpa using hA

private theorem reindex_smul {D₁ D₂ : ℕ} (h : D₁ = D₂) (c : ℂ)
    (A : MPSTensor (d * d) D₁) :
    MPSTensor.reindex h (fun i ↦ c • A i) =
      fun i ↦ c • MPSTensor.reindex h A i := by
  subst h
  rfl

private theorem reindex_dependent_eq {ι : Type*} (D : ι → ℕ)
    (A : (x : ι) → MPSTensor (d * d) (D x)) {x y : ι} {E : ℕ}
    (hxy : x = y) (h₁ : D x = E) (h₂ : D y = E) :
    MPSTensor.reindex h₁ (A x) = MPSTensor.reindex h₂ (A y) := by
  subst hxy
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  subst hh
  rfl

private noncomputable def unitaryReindex {D₁ D₂ : ℕ} (h : D₁ = D₂)
    (U : Matrix.unitaryGroup (Fin D₁) ℂ) :
    Matrix.unitaryGroup (Fin D₂) ℂ :=
  ⟨Matrix.reindex (finCongr h) (finCongr h) U,
    Matrix.reindex_mem_unitaryGroup (finCongr h) U U.property⟩

private theorem unitaryReindex_dependent_eq {ι : Type*} (D : ι → ℕ)
    (U : (x : ι) → Matrix.unitaryGroup (Fin (D x)) ℂ) {x y : ι} {E : ℕ}
    (hxy : x = y) (h₁ : D x = E) (h₂ : D y = E) :
    unitaryReindex h₁ (U x) = unitaryReindex h₂ (U y) := by
  subst hxy
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  subst hh
  rfl

@[simp] private theorem unitaryReindex_self {D : ℕ} (h : D = D)
    (U : Matrix.unitaryGroup (Fin D) ℂ) :
    unitaryReindex h U = U := by
  have hh : h = rfl := Subsingleton.elim _ _
  subst hh
  ext i j
  rfl

/-- A nonzero common scalar normalization does not affect the unitary gauge
between two injective tensors.  This supplies the canonical-form unitarity in
equation `eq:defT` of arXiv:2502.20257, lines 1554--1557. -/
private theorem exists_unitaryConj_of_gaugeEquiv_of_smul_leftCanonical
    {D : ℕ} [NeZero D] {A B : MPSTensor (d * d) D} {c : ℂ}
    (hc : c ≠ 0) (hA : Kraus.IsInjective A) (h : MPSTensor.GaugeEquiv A B)
    (hAleft : MPSTensor.IsLeftCanonical (fun i ↦ c • A i))
    (hBleft : MPSTensor.IsLeftCanonical (fun i ↦ c • B i)) :
    ∃ U : Matrix.unitaryGroup (Fin D) ℂ,
      ∀ i, B i = (U : Matrix (Fin D) (Fin D) ℂ) * A i *
        (U : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  obtain ⟨X, hX⟩ := h
  have hB : Kraus.IsInjective B :=
    MPSTensor.isInjective_of_gaugeEquiv hA ⟨X, hX⟩
  have hAc : Kraus.IsInjective (fun i ↦ c • A i) := hA.smul hc
  have hBc : Kraus.IsInjective (fun i ↦ c • B i) := hB.smul hc
  have hAc_irr : Kraus.IsIrreducibleFamily (fun i ↦ c • A i) :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM _
      (Kraus.injective_implies_irreducibleCP _ hAc)
  have hBc_irr : Kraus.IsIrreducibleFamily (fun i ↦ c • B i) :=
    Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM _
      (Kraus.injective_implies_irreducibleCP _ hBc)
  have hcGauge : ∀ i,
      c • B i = (1 : ℂ) • ((X : Matrix (Fin D) (Fin D) ℂ) * (c • A i) *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
    intro i
    simpa only [one_smul, mul_smul_comm, smul_mul_assoc] using
      congrArg (c • ·) (hX i)
  obtain ⟨U, _hOne, hU⟩ :=
    MPSTensor.exists_unitaryConj_of_gaugePhase_data_of_leftCanonical_irreducible
      X 1 one_ne_zero hcGauge hAleft hBleft hAc_irr hBc_irr
  refine ⟨U, fun i ↦ ?_⟩
  have hi : c • B i = c • ((U : Matrix (Fin D) (Fin D) ℂ) * A i *
      (U : Matrix (Fin D) (Fin D) ℂ)ᴴ) := by
    simpa only [one_smul, mul_smul_comm, smul_mul_assoc] using hU i
  have hi' := congrArg (c⁻¹ • ·) hi
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi'

/-- There is a unitary virtual matrix \(T_g\) satisfying
\(\mathcal U_g^\dagger=T_g^\dagger\mathcal U_{g^{-1}}T_g\).

Canonicality is the explicit hypothesis that every normalized flattening is
left-canonical. This is equation `eq:defT` of arXiv:2502.20257, lines
1552--1557. -/
theorem IsRepresentation.exists_daggerInverseGauge [Group G]
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) :
    ∃ T : Matrix.unitaryGroup (Fin (F.bondDim g)) ℂ,
      ∀ i,
        (MPOTensor.physicalAdjointTensor (F.tensor g)).toMPSTensor i =
          (T : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ)ᴴ *
            inverseFlattening F hF g i *
            (T : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) := by
  let A : MPSTensor (d * d) (F.bondDim g) := inverseFlattening F hF g
  let B : MPSTensor (d * d) (F.bondDim g) :=
    (MPOTensor.physicalAdjointTensor (F.tensor g)).toMPSTensor
  have hA : Kraus.IsInjective A := by
    simp only [A, inverseFlattening, MPSTensor.isInjective_reindex]
    exact hF.isInjective g⁻¹
  have hSame : MPSTensor.SameMPV A B := by
    intro N ρ
    exact (hF.sameMPV_physicalAdjointTensor_inverseFlattening F g N ρ).symm
  have hGauge : MPSTensor.GaugeEquiv A B :=
    MPSTensor.fundamentalTheorem_singleBlock hA hSame
  have hd : d ≠ 0 := by
    let hdd : NeZero (d * d) := Kraus.neZero_d_of_isInjective (hF.isInjective g)
    intro hd
    exact hdd.out (Nat.mul_eq_zero.mpr (Or.inl hd))
  have hsqrt : (Real.sqrt d : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero hd)).ne'
  have hc : ((Real.sqrt d : ℂ)⁻¹) ≠ 0 := inv_ne_zero hsqrt
  have hAleft : MPSTensor.IsLeftCanonical
      (fun i ↦ ((Real.sqrt d : ℂ)⁻¹) • A i) := by
    change MPSTensor.IsLeftCanonical
      (fun i ↦ ((Real.sqrt d : ℂ)⁻¹) •
        MPSTensor.reindex (hF.bondDim_inv F g).symm
          (F.tensor g⁻¹).toMPSTensor i)
    rw [← reindex_smul]
    exact leftCanonical_reindex (hF.bondDim_inv F g).symm
      (F.tensor g⁻¹).normalizedFlattening (hcanonical g⁻¹)
  have hBcanonical : MPSTensor.IsLeftCanonical
      (MPOTensor.physicalAdjointTensor (F.tensor g)).normalizedFlattening := by
    rw [MPOTensor.normalizedFlattening_physicalAdjointTensor]
    exact (MPSTensor.leftCanonical_reindexPhysical_equiv
      (MPOTensor.physicalPairSwapEquiv d) _).2 ((hcanonical g).mapStar)
  have hBleft : MPSTensor.IsLeftCanonical
      (fun i ↦ ((Real.sqrt d : ℂ)⁻¹) • B i) := by
    change MPSTensor.IsLeftCanonical
      (MPOTensor.physicalAdjointTensor (F.tensor g)).normalizedFlattening
    exact hBcanonical
  obtain ⟨U, hU⟩ :=
    exists_unitaryConj_of_gaugeEquiv_of_smul_leftCanonical
      hc hA hGauge hAleft hBleft
  refine ⟨U⁻¹, fun i ↦ ?_⟩
  simpa [A, B, Matrix.star_eq_conjTranspose] using hU i

/-- The chosen unitary virtual matrix \(T_g\) in equation `eq:defT` of
arXiv:2502.20257, lines 1552--1557. -/
noncomputable def IsRepresentation.daggerInverseGauge [Group G]
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) : Matrix.unitaryGroup (Fin (F.bondDim g)) ℂ :=
  Classical.choose (hF.exists_daggerInverseGauge F hcanonical g)

/-- The chosen virtual gauge satisfies equation `eq:defT` of
arXiv:2502.20257, lines 1552--1557. -/
theorem IsRepresentation.physicalAdjointTensor_eq_daggerInverseGauge [Group G]
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) (i : Fin (d * d)) :
    (MPOTensor.physicalAdjointTensor (F.tensor g)).toMPSTensor i =
      (hF.daggerInverseGauge F hcanonical g :
          Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ)ᴴ *
        inverseFlattening F hF g i *
        (hF.daggerInverseGauge F hcanonical g :
          Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) :=
  Classical.choose_spec (hF.exists_daggerInverseGauge F hcanonical g) i

/-- Reindex \(T_{g^{-1}}\) to the bond coordinates used by \(T_g\).

This is the bond-space identification in equation `eq:intro_sigma` of
arXiv:2502.20257, lines 1557--1562. -/
noncomputable def IsRepresentation.inverseDaggerInverseGauge [Group G]
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) : Matrix.unitaryGroup (Fin (F.bondDim g)) ℂ :=
  unitaryReindex (hF.bondDim_inv F g).symm
    (hF.daggerInverseGauge F hcanonical g⁻¹)

/-- The physical adjoint on a flattened tensor: exchange the two physical
coordinates and conjugate every virtual matrix entry.

This is the tensor operation used between equations `eq:defT` and
`eq:intro_sigma` of arXiv:2502.20257, lines 1557--1562. -/
private noncomputable def flattenedPhysicalAdjoint {D : ℕ}
    (A : MPSTensor (d * d) D) : MPSTensor (d * d) D :=
  Kraus.reindexPhysical (MPOTensor.physicalPairSwapEquiv d) (MPSTensor.mapStar A)

/-- Applying the flattened physical adjoint twice returns the original tensor;
this is used in the passage from `eq:defT` to `eq:intro_sigma` in
arXiv:2502.20257, lines 1557--1562. -/
private theorem flattenedPhysicalAdjoint_involutive {D : ℕ}
    (A : MPSTensor (d * d) D) :
    flattenedPhysicalAdjoint (d := d) (flattenedPhysicalAdjoint (d := d) A) = A := by
  ext ij β α
  rw [show ij = finProdFinEquiv (ij.divNat, ij.modNat) by
    exact (finProdFinEquiv.apply_symm_apply ij).symm]
  simp [flattenedPhysicalAdjoint, Kraus.reindexPhysical, MPSTensor.mapStar,
    Matrix.map_apply]

/-- The flattened operation is the physical-adjoint tensor of `eq:defT` in
arXiv:2502.20257, lines 1552--1557. -/
private theorem flattenedPhysicalAdjoint_toMPSTensor {D : ℕ}
    (U : MPOTensor d D) :
    flattenedPhysicalAdjoint (d := d) U.toMPSTensor =
      (MPOTensor.physicalAdjointTensor U).toMPSTensor := by
  ext ij β α
  rw [show ij = finProdFinEquiv (ij.divNat, ij.modNat) by
    exact (finProdFinEquiv.apply_symm_apply ij).symm]
  simp [flattenedPhysicalAdjoint, Kraus.reindexPhysical, MPSTensor.mapStar,
    MPOTensor.toMPSTensor, Matrix.map_apply]

/-- Taking the flattened physical adjoint of one unitary-gauge equation gives
the oppositely oriented gauge with the entrywise-conjugate unitary.  This is
the conjugation step between `eq:defT` and `eq:intro_sigma` in
arXiv:2502.20257, lines 1557--1562. -/
private theorem flattenedPhysicalAdjoint_gauge_symm {D : ℕ}
    (A B : MPSTensor (d * d) D) (S : Matrix.unitaryGroup (Fin D) ℂ)
    (hS : ∀ i,
      flattenedPhysicalAdjoint (d := d) B i =
        (S : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i *
          (S : Matrix (Fin D) (Fin D) ℂ)) :
    ∀ i,
      flattenedPhysicalAdjoint (d := d) A i =
        (Matrix.UnitaryGroup.map_star S : Matrix (Fin D) (Fin D) ℂ) * B i *
          (((Matrix.UnitaryGroup.map_star S)⁻¹ : Matrix.unitaryGroup (Fin D) ℂ) :
            Matrix (Fin D) (Fin D) ℂ) := by
  classical
  intro i
  let Sstar := Matrix.UnitaryGroup.map_star S
  have hFirst :
      ((S : Matrix (Fin D) (Fin D) ℂ)ᴴ).map (starRingEnd ℂ) =
        ((Sstar⁻¹ : Matrix.unitaryGroup (Fin D) ℂ) :
          Matrix (Fin D) (Fin D) ℂ) := by
    rw [show (Sstar⁻¹ : Matrix.unitaryGroup (Fin D) ℂ) =
      Matrix.UnitaryGroup.transpose S by
        exact Matrix.UnitaryGroup.map_star_inv_eq_transpose S]
    ext β α
    simp [Matrix.conjTranspose_apply, Matrix.map_apply]
  have hLeft :
      (flattenedPhysicalAdjoint (d := d) B
        (MPOTensor.physicalPairSwapEquiv d i)).map (starRingEnd ℂ) = B i := by
    change flattenedPhysicalAdjoint (d := d)
      (flattenedPhysicalAdjoint (d := d) B) i = B i
    exact congrFun (flattenedPhysicalAdjoint_involutive B) i
  have hRight :
      (((S : Matrix (Fin D) (Fin D) ℂ)ᴴ *
          A (MPOTensor.physicalPairSwapEquiv d i) *
          (S : Matrix (Fin D) (Fin D) ℂ))).map (starRingEnd ℂ) =
        ((Sstar⁻¹ : Matrix.unitaryGroup (Fin D) ℂ) :
          Matrix (Fin D) (Fin D) ℂ) *
          flattenedPhysicalAdjoint (d := d) A i *
          (Sstar : Matrix (Fin D) (Fin D) ℂ) := by
    rw [Matrix.map_mul, Matrix.map_mul, hFirst]
    rfl
  have hMap := congrArg
    (fun M : Matrix (Fin D) (Fin D) ℂ ↦ M.map (starRingEnd ℂ))
    (hS (MPOTensor.physicalPairSwapEquiv d i))
  have hBi : B i =
      ((Sstar⁻¹ : Matrix.unitaryGroup (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) *
        flattenedPhysicalAdjoint (d := d) A i *
        (Sstar : Matrix (Fin D) (Fin D) ℂ) := by
    calc
      B i =
          (flattenedPhysicalAdjoint (d := d) B
            (MPOTensor.physicalPairSwapEquiv d i)).map (starRingEnd ℂ) := hLeft.symm
      _ = (((S : Matrix (Fin D) (Fin D) ℂ)ᴴ *
          A (MPOTensor.physicalPairSwapEquiv d i) *
          (S : Matrix (Fin D) (Fin D) ℂ))).map (starRingEnd ℂ) := hMap
      _ = _ := hRight
  have hInv : (Sstar : Matrix (Fin D) (Fin D) ℂ) *
      ((Sstar⁻¹ : Matrix.unitaryGroup (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = 1 := by
    simp
  have hResult : flattenedPhysicalAdjoint (d := d) A i =
      (Sstar : Matrix (Fin D) (Fin D) ℂ) * B i *
        ((Sstar⁻¹ : Matrix.unitaryGroup (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    calc
      flattenedPhysicalAdjoint (d := d) A i =
          1 * flattenedPhysicalAdjoint (d := d) A i * 1 := by simp
      _ = ((Sstar : Matrix (Fin D) (Fin D) ℂ) *
            ((Sstar⁻¹ : Matrix.unitaryGroup (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) *
          flattenedPhysicalAdjoint (d := d) A i *
            ((Sstar : Matrix (Fin D) (Fin D) ℂ) *
              ((Sstar⁻¹ : Matrix.unitaryGroup (Fin D) ℂ) :
                Matrix (Fin D) (Fin D) ℂ)) := by rw [hInv]
      _ = (Sstar : Matrix (Fin D) (Fin D) ℂ) *
            (((Sstar⁻¹ : Matrix.unitaryGroup (Fin D) ℂ) :
                Matrix (Fin D) (Fin D) ℂ) *
              flattenedPhysicalAdjoint (d := d) A i *
              (Sstar : Matrix (Fin D) (Fin D) ℂ)) *
            ((Sstar⁻¹ : Matrix.unitaryGroup (Fin D) ℂ) :
              Matrix (Fin D) (Fin D) ℂ) := by simp only [Matrix.mul_assoc]
      _ = (Sstar : Matrix (Fin D) (Fin D) ℂ) * B i *
            ((Sstar⁻¹ : Matrix.unitaryGroup (Fin D) ℂ) :
              Matrix (Fin D) (Fin D) ℂ) := by rw [hBi]
  simpa only [Sstar] using hResult

private theorem flattenedPhysicalAdjoint_reindex_gauge {D₁ D₂ : ℕ}
    (h : D₁ = D₂) (A : MPSTensor (d * d) D₁) (B : MPSTensor (d * d) D₂)
    (T : Matrix.unitaryGroup (Fin D₂) ℂ)
    (hT : ∀ i,
      flattenedPhysicalAdjoint (d := d) B i =
        (T : Matrix (Fin D₂) (Fin D₂) ℂ)ᴴ * MPSTensor.reindex h A i *
          (T : Matrix (Fin D₂) (Fin D₂) ℂ)) :
    ∀ i,
      flattenedPhysicalAdjoint (d := d) (MPSTensor.reindex h.symm B) i =
        (unitaryReindex h.symm T : Matrix (Fin D₁) (Fin D₁) ℂ)ᴴ * A i *
          (unitaryReindex h.symm T : Matrix (Fin D₁) (Fin D₁) ℂ) := by
  subst h
  simpa using hT

/-- The equation `eq:defT` at \(g^{-1}\), transported to the bond coordinates
of \(g\) and physically adjointed as in arXiv:2502.20257, lines 1557--1562. -/
private theorem IsRepresentation.flattenedPhysicalAdjoint_inverseFlattening
    [Group G] (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) (i : Fin (d * d)) :
    flattenedPhysicalAdjoint (d := d) (inverseFlattening F hF g) i =
      (hF.inverseDaggerInverseGauge F hcanonical g :
          Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ)ᴴ *
        (F.tensor g).toMPSTensor i *
        (hF.inverseDaggerInverseGauge F hcanonical g :
          Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) := by
  classical
  let hD := hF.bondDim_inv F g
  apply flattenedPhysicalAdjoint_reindex_gauge hD
      (F.tensor g).toMPSTensor (F.tensor g⁻¹).toMPSTensor
      (hF.daggerInverseGauge F hcanonical g⁻¹) _ i
  intro j
  have hinverse : inverseFlattening F hF g⁻¹ =
      MPSTensor.reindex hD (F.tensor g).toMPSTensor := by
    exact reindex_dependent_eq (fun x ↦ F.bondDim x)
      (fun x ↦ (F.tensor x).toMPSTensor) (inv_inv g)
      (hF.bondDim_inv F g⁻¹).symm hD
  have hbase :=
    hF.physicalAdjointTensor_eq_daggerInverseGauge F hcanonical g⁻¹ j
  rw [hinverse] at hbase
  simpa [flattenedPhysicalAdjoint_toMPSTensor] using hbase

/-- There is a scalar \(\sigma_g\) such that
\(T_gT_{g^{-1}}^*=\sigma_g\mathbf 1\), where the star is entrywise complex
conjugation.

This is equation `eq:intro_sigma` of arXiv:2502.20257, lines 1557--1562. -/
theorem IsRepresentation.exists_daggerInverseScalar [Group G]
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) :
    ∃ σ : ℂ,
      (hF.daggerInverseGauge F hcanonical g :
          Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) *
        (hF.inverseDaggerInverseGauge F hcanonical g :
          Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ).map
            (starRingEnd ℂ) = σ • 1 := by
  let A : MPSTensor (d * d) (F.bondDim g) := inverseFlattening F hF g
  let B : MPSTensor (d * d) (F.bondDim g) :=
    (MPOTensor.physicalAdjointTensor (F.tensor g)).toMPSTensor
  let T := hF.daggerInverseGauge F hcanonical g
  let S := hF.inverseDaggerInverseGauge F hcanonical g
  let X : GL (Fin (F.bondDim g)) ℂ := Unitary.toUnits T⁻¹
  let Y : GL (Fin (F.bondDim g)) ℂ :=
    Unitary.toUnits (Matrix.UnitaryGroup.map_star S)
  have hA : Kraus.IsInjective A := by
    simp only [A, inverseFlattening, MPSTensor.isInjective_reindex]
    exact hF.isInjective g⁻¹
  have hX : ∀ i, B i =
      (X : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) * A i *
        ((X⁻¹ : GL (Fin (F.bondDim g)) ℂ) :
          Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) := by
    intro i
    simpa [A, B, T, X, Matrix.star_eq_conjTranspose] using
      hF.physicalAdjointTensor_eq_daggerInverseGauge F hcanonical g i
  have hS : ∀ i,
      flattenedPhysicalAdjoint (d := d) A i =
        (S : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ)ᴴ *
          (F.tensor g).toMPSTensor i *
          (S : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) := by
    intro i
    exact hF.flattenedPhysicalAdjoint_inverseFlattening F hcanonical g i
  have hY' := flattenedPhysicalAdjoint_gauge_symm
    (d := d) (F.tensor g).toMPSTensor A S hS
  have hY : ∀ i, B i =
      (Y : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) * A i *
        ((Y⁻¹ : GL (Fin (F.bondDim g)) ℂ) :
          Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) := by
    intro i
    change (MPOTensor.physicalAdjointTensor (F.tensor g)).toMPSTensor i = _
    rw [← flattenedPhysicalAdjoint_toMPSTensor]
    simpa [Y] using hY' i
  obtain ⟨u, hu⟩ := MPSTensor.gauge_unique_up_to_scalar hA hX hY
  refine ⟨(u : ℂ), ?_⟩
  have hu' :
      (Matrix.UnitaryGroup.map_star S :
          Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) =
        (u : ℂ) •
          ((T⁻¹ : Matrix.unitaryGroup (Fin (F.bondDim g)) ℂ) :
            Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) := by
    simpa [X, Y] using hu
  calc
    (T : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) *
          (S : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ).map
            (starRingEnd ℂ) =
        (T : Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) *
          ((u : ℂ) •
            ((T⁻¹ : Matrix.unitaryGroup (Fin (F.bondDim g)) ℂ) :
              Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ)) := by
              rw [← hu']
              rfl
    _ = (u : ℂ) • 1 := by simp

/-- The scalar \(\sigma_g\) in equation `eq:intro_sigma` of
arXiv:2502.20257, lines 1557--1562. -/
noncomputable def IsRepresentation.daggerInverseScalar [Group G]
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) : ℂ :=
  Classical.choose (hF.exists_daggerInverseScalar F hcanonical g)

/-- The chosen scalar \(\sigma_g\) satisfies equation `eq:intro_sigma` of
arXiv:2502.20257, lines 1557--1562. -/
theorem IsRepresentation.daggerInverseGauge_mul_mapStar_inverse_eq_smul_one
    [Group G] (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) :
    (hF.daggerInverseGauge F hcanonical g :
        Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) *
      (hF.inverseDaggerInverseGauge F hcanonical g :
        Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ).map
          (starRingEnd ℂ) =
        hF.daggerInverseScalar F hcanonical g • 1 :=
  Classical.choose_spec (hF.exists_daggerInverseScalar F hcanonical g)

private theorem unitaryReindex_mul_mapStar_of_mul_mapStar_reindex
    {D₁ D₂ : ℕ} (h : D₁ = D₂)
    (T : Matrix.unitaryGroup (Fin D₂) ℂ)
    (S : Matrix.unitaryGroup (Fin D₁) ℂ) (σ : ℂ)
    (hscalar :
      (T : Matrix (Fin D₂) (Fin D₂) ℂ) *
        (unitaryReindex h S : Matrix (Fin D₂) (Fin D₂) ℂ).map
          (starRingEnd ℂ) = σ • 1) :
    (unitaryReindex h.symm T : Matrix (Fin D₁) (Fin D₁) ℂ) *
      (S : Matrix (Fin D₁) (Fin D₁) ℂ).map (starRingEnd ℂ) = σ • 1 := by
  subst h
  simpa using hscalar

/-- Equation `eq:intro_sigma` at \(g^{-1}\), transported to the bond coordinates
of \(g\), as in arXiv:2502.20257, lines 1559--1563. -/
private theorem IsRepresentation.inverseDaggerInverseGauge_mul_mapStar_eq_smul_one
    [Group G] (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) :
    (hF.inverseDaggerInverseGauge F hcanonical g :
        Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ) *
      (hF.daggerInverseGauge F hcanonical g :
        Matrix (Fin (F.bondDim g)) (Fin (F.bondDim g)) ℂ).map
          (starRingEnd ℂ) =
        hF.daggerInverseScalar F hcanonical g⁻¹ • 1 := by
  classical
  let hD := hF.bondDim_inv F g
  apply unitaryReindex_mul_mapStar_of_mul_mapStar_reindex hD
      (hF.daggerInverseGauge F hcanonical g⁻¹)
      (hF.daggerInverseGauge F hcanonical g)
      (hF.daggerInverseScalar F hcanonical g⁻¹)
  have hinverse : hF.inverseDaggerInverseGauge F hcanonical g⁻¹ =
      unitaryReindex hD (hF.daggerInverseGauge F hcanonical g) := by
    exact unitaryReindex_dependent_eq (fun x ↦ F.bondDim x)
      (fun x ↦ hF.daggerInverseGauge F hcanonical x) (inv_inv g)
      (hF.bondDim_inv F g⁻¹).symm hD
  have hbase :=
    hF.daggerInverseGauge_mul_mapStar_inverse_eq_smul_one F hcanonical g⁻¹
  rw [hinverse] at hbase
  exact hbase

/-- The scalar \(\sigma_g\) has unit modulus, written as
\(\sigma_g\overline{\sigma_g}=1\).

This is the unit-circle assertion following equation `eq:intro_sigma` in
arXiv:2502.20257, lines 1559--1562. -/
theorem IsRepresentation.daggerInverseScalar_mul_star_eq_one [Group G]
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) :
    hF.daggerInverseScalar F hcanonical g *
      starRingEnd ℂ (hF.daggerInverseScalar F hcanonical g) = 1 :=
  Matrix.scalar_mul_star_eq_one_of_mul_map_star_eq_smul_one
    (hF.daggerInverseGauge F hcanonical g)
    (hF.inverseDaggerInverseGauge F hcanonical g)
    (hF.daggerInverseScalar F hcanonical g)
    (hF.daggerInverseGauge_mul_mapStar_inverse_eq_smul_one F hcanonical g)

/-- The scalar \(\sigma_g\) has complex norm one.

This is the assertion \(\sigma_g\in U(1)\) following equation
`eq:intro_sigma` in arXiv:2502.20257, lines 1559--1562. -/
theorem IsRepresentation.norm_daggerInverseScalar [Group G]
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) : ‖hF.daggerInverseScalar F hcanonical g‖ = 1 := by
  let σ := hF.daggerInverseScalar F hcanonical g
  have h := hF.daggerInverseScalar_mul_star_eq_one F hcanonical g
  change σ * starRingEnd ℂ σ = 1 at h
  rw [Complex.mul_conj] at h
  have hnormSq : Complex.normSq σ = 1 := by exact_mod_cast h
  change ‖σ‖ = 1
  nlinarith [Complex.sq_norm σ, norm_nonneg σ]

/-- The scalars for inverse group elements satisfy
\(\sigma_g\sigma_{g^{-1}}=1\).

This is the reciprocal relation following equation `eq:intro_sigma` in
arXiv:2502.20257, lines 1559--1562. -/
theorem IsRepresentation.daggerInverseScalar_mul_inverse_eq_one [Group G]
    (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) :
    hF.daggerInverseScalar F hcanonical g *
      hF.daggerInverseScalar F hcanonical g⁻¹ = 1 :=
  Matrix.paired_scalars_mul_eq_one_of_mul_map_star_eq_smul_one
    (hF.daggerInverseGauge F hcanonical g)
    (hF.inverseDaggerInverseGauge F hcanonical g)
    (hF.daggerInverseScalar F hcanonical g)
    (hF.daggerInverseScalar F hcanonical g⁻¹)
    (hF.daggerInverseGauge_mul_mapStar_inverse_eq_smul_one F hcanonical g)
    (hF.inverseDaggerInverseGauge_mul_mapStar_eq_smul_one F hcanonical g)

/-- If \(g=g^{-1}\), then the scalar \(\sigma_g\) is \(1\) or \(-1\).

This is the involution conclusion following equation `eq:intro_sigma` in
arXiv:2502.20257, lines 1563--1567. -/
theorem IsRepresentation.daggerInverseScalar_eq_one_or_neg_one_of_inv_eq
    [Group G] (F : MPOTensor.GroupFamily G d) (hF : F.IsRepresentation)
    (hcanonical : ∀ g : G,
      MPSTensor.IsLeftCanonical (F.tensor g).normalizedFlattening)
    (g : G) (hg : g⁻¹ = g) :
    hF.daggerInverseScalar F hcanonical g = 1 ∨
      hF.daggerInverseScalar F hcanonical g = -1 := by
  apply sq_eq_one_iff.mp
  rw [pow_two]
  simpa only [hg] using
    hF.daggerInverseScalar_mul_inverse_eq_one F hcanonical g

end MPOTensor.GroupFamily
