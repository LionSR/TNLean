/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CyclicActiveRetainedCoordinates
import TNLean.MPS.MPDO.FixedBondProductEtaTensor
import TNLean.MPS.CanonicalForm.Definitions

/-!
# Visibility of selected fixed-product sectors

This file compares the positive physical sectors of the selected fixed-product
tensor with the original injective tensor in the same physical coordinates.

## Reference

* arXiv:1606.00608, Appendix C.2, Proposition 4to2, lines 1597--1619.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor.EtaLocalStructureData

variable {d D : ℕ} {K : MPOTensor d D}

/-- In the physical coordinates of the selected fixed-product factorization,
the original tensor and the selected tensor have proportional periodic
operators at every length at least two.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1605.

**Scope restriction (selected-sector visibility):** The positive realization scalar
is retained. No virtual comparison between the two tensors is asserted. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem exists_positive_scalar_mpo_changePhysicalBasis_eq_smul_selected
    (data : EtaLocalStructureData K) (N : ℕ) (hN : 2 ≤ N) :
    ∃ c : ℝ, 0 < c ∧
      mpo (PhysicalSectorFactorization.changePhysicalBasis
        (data.bondData.fixedProductTensorDataPhysicalSectorFactorization
          |>.physicalCoordinateMatrix) K) N =
        (c : ℂ) •
          mpo (data.bondData.fixedProductTensorDataPhysicalSectorFactorization
            |>.sectorCoordinateTensor) N := by
  obtain ⟨c, hc, hreal⟩ := data.realizes_mpo N hN
  refine ⟨c, hc, ?_⟩
  let F := data.bondData.fixedProductTensorDataPhysicalSectorFactorization
  change mpo (PhysicalSectorFactorization.changePhysicalBasis
    F.physicalCoordinateMatrix K) N = (c : ℂ) • mpo F.sectorCoordinateTensor N
  rw [F.sectorCoordinateTensor_eq_changePhysicalBasis]
  rw [← singleKrausMap_sitewisePhysicalMatrix_mpo]
  rw [hreal]
  rw [(singleKrausMap _).map_smul]
  rw [← data.bondData.fixedProductTensorData.mpo_eq_product N hN]
  rw [singleKrausMap_sitewisePhysicalMatrix_mpo]

end MPOTensor.EtaLocalStructureData

namespace MPOTensor.PhysicalSectorFactorization

variable {d D E : ℕ} {K : MPOTensor d D} {C : MPOTensor d E}

/-- Changing an injective tensor to the physical coordinates of any
physical-sector factorization preserves injectivity.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1605.

**Scope restriction (selected-sector visibility):** The coordinate matrix is unitary
on the physical space; no virtual map between the two tensor carriers is used.
See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem changePhysicalBasis_physicalCoordinateMatrix_isInjective
    (F : PhysicalSectorFactorization C) (hK : K.IsInjective) :
    (changePhysicalBasis F.physicalCoordinateMatrix K).IsInjective := by
  apply MPOTensor.isInjective_of_eq_changePhysicalBasis
    F.physicalCoordinateMatrixᴴ _ K ?_ hK
  rw [changePhysicalBasis_changePhysicalBasis,
    F.physicalCoordinateMatrix_isometry]
  ext i j beta alpha
  simp [changePhysicalBasis, physicalSlice]

/-- A matrix from a non-cyclic-active sector has zero trace pairing with every
one-site matrix of the factorized tensor.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1603--1617.

**Scope restriction (selected-sector visibility):** The length-two cyclic contraction
vanishes because at least one orientation of every two-edge cycle through the
sector is absent. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem trace_sectorCoordinateTensor_mul_eq_zero_of_not_isCyclicActiveSector
    (F : PhysicalSectorFactorization C)
    {k : Fin F.sectorCount} (hk : ¬ F.IsCyclicActiveSector k)
    (x y : F.SectorIndex k)
    (u v : Fin (Fintype.card F.SectorSiteIndex)) :
    Matrix.trace
      (F.sectorCoordinateTensor (F.sectorFinEquiv.symm ⟨k, x⟩)
        (F.sectorFinEquiv.symm ⟨k, y⟩) *
        F.sectorCoordinateTensor u v) = 0 := by
  generalize hu : F.sectorFinEquiv u = su
  generalize hv : F.sectorFinEquiv v = sv
  obtain ⟨r, a⟩ := su
  obtain ⟨s, b⟩ := sv
  have hu' : u = F.sectorFinEquiv.symm ⟨r, a⟩ := by
    apply F.sectorFinEquiv.injective
    rw [Equiv.apply_symm_apply, hu]
  have hv' : v = F.sectorFinEquiv.symm ⟨s, b⟩ := by
    apply F.sectorFinEquiv.injective
    rw [Equiv.apply_symm_apply, hv]
  subst u
  subst v
  by_cases hrs : r = s
  · subst s
    have hedge : F.neighboringOperator k r = 0 ∨
        F.neighboringOperator r k = 0 := by
      by_contra h
      push Not at h
      exact hk ⟨r, h.1, Relation.ReflTransGen.single h.2⟩
    rcases hedge with hkr | hrk
    · have hprod :=
        F.oneSiteSectorMatrix_mul_eq_zero_of_neighboringOperator_eq_zero
          k r hkr x y a b
      have htrace := congrArg Matrix.trace hprod
      simpa [oneSiteSectorMatrix] using htrace
    · rw [Matrix.trace_mul_comm]
      have hprod :=
        F.oneSiteSectorMatrix_mul_eq_zero_of_neighboringOperator_eq_zero
          r k hrk a b x y
      have htrace := congrArg Matrix.trace hprod
      simpa [oneSiteSectorMatrix] using htrace
  · have hzero : F.sectorCoordinateTensor
        (F.sectorFinEquiv.symm ⟨r, a⟩)
        (F.sectorFinEquiv.symm ⟨s, b⟩) = 0 := by
      ext beta alpha
      exact F.sectorCoordinateTensor_apply_ne hrs a b beta alpha
    rw [hzero, Matrix.mul_zero, Matrix.trace_zero]

/-- A cross-sector physical matrix of the original injective tensor vanishes
when its two-site periodic operator is proportional to that of the selected
factorized tensor.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1605.

**Scope restriction (selected-sector visibility):** This is a conclusion about the
original tensor in the selected physical coordinates, obtained from the
length-two closed operator and trace-pairing nondegeneracy. No virtual
comparison is assumed. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem changePhysicalBasis_apply_ne_eq_zero_of_mpo_two_eq_smul
    (F : PhysicalSectorFactorization C) (hK : K.IsInjective) (c : ℂ)
    (hmpo : mpo (changePhysicalBasis F.physicalCoordinateMatrix K) 2 =
      c • mpo F.sectorCoordinateTensor 2)
    {k h : Fin F.sectorCount} (hkh : k ≠ h)
    (x : F.SectorIndex k) (y : F.SectorIndex h) :
    changePhysicalBasis F.physicalCoordinateMatrix K
        (F.sectorFinEquiv.symm ⟨k, x⟩)
        (F.sectorFinEquiv.symm ⟨h, y⟩) = 0 := by
  let M := changePhysicalBasis F.physicalCoordinateMatrix K
  have hM : M.IsInjective :=
    F.changePhysicalBasis_physicalCoordinateMatrix_isInjective hK
  change M (F.sectorFinEquiv.symm ⟨k, x⟩)
    (F.sectorFinEquiv.symm ⟨h, y⟩) = 0
  apply (LinearMap.ker_eq_bot'.1
    (MPSTensor.traceMulRightPi_ker_eq_bot hM))
  funext p
  rw [MPSTensor.traceMulRightPi_apply, Pi.zero_apply]
  set u := p.divNat
  set v := p.modNat
  change Matrix.trace
    (M (F.sectorFinEquiv.symm ⟨k, x⟩)
      (F.sectorFinEquiv.symm ⟨h, y⟩) * M u v) = 0
  have h2 := congrFun (congrFun hmpo
    (Fin.cons (F.sectorFinEquiv.symm ⟨k, x⟩)
      (fun _ : Fin 1 ↦ u)))
    (Fin.cons (F.sectorFinEquiv.symm ⟨h, y⟩)
      (fun _ : Fin 1 ↦ v))
  have hCzero : F.sectorCoordinateTensor
      (F.sectorFinEquiv.symm ⟨k, x⟩)
      (F.sectorFinEquiv.symm ⟨h, y⟩) = 0 := by
    ext beta alpha
    exact F.sectorCoordinateTensor_apply_ne hkh x y beta alpha
  simp [mpo_apply, mpoMatrixEntry, List.ofFn_succ, hCzero] at h2
  simpa [M] using h2

/-- A one-site matrix from a non-cyclic-active selected sector vanishes in the
original injective tensor expressed in the selected physical coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1617.

**Scope restriction (selected-sector visibility):** Length-two periodic coefficients
delete sectors outside cyclic support, and injectivity of the original tensor
separates the remaining trace pairing. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem changePhysicalBasis_apply_eq_zero_of_not_isCyclicActiveSector
    (F : PhysicalSectorFactorization C) (hK : K.IsInjective) (c : ℂ)
    (hmpo : mpo (changePhysicalBasis F.physicalCoordinateMatrix K) 2 =
      c • mpo F.sectorCoordinateTensor 2)
    (k : Fin F.sectorCount) (hk : ¬ F.IsCyclicActiveSector k)
    (x y : F.SectorIndex k) :
    changePhysicalBasis F.physicalCoordinateMatrix K
        (F.sectorFinEquiv.symm ⟨k, x⟩)
        (F.sectorFinEquiv.symm ⟨k, y⟩) = 0 := by
  let M := changePhysicalBasis F.physicalCoordinateMatrix K
  have hM : M.IsInjective :=
    F.changePhysicalBasis_physicalCoordinateMatrix_isInjective hK
  change M (F.sectorFinEquiv.symm ⟨k, x⟩)
    (F.sectorFinEquiv.symm ⟨k, y⟩) = 0
  apply (LinearMap.ker_eq_bot'.1
    (MPSTensor.traceMulRightPi_ker_eq_bot hM))
  funext p
  rw [MPSTensor.traceMulRightPi_apply, Pi.zero_apply]
  set u := p.divNat
  set v := p.modNat
  change Matrix.trace
    (M (F.sectorFinEquiv.symm ⟨k, x⟩)
      (F.sectorFinEquiv.symm ⟨k, y⟩) * M u v) = 0
  have h2 := congrFun (congrFun hmpo
    (Fin.cons (F.sectorFinEquiv.symm ⟨k, x⟩)
      (fun _ : Fin 1 ↦ u)))
    (Fin.cons (F.sectorFinEquiv.symm ⟨k, y⟩)
      (fun _ : Fin 1 ↦ v))
  have hCtrace :=
    F.trace_sectorCoordinateTensor_mul_eq_zero_of_not_isCyclicActiveSector
      hk x y u v
  simp only [mpo_apply, mpoMatrixEntry, List.ofFn_succ, Fin.isValue,
    Fin.cons_zero, Fin.cons_succ, List.ofFn_zero, evalWord_cons, evalWord_nil,
    mul_one, Matrix.smul_apply, smul_eq_mul] at h2
  rw [hCtrace, mul_zero] at h2
  simpa [M] using h2

/-- A missing selected edge forces the corresponding ordered product of
original-tensor sector matrices to vanish.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1617.

**Scope restriction (selected-sector visibility):** The length-three periodic identity
transfers only an edge which is already zero in the selected factorization.
It does not infer the vanishing of nonrecurrent edges from closed operators.
See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem changePhysicalBasis_mul_eq_zero_of_neighboringOperator_eq_zero
    (F : PhysicalSectorFactorization C) (hK : K.IsInjective) (c : ℂ)
    (hmpo : mpo (changePhysicalBasis F.physicalCoordinateMatrix K) 3 =
      c • mpo F.sectorCoordinateTensor 3)
    (k h : Fin F.sectorCount) (hkh : F.neighboringOperator k h = 0)
    (x y : F.SectorIndex k) (a b : F.SectorIndex h) :
    changePhysicalBasis F.physicalCoordinateMatrix K
        (F.sectorFinEquiv.symm ⟨k, x⟩)
        (F.sectorFinEquiv.symm ⟨k, y⟩) *
      changePhysicalBasis F.physicalCoordinateMatrix K
        (F.sectorFinEquiv.symm ⟨h, a⟩)
        (F.sectorFinEquiv.symm ⟨h, b⟩) = 0 := by
  let M := changePhysicalBasis F.physicalCoordinateMatrix K
  have hM : M.IsInjective :=
    F.changePhysicalBasis_physicalCoordinateMatrix_isInjective hK
  apply (LinearMap.ker_eq_bot'.1
    (MPSTensor.traceMulRightPi_ker_eq_bot hM))
  funext p
  rw [MPSTensor.traceMulRightPi_apply, Pi.zero_apply]
  set u := p.divNat
  set v := p.modNat
  change Matrix.trace
    ((M (F.sectorFinEquiv.symm ⟨k, x⟩)
      (F.sectorFinEquiv.symm ⟨k, y⟩) *
        M (F.sectorFinEquiv.symm ⟨h, a⟩)
          (F.sectorFinEquiv.symm ⟨h, b⟩)) * M u v) = 0
  have h3 := congrFun (congrFun hmpo
    (Fin.cons (F.sectorFinEquiv.symm ⟨k, x⟩) <|
      Fin.cons (F.sectorFinEquiv.symm ⟨h, a⟩)
        (fun _ : Fin 1 ↦ u)))
    (Fin.cons (F.sectorFinEquiv.symm ⟨k, y⟩) <|
      Fin.cons (F.sectorFinEquiv.symm ⟨h, b⟩)
        (fun _ : Fin 1 ↦ v))
  have hCprod :=
    F.oneSiteSectorMatrix_mul_eq_zero_of_neighboringOperator_eq_zero
      k h hkh x y a b
  simp only [mpo_apply, mpoMatrixEntry, List.ofFn_succ, Fin.isValue,
    Fin.cons_zero, Fin.cons_succ, List.ofFn_zero, evalWord_cons, evalWord_nil,
    mul_one, Matrix.smul_apply, smul_eq_mul] at h3
  simp only [oneSiteSectorMatrix] at hCprod
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc] at h3
  rw [hCprod, Matrix.zero_mul, Matrix.trace_zero, mul_zero] at h3
  simpa [M, Matrix.mul_assoc] using h3

/-- Every cyclic-active selected sector contains a nonzero one-site matrix of
the original injective tensor in the selected physical coordinates.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1617.

**Scope restriction (selected-sector visibility):** A nonzero diagonal cyclic
coefficient of length at least two is transferred through the closed-operator
proportionality. Only nonvanishing of one original one-site factor is
concluded. See `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem exists_changePhysicalBasis_apply_ne_zero_of_isCyclicActiveSector
    (F : PhysicalSectorFactorization C)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hmpo : ∀ N : ℕ, 2 ≤ N → ∃ c : ℂ, c ≠ 0 ∧
      mpo (changePhysicalBasis F.physicalCoordinateMatrix K) N =
        c • mpo F.sectorCoordinateTensor N)
    (q : Fin F.sectorCount) (hq : F.IsCyclicActiveSector q) :
    ∃ x y : F.SectorIndex q,
      changePhysicalBasis F.physicalCoordinateMatrix K
        (F.sectorFinEquiv.symm ⟨q, x⟩)
        (F.sectorFinEquiv.symm ⟨q, y⟩) ≠ 0 := by
  classical
  obtain ⟨N, hNinst, hN, k, hk0, z, hz⟩ :=
    F.exists_cyclicNeighboringProduct_diag_ne_zero_of_isCyclicActiveSector
      hpos hq
  subst q
  letI : NeZero N := hNinst
  let s := (F.sectorCoordinateChainEquiv N).symm ⟨k, z⟩
  have hselected :
      mpo F.sectorCoordinateTensor N s s ≠ 0 := by
    have hblock := congrFun (congrFun
      (F.reindex_mpo_sectorCoordinateTensor_eq_blockDiagonal (N := N))
        ⟨k, z⟩) ⟨k, z⟩
    have hentry :
        mpo F.sectorCoordinateTensor N s s =
          F.cyclicNeighboringProduct k z z := by
      simpa [s, Matrix.reindex_apply] using hblock
    rw [hentry]
    exact hz
  obtain ⟨c, hc, hclosed⟩ := hmpo N hN
  have horiginal :
      mpo (changePhysicalBasis F.physicalCoordinateMatrix K) N s s ≠ 0 := by
    have hentry := congrFun (congrFun hclosed s) s
    rw [hentry, Matrix.smul_apply, smul_eq_mul]
    exact mul_ne_zero hc hselected
  refine ⟨z 0, z 0, ?_⟩
  intro hzero
  apply horiginal
  cases N with
  | zero => omega
  | succ n =>
      simp [mpo_apply, mpoMatrixEntry, MPOTensor.evalWord_ofFn,
        List.ofFn_succ, s, hzero]

/-- The entries of the original tensor belonging to cyclic-active selected
sectors. -/
abbrev CyclicActiveOriginalEntryIndex (F : PhysicalSectorFactorization C) :=
  Σ q : F.CyclicActiveSector, F.SectorIndex q × F.SectorIndex q

/-- The original one-site matrices in cyclic-active selected-sector
coordinates. -/
noncomputable def cyclicActiveOriginalOneSiteMatrixFamily
    (F : PhysicalSectorFactorization C) (K : MPOTensor d D)
    (u : F.CyclicActiveOriginalEntryIndex) :
    Matrix (Fin D) (Fin D) ℂ :=
  changePhysicalBasis F.physicalCoordinateMatrix K
    (F.sectorFinEquiv.symm ⟨u.1, u.2.1⟩)
    (F.sectorFinEquiv.symm ⟨u.1, u.2.2⟩)

/-- The cyclic-active selected-sector matrices of the original injective
tensor span its full virtual matrix algebra.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1617.

**Scope restriction (selected-sector visibility):** Length-two closed operators
remove cross-sector entries and sectors outside cyclic support. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActiveOriginalOneSiteMatrixFamily_span_eq_top
    (F : PhysicalSectorFactorization C) (hK : K.IsInjective) (c : ℂ)
    (hmpo : mpo (changePhysicalBasis F.physicalCoordinateMatrix K) 2 =
      c • mpo F.sectorCoordinateTensor 2) :
    Submodule.span ℂ
      (Set.range (F.cyclicActiveOriginalOneSiteMatrixFamily K)) = ⊤ := by
  let M := changePhysicalBasis F.physicalCoordinateMatrix K
  have hM : M.IsInjective :=
    F.changePhysicalBasis_physicalCoordinateMatrix_isInjective hK
  apply top_unique
  rw [← hM.span_eq_top]
  apply Submodule.span_le.2
  rintro A ⟨p, rfl⟩
  change M p.divNat p.modNat ∈ _
  generalize hi : F.sectorFinEquiv p.divNat = si
  generalize hj : F.sectorFinEquiv p.modNat = sj
  obtain ⟨k, x⟩ := si
  obtain ⟨h, y⟩ := sj
  have hi' : p.divNat = F.sectorFinEquiv.symm ⟨k, x⟩ := by
    apply F.sectorFinEquiv.injective
    rw [Equiv.apply_symm_apply, hi]
  have hj' : p.modNat = F.sectorFinEquiv.symm ⟨h, y⟩ := by
    apply F.sectorFinEquiv.injective
    rw [Equiv.apply_symm_apply, hj]
  rw [hi', hj']
  change changePhysicalBasis F.physicalCoordinateMatrix K
    (F.sectorFinEquiv.symm ⟨k, x⟩)
    (F.sectorFinEquiv.symm ⟨h, y⟩) ∈ _
  by_cases hkh : k = h
  · subst h
    by_cases hk : F.IsCyclicActiveSector k
    · apply Submodule.subset_span
      exact ⟨⟨⟨k, (F.cyclicActiveWeight_ne_zero_iff k).2 hk⟩, x, y⟩, rfl⟩
    · rw [F.changePhysicalBasis_apply_eq_zero_of_not_isCyclicActiveSector
        hK c hmpo k hk x y]
      exact Submodule.zero_mem _
  · rw [F.changePhysicalBasis_apply_ne_eq_zero_of_mpo_two_eq_smul
      hK c hmpo hkh x y]
    exact Submodule.zero_mem _

private theorem reflTransGen_of_matrix_family
    {Q : Type*} {ι : Q → Type*}
    (A : (q : Q) → ι q → Matrix (Fin D) (Fin D) ℂ)
    (R : Q → Q → Prop)
    (hspan : Submodule.span ℂ
      (Set.range fun u : Σ q, ι q ↦ A u.1 u.2) = ⊤)
    (hnonzero : ∀ q, ∃ i, A q i ≠ 0)
    (hprod : ∀ q h, ¬ R q h → ∀ i j, A q i * A h j = 0)
    (q h : Q) :
    Relation.ReflTransGen R q h := by
  classical
  by_contra hreach
  let S : Set Q := fun r ↦ Relation.ReflTransGen R q r
  let space : Set Q → Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    fun T ↦ Submodule.span ℂ
      {X | ∃ r, r ∈ T ∧ ∃ i, A r i = X}
  have hqS : q ∈ S := Relation.ReflTransGen.refl
  have hhS : h ∈ Sᶜ := hreach
  have hcut : ∀ a ∈ S, ∀ b ∈ Sᶜ, ¬ R a b := by
    intro a ha b hb hab
    exact hb (ha.tail hab)
  have hsup : space S ⊔ space Sᶜ = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.2
    rintro X ⟨u, rfl⟩
    by_cases hu : u.1 ∈ S
    · apply (le_sup_left : space S ≤ _) (Submodule.subset_span ?_)
      exact ⟨u.1, hu, u.2, rfl⟩
    · apply (le_sup_right : space Sᶜ ≤ _) (Submodule.subset_span ?_)
      exact ⟨u.1, hu, u.2, rfl⟩
  have hspace_ne_bot (T : Set Q) (r : Q) (hr : r ∈ T) :
      space T ≠ ⊥ := by
    obtain ⟨i, hi⟩ := hnonzero r
    intro hbot
    have hmem : A r i ∈ space T :=
      Submodule.subset_span ⟨r, hr, i, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hi hmem
  have hmul : ∀ X ∈ space S, ∀ Y ∈ space Sᶜ, X * Y = 0 := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem X hX =>
        obtain ⟨a, ha, i, rfl⟩ := hX
        intro Y hY
        induction hY using Submodule.span_induction with
        | mem Y hY =>
            obtain ⟨b, hb, j, rfl⟩ := hY
            exact hprod a b (hcut a ha b hb) i j
        | zero => simp
        | add Y Z _ _ hY hZ => rw [mul_add, hY, hZ, add_zero]
        | smul c Y _ hY => rw [Algebra.mul_smul_comm, hY, smul_zero]
    | zero =>
        intro Y _
        exact Matrix.zero_mul Y
    | add X Z _ _ hX hZ =>
        intro Y hY
        rw [add_mul, hX Y hY, hZ Y hY, add_zero]
    | smul c X _ hX =>
        intro Y hY
        rw [Algebra.smul_mul_assoc, hX Y hY, smul_zero]
  exact Matrix.submodule_sup_ne_top_of_mul_eq_zero
    (space S) (space Sᶜ)
    (hspace_ne_bot S q hqS) (hspace_ne_bot Sᶜ h hhS)
    hmul hsup

/-- The cyclic-active sector graph of a selected fixed-product tensor is
strongly connected when its closed operators are nontrivially proportional
to those of an injective tensor.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1619.

**Scope restriction (selected-sector visibility):** Length two identifies the
trace-visible one-site span, while length three transfers only literal zero
neighboring edges. The directed-cut contradiction is carried out in the
original injective tensor. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem cyclicActive_reflTransGen_neighboringOperator_ne_zero_of_closed_mpo
    (F : PhysicalSectorFactorization C) (hK : K.IsInjective)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (hclosed : ∀ N : ℕ, 2 ≤ N → ∃ c : ℂ, c ≠ 0 ∧
      mpo (changePhysicalBasis F.physicalCoordinateMatrix K) N =
        c • mpo F.sectorCoordinateTensor N)
    (q h : F.CyclicActiveSector) :
    Relation.ReflTransGen
      (fun a b : F.CyclicActiveSector ↦
        F.neighboringOperator a b ≠ 0) q h := by
  obtain ⟨c₂, -, h₂⟩ := hclosed 2 le_rfl
  obtain ⟨c₃, -, h₃⟩ := hclosed 3 (by omega)
  apply reflTransGen_of_matrix_family
    (fun (r : F.CyclicActiveSector)
        (xy : F.SectorIndex r × F.SectorIndex r) ↦
      changePhysicalBasis F.physicalCoordinateMatrix K
        (F.sectorFinEquiv.symm ⟨r, xy.1⟩)
        (F.sectorFinEquiv.symm ⟨r, xy.2⟩))
    (fun a b : F.CyclicActiveSector ↦
      F.neighboringOperator a b ≠ 0)
  · exact F.cyclicActiveOriginalOneSiteMatrixFamily_span_eq_top hK c₂ h₂
  · intro r
    obtain ⟨x, y, hxy⟩ :=
      F.exists_changePhysicalBasis_apply_ne_zero_of_isCyclicActiveSector
        hpos hclosed r ((F.cyclicActiveWeight_ne_zero_iff r).1 r.property)
    exact ⟨(x, y), hxy⟩
  · intro a b hab x y
    apply F.changePhysicalBasis_mul_eq_zero_of_neighboringOperator_eq_zero
      hK c₃ h₃ a b
    exact not_ne_iff.mp hab

end MPOTensor.PhysicalSectorFactorization

namespace MPOTensor.EtaLocalStructureData

variable {d D : ℕ} {K : MPOTensor d D}

/-- The cyclic-active selected fixed-product sectors form one recurrent
component under the source hypotheses of Proposition `4to2`.

Source: arXiv:1606.00608, Appendix C.2, Proposition `4to2`, lines
1597--1619.

**Scope restriction (selected-sector visibility):** The proof uses the original
injective tensor in the selected physical coordinates, and does not assert
injectivity or normality of the selected fixed-product tensor. See
`docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`. -/
theorem selectedFixedProduct_cyclicActive_reflTransGen_neighboringOperator_ne_zero
    (_hMPDO : IsMPDO K) (hK : K.IsInjective)
    (_hNormal : MPSTensor.IsNormalTensor K.toMPSTensor)
    (data : EtaLocalStructureData K) (_hZCL : K.IsSourceZCL)
    (q h :
      data.bondData.fixedProductTensorDataPhysicalSectorFactorization
        |>.CyclicActiveSector) :
    Relation.ReflTransGen
      (fun a b :
          data.bondData.fixedProductTensorDataPhysicalSectorFactorization
            |>.CyclicActiveSector ↦
        (data.bondData.fixedProductTensorDataPhysicalSectorFactorization
          |>.neighboringOperator a b) ≠ 0) q h := by
  let F :=
    data.bondData.fixedProductTensorDataPhysicalSectorFactorization
  apply F.cyclicActive_reflTransGen_neighboringOperator_ne_zero_of_closed_mpo
    hK data.bondData.fixedProductTensorDataPhysicalSectorFactorization_neighboring_pos
  intro N hN
  obtain ⟨c, hc, hclosed⟩ :=
    data.exists_positive_scalar_mpo_changePhysicalBasis_eq_smul_selected N hN
  exact ⟨(c : ℂ), Complex.ofReal_ne_zero.mpr (ne_of_gt hc), hclosed⟩

end MPOTensor.EtaLocalStructureData
